#!/usr/bin/env python
"""GDB pretty printers."""

from __future__ import print_function
import contextlib
import functools
import glob
import itertools
import re
import sys
import types
import gdb
import gdb.printing
import gdb.types

print('Python ' + sys.version)
if sys.version_info.major < 3:
    print('Python 3 is required.')
    raise RuntimeError('Python 3 is required.')  # exit() would terminate gdb

# clear pretty printer list
gdb.pretty_printers[:] = []

# max nesting depth (of pp() and of the automatic dereferencing)
maxdepth: int = 10

# max children
maxchildren: int = 50

# automatic dereferencing of pointers and references
deref: bool = True

# read the target before dereferencing (fetch_lazy): unreadable memory shows
# the plain pointer instead of <Fehler: ...>; False is faster for big objects
deref_probe: bool = True

# max string length
maxstrlen: int = 80

# print adresses on each dereference (@0x...: value)
printaddr: bool = False

print('Options:')
print(f'py maxdepth = {maxdepth}')
print(f'py maxchildren = {maxchildren}')
print(f'py deref = {deref}')
print(f'py deref_probe = {deref_probe}')
print(f'py maxstrlen = {maxstrlen}')
print(f'py printaddr = {printaddr}')

# Some ANSI escape sequences

normal = '\x1b[0m'
bold = '\x1b[1m'
faint = '\x1b[2m'
underline = '\x1b[4m'
reverse = '\x1b[7m'
key_up = '\x1b[A'
key_down = '\x1b[B'
key_right = '\x1b[C'
key_left = '\x1b[D'


# Helper functions


trace_depth = 0


def trace(fn, cls_name=''):
    """Decorator to trace function calls."""
    # Comment out to enable.
    return fn

    def wrapper(*args, **kwargs):
        global trace_depth
        indent = ' ' * trace_depth
        name = fn.__name__
        trace_depth += 1
        result = None
        try:
            print(f'{indent}entering {cls_name}.{name}(')
            result = fn(*args, **kwargs)
        except Exception as e:
            print(f'{indent}exception in {cls_name}.{name}')
            raise e
        else:
            print(f'{indent}leaving {cls_name}.{name}')
        trace_depth -= 1
        return result
    return wrapper


def trace_class(cls):
    """Decorator to trace method calls for a class."""
    for name in cls.__dict__:
        if callable(cls.__dict__[name]):
            setattr(cls, name, trace(cls.__dict__[name], cls.__name__))
    return cls


@trace
def tuple_element(val: gdb.Value, n: int) -> gdb.Value:
    """Return the nth value from a std::tuple by walking its base classes (like the libstdc++ printer)."""
    # tuple<T0, T1, ...> : _Tuple_impl<0, T0, T1, ...>
    # _Tuple_impl<i, Ti, ...> : _Tuple_impl<i + 1, ...>, _Head_base<i, Ti>
    # (the last _Tuple_impl has the _Head_base only)
    fields = val.type.strip_typedefs().fields()
    if not fields or not fields[0].is_base_class:
        raise gdb.error(f'unknown tuple layout: {val.type}')
    impl = val.cast(fields[0].type)
    for _ in range(n):
        fields = impl.type.strip_typedefs().fields()
        if len(fields) != 2 or not fields[0].is_base_class:
            raise IndexError(f'tuple index {n} out of range')
        impl = impl.cast(fields[0].type)
    fields = impl.type.strip_typedefs().fields()
    if not fields or not fields[-1].is_base_class:
        raise gdb.error(f'unknown tuple layout: {impl.type}')
    return head_value(impl.cast(fields[-1].type))


def head_value(head: gdb.Value) -> gdb.Value:
    """Return the value stored in a std::_Head_base."""
    fields = head.type.strip_typedefs().fields()
    if fields and fields[0].name == '_M_head_impl':
        return head['_M_head_impl']
    if fields and fields[0].is_base_class:  # empty base optimization
        return head.cast(fields[0].type)
    raise gdb.error(f'unknown tuple layout: {head.type}')


head_base_re = re.compile(r'_Head_base<\s*(\d+)')  # gcc: _Head_base<0, ...>, clang: _Head_base<0UL, ...>


def find_head_base(val: gdb.Value, n: int, depth: int = 0):
    """Return the base class _Head_base<n, ...> of a tuple, searched recursively (None if none)."""
    if depth >= maxdepth:
        return None
    for f in val.type.strip_typedefs().fields():
        if not f.is_base_class:
            continue
        base = val.cast(f.type)
        match = head_base_re.search(f.name or str(f.type))
        if match and int(match.group(1)) == n:
            return base
        found = find_head_base(base, n, depth + 1)
        if found is not None:
            return found
    return None


@trace
def dereference_tuple(val: gdb.Value, n: int) -> gdb.Value:
    """Return the nth value fron a tuple."""
    # The base classes first: no symbol lookup, no compiler specific names
    # (clang names it _Head_base<0UL, ...>).
    try:
        return tuple_element(val, n)
    except Exception:  # unknown layout: search _Head_base<n, ...> among all base classes
        pass
    with contextlib.suppress(Exception):
        head = find_head_base(val, n)
        if head is not None:
            return head_value(head)
    # last resort: look _Head_base up by name
    elem_typename = str(val.type.template_argument(n))
    try:
        pointer_typename = f'std::_Head_base<{n}, {elem_typename}, false>'
        pointer_type = gdb.lookup_type(pointer_typename)
    except gdb.error:  # C++20
        pointer_typename = f'std::_Head_base<{n}ul, {elem_typename}, false>'
        pointer_type = gdb.lookup_type(pointer_typename)
    return val.cast(pointer_type)['_M_head_impl']


@trace
def compressed_pair_first(val: gdb.Value) -> gdb.Value:
    """Return the first value of a libc++ __compressed_pair."""
    typ = val.type.strip_typedefs()
    if typ.code != gdb.TYPE_CODE_STRUCT:  # libc++ >= 19: plain member (_LIBCPP_COMPRESSED_PAIR)
        return val
    # __compressed_pair<T1, T2> : __compressed_pair_elem<T1, 0>, __compressed_pair_elem<T2, 1>
    return val.cast(typ.fields()[0].type)['__value_']


@trace
def dereference_unique_ptr(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a std::unique_ptr (libstdc++ or libc++)."""
    if has_field(val, '__ptr_'):  # libc++
        return compressed_pair_first(val['__ptr_'])
    # Alt: return val['_M_t']['_M_t']['_M_head_impl']
    impl = val['_M_t']
    if has_field(impl, '_M_t'):  # __uniq_ptr_impl / __uniq_ptr_data (GCC >= 7), else std::tuple
        impl = impl['_M_t']
    return dereference_tuple(impl, 0)


@trace
def dereference_shared_ptr(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a std::shared_ptr (libstdc++ or libc++)."""
    if has_field(val, '__ptr_'):  # libc++
        return val['__ptr_']
    return val['_M_ptr']


@trace
def dereference_weak_ptr(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a std::weak_ptr (None: expired)."""
    if has_field(val, '__cntrl_'):  # libc++: __shared_owners_ is the use count - 1
        cntrl = val['__cntrl_']
        if int(cntrl) == 0 or scalar_value(cntrl['__shared_owners_']) < 0:
            return None
        return val['__ptr_']
    pi = val['_M_refcount']['_M_pi']
    if int(pi) == 0 or scalar_value(pi['_M_use_count']) <= 0:
        return None
    return val['_M_ptr']


@trace
def dereference_qweak_pointer(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a QWeakPointer (None: object deleted)."""
    d = val['d']
    if int(d) != 0 and scalar_value(d['strongref']) <= 0:
        return None
    return val['value']


@trace
def dereference_qpointer(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a QPointer (None: object deleted)."""
    if has_field(val, 'wp'):  # Qt5/Qt6: QWeakPointer<QObject>
        ptr = dereference_qweak_pointer(val['wp'])
    else:  # Qt4
        ptr = val['o']
    if ptr is None:
        return None
    return ptr.cast(val.type.strip_typedefs().template_argument(0).pointer())


@trace
def dereference_boost_weak_ptr(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a boost::weak_ptr (None: expired)."""
    pi = val['pn']['pi_']
    if int(pi) == 0 or scalar_value(pi['use_count_']) <= 0:
        return None
    return val['px']


# smart pointer template -> function returning its raw pointer (None: expired)
smart_pointers = {
    'std::shared_ptr': dereference_shared_ptr,
    'std::unique_ptr': dereference_unique_ptr,
    'std::weak_ptr': dereference_weak_ptr,
    'QSharedPointer': lambda val: val['value'],
    'QWeakPointer': dereference_qweak_pointer,
    'QPointer': dereference_qpointer,
    'QScopedPointer': lambda val: val['d'],
    'boost::shared_ptr': lambda val: val['px'],
    'boost::weak_ptr': dereference_boost_weak_ptr,
    'boost::scoped_ptr': lambda val: val['px'],
    'boost::intrusive_ptr': lambda val: val['px'],
}


@trace
def std_array_at(array: gdb.Value, n: int) -> gdb.Value:
    """Return the nth element of a std::array."""
    elem_type = array.type.template_argument(0)
    elem_size = array.type.template_argument(1)
    elems = array['_M_elems'].dereference().cast(elem_type.array(int(elem_size)))
    return elems[n]


@trace
def std_vector_at(vector: gdb.Value, n: int) -> gdb.Value:
    """Return the nth element of a std::vector."""
    elem_type = vector.type.template_argument(0)
    start = vector['_M_impl']['_M_start']
    finish = vector['_M_impl']['_M_finish']
    size = int(finish - start)
    if n < 0 or n >= size:
        raise IndexError(f'index {n} out of range (size {size})')
    elems = start.dereference().cast(elem_type.array(size))
    return elems[n]


@trace
@functools.lru_cache(maxsize=None)  # functools.cache needs Python 3.9
def enum_value(enum: str) -> int:
    """Return the integer value of an enumeration."""
    return int(gdb.parse_and_eval(enum))


@trace
def getaddr(val: gdb.Value) -> int:
    """Return ther address if a value."""
    if val.type.strip_typedefs().code == gdb.TYPE_CODE_PTR:
        return int(val)
    if val.address:
        return int(val.address)
    return 0


@trace
def type_has_field(typ: gdb.Type, name: str) -> bool:
    """Return whether a type (or one of its base classes) has a field."""
    while typ.code in (gdb.TYPE_CODE_PTR, gdb.TYPE_CODE_REF, gdb.TYPE_CODE_RVALUE_REF):
        typ = typ.target()
    typ = typ.unqualified().strip_typedefs()
    try:
        fields = typ.fields()
    except (gdb.error, TypeError):  # TypeError: not a struct type
        return False
    for field in fields:
        if field.name == name:
            return True
    return any(field.is_base_class and field.type is not None
               and type_has_field(field.type, name) for field in fields)


def has_field(val: gdb.Value, name: str) -> bool:
    """Return whether a value (or one of its base classes) has a field."""
    return type_has_field(val.type, name)


def basic_typename(typ: gdb.Type) -> str:
    """Return the name of a type without cv-qualifiers, typedefs and references ('' if none)."""
    typ = gdb.types.get_basic_type(typ)
    return typ.tag or typ.name or ''


template_name_re = re.compile(r'^([\w:]+)<')
inline_namespace_re = re.compile(r'^std::__\w+::')  # libc++ std::__1::, versioned std::__8::


def template_name(typ: gdb.Type) -> str:
    """Return the template name of a type, e.g. 'std::unique_ptr' ('' if none).

    Without cv-qualifiers, typedefs, references and inline namespaces."""
    match = template_name_re.match(basic_typename(typ))
    return inline_namespace_re.sub('std::', match.group(1)) if match else ''


def scalar_value(val: gdb.Value) -> int:
    """Return the integer value of a wrapper like QAtomicInt or std::atomic<int>."""
    for _ in range(maxdepth):
        typ = val.type.strip_typedefs()
        if typ.code not in (gdb.TYPE_CODE_STRUCT, gdb.TYPE_CODE_UNION):
            return int(val)
        field = next((f for f in typ.fields() if hasattr(f, 'bitpos')), None)  # first non static field
        if field is None:
            break
        val = val.cast(field.type) if field.is_base_class else val[field]
    raise gdb.error(f'no integer in {val.type}')


def error_text(e: Exception) -> str:
    """Return a short error text to be shown instead of a value."""
    return f'<Fehler: {e}>'


# current nesting depth of pp()
pp_depth = 0


@trace
def pp(val: gdb.Value) -> str:
    """Return the pretty printed value as string. Never raises."""
    global pp_depth
    if pp_depth >= maxdepth:
        return '...'
    pp_depth += 1
    try:
        if not isinstance(val, gdb.Value):  # e.g. a child given as Python string
            return str(val)
        v = gdb.default_visualizer(val)
        if v is None:
            return str(val)
        s = v.to_string()
        if isinstance(s, gdb.LazyString):
            return str(s.value())
        if s is None:  # printer shows children only
            return '{...}'
        return str(s)
    except Exception as e:
        return error_text(e)
    finally:
        pp_depth -= 1


def printer_children(val: gdb.Value):
    """Return the children of the pretty printer for a value (at most maxchildren)."""
    printer = gdb.default_visualizer(val)
    if printer is None or not hasattr(printer, 'children'):
        return iter(())
    return itertools.islice(printer.children(), maxchildren)


def struct_children(val: gdb.Value):
    """Return an iterator to the base classes and fields of a struct value."""
    try:
        if val.type.strip_typedefs().code in (gdb.TYPE_CODE_REF, gdb.TYPE_CODE_RVALUE_REF):
            val = val.referenced_value()
        fields = val.type.strip_typedefs().fields()
    except Exception:
        return
    anon = 0
    for f in fields:
        if not hasattr(f, 'bitpos'):  # static member
            continue
        try:
            if f.is_base_class:
                yield f.name, val.cast(f.type)
            else:
                name = f.name
                if not name:  # child names must be unique (gdb/MI)
                    anon += 1
                    name = '<anon>' if anon == 1 else f'<anon{anon}>'
                yield name, val[f]
        except Exception:
            continue


def raw_children(self):
    return struct_children(self.val)

def with_children(cls):
    if not hasattr(cls, 'children'):
        cls.children = raw_children
    return cls


# Exception safety: as soon as one printer raises, cpptools drops all
# remaining children of a variable. So no printer may raise.

def safe_to_string(fn):
    """Wrap to_string(): show an error text instead of raising."""
    @functools.wraps(fn)
    def wrapper(self):
        try:
            return fn(self)
        except Exception as e:
            return error_text(e)
    wrapper.safe = True
    return wrapper


def safe_children(fn):
    """Wrap children(): stop at the first error instead of raising.

    The error is shown as an additional child '<Fehler>'; a map gets a
    complete key/value pair instead. Child names must be unique strings
    (gdb/MI: 'Duplicate variable object name'), so duplicates get a suffix."""
    @functools.wraps(fn)
    def wrapper(self):
        n = 0
        names = set()
        try:
            for name, value in fn(self):
                name = str(name)
                if name in names:
                    name = f'{name}#{n}'
                names.add(name)
                yield name, value
                n += 1
        except Exception as e:
            text = error_text(e)
            try:
                is_map = self.display_hint() == 'map'
            except Exception:
                is_map = False
            if not is_map:
                yield '<Fehler>', text
            elif n % 2 == 0:  # key and value
                yield '<Fehler>', '<Fehler>'
                yield '<Text>', text
            else:  # value of the last key
                yield '<Text>', text
    wrapper.safe = True
    return wrapper


def safe_display_hint(fn):
    """Wrap display_hint() (or num_children()): None instead of raising."""
    @functools.wraps(fn)
    def wrapper(self):
        try:
            return fn(self)
        except Exception:
            return None
    wrapper.safe = True
    return wrapper


def safe_printer(cls):
    """Make to_string(), children(), display_hint() and num_children() of a
    printer class exception safe.

    Inherited methods, too (foreign printers like libstdc++'s). Idempotent."""
    for name, wrap in (('to_string', safe_to_string),
                       ('children', safe_children),
                       ('display_hint', safe_display_hint),
                       ('num_children', safe_display_hint)):  # gdb >= 14 (DAP): None = count children
        raw = next((c.__dict__[name] for c in cls.__mro__ if name in c.__dict__), None)
        if isinstance(raw, (staticmethod, classmethod)):  # would get self as argument
            continue
        fn = getattr(cls, name, None)
        if callable(fn) and not getattr(fn, 'safe', False):
            setattr(cls, name, wrap(fn))
    return cls


class SafeRegexpCollectionPrettyPrinter(gdb.printing.RegexpCollectionPrettyPrinter):
    """RegexpCollectionPrettyPrinter whose lookup never raises (e.g. in a printer's __init__).

    On error there is no printer (None) and gdb shows the value natively."""

    def __call__(self, val):
        try:
            return super().__call__(val)
        except Exception:
            return None
    __call__.safe = True


def safe_lookup(fn):
    """Wrap a lookup function (or __call__ of a printer collection): no printer
    (None) instead of raising. The class of a found printer is made safe, too."""
    @functools.wraps(fn)
    def wrapper(*args):
        try:
            printer = fn(*args)
        except Exception:
            return None
        if printer is not None:
            with contextlib.suppress(Exception):
                safe_printer(type(printer))
        return printer
    wrapper.safe = True
    return wrapper


def harden_printers(printers: list):
    """Make the foreign printers of a printer list (e.g. libstdc++) exception safe. Idempotent."""
    for i, printer in enumerate(printers):
        try:
            if getattr(printer, 'safe', False):  # own or already hardened
                continue
            if isinstance(printer, (types.FunctionType, types.MethodType)):  # lookup function
                printers[i] = safe_lookup(printer)
                continue
            cls = type(printer)  # printer collection: __call__ is the lookup
            if not getattr(cls.__call__, 'safe', False):
                cls.__call__ = safe_lookup(cls.__call__)
            subprinters = []
            for name in ('subprinters', '_subprinters', 'lookup', '_lookup'):
                subs = getattr(printer, name, None)
                if isinstance(subs, dict):
                    subprinters.extend(subs.values())
                elif isinstance(subs, (list, tuple)):
                    subprinters.extend(subs)
            for sp in subprinters:
                # gen_printer: gdb.printing.RegexpCollectionPrettyPrinter, (_)function: libstdc++
                for name in ('gen_printer', 'function', '_function'):
                    gen = getattr(sp, name, None)
                    if isinstance(gen, type):
                        safe_printer(gen)
            printer.safe = True
        except Exception:
            continue


# STL pretty printers


path = glob.glob('/usr/share/*/python/libstdcxx/v6/printers.py')
if len(path) == 0:
    path = glob.glob('/usr/share/*/*/python/libstdcxx/v6/printers.py')
if len(path) == 0:
    path = glob.glob('/usr/share/*/*/*/python/libstdcxx/v6/printers.py')
if len(path) > 0:
    sys.path.insert(0, path[0][:-25])
    try:  # made exception safe by harden_all_printers() at the end
        from libstdcxx.v6.printers import register_libstdcxx_printers
        register_libstdcxx_printers(None)
    except Exception as e:  # keep the other printers
        print(f'libstdc++ pretty printers not loaded: {e}')
else:
    print('libstdc++ pretty printers not found')


# Qt and boost smart pointers (the std ones are shown by libstdc++)


@trace_class
class SmartPointerPrinter:
    """Pretty printer for Qt and boost smart pointers (when deref shows no target)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val
        self.name = template_name(val.type)
        self.ptr = smart_pointers[self.name](val)  # None: object deleted / expired

    def counts(self) -> str:
        """Return the reference counts as text ('' if none)."""
        if self.name in ('QSharedPointer', 'QWeakPointer'):
            d = self.val['d']
            if int(d) != 0:
                return f" (strong {scalar_value(d['strongref'])}, weak {scalar_value(d['weakref'])})"
        elif self.name in ('boost::shared_ptr', 'boost::weak_ptr'):
            pi = self.val['pn']['pi_']
            if int(pi) != 0:
                return f" (use count {scalar_value(pi['use_count_'])}, weak count {scalar_value(pi['weak_count_'])})"
        return ''

    def to_string(self) -> str:
        """Convert value to string."""
        if self.ptr is None:
            target = '<expired>'
        elif int(self.ptr) == 0:
            target = '<null>'
        else:
            target = f'{int(self.ptr):#x}'
        return f'{self.name} {target}{self.counts()}'

    def children(self):
        """Return the raw pointer."""
        if self.ptr is not None and int(self.ptr) != 0:
            yield 'data', self.ptr


# Boost pretty printers


@trace_class
class BoostOptionalPrinter:
    """Pretty Printer for boost::optional."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def to_string(self) -> str:
        """Convert value to string."""
        if has_field(self.val, 'storage'):  # boost >= 1.87
            storage = self.val['storage']
            if storage['init_']:
                return str(storage['storage_']['value_'])
            return '<empty>'
        if self.val['m_initialized']:
            stored_type = self.val.type.template_argument(0)
            try:
                data = self.val['m_storage']['dummy_']['data']
                return str(data.address.cast(stored_type.pointer()).dereference())
            except Exception:
                return str(self.val['m_storage'].address.cast(stored_type.pointer()).dereference())
        else:
            return '<empty>'


@trace_class
class BoostUnorderedMapPrinter:
    """Pretty Printer for boost::unordered_map."""

    def __init__(self, val):
        """Initialize."""
        self.val = val

    def to_string(self):
        """Convert value to string."""
        return f"map of size {int(self.val['table_']['size_'])}"

    def values(self):
        """Return an interator to the stored values (pairs for a map)."""
        table = self.val['table_']
        buckets_arr = table['buckets_']
        # at most maxchildren values; visited guards against cyclic node chains
        count = min(int(table['size_']), maxchildren)
        visited = set()

        if has_field(buckets_arr, 'buckets'):  # boost >= 1.87 (fca)
            # bucket array with one node chain per bucket; the bucket at
            # index size_ is an always-empty sentinel
            buckets = buckets_arr['buckets']
            n = 0
            for i in range(int(buckets_arr['size_'])):
                if n >= count:
                    return
                node_ptr = (buckets + i).dereference()['next']
                while int(node_ptr) != 0 and int(node_ptr) not in visited and n < count:
                    visited.add(int(node_ptr))
                    node = node_ptr.dereference()
                    yield node['buf']['t_']
                    n += 1
                    node_ptr = node['next']
            return

        # boost < 1.87
        # find types
        allocators_type = table['allocators_'].type
        node_allocator_type = allocators_type.template_argument(1)
        node_type = node_allocator_type.template_argument(0)
        value_type = node_type.template_argument(0)

        # find first node
        buckets = table['buckets_']
        first_node = buckets[int(table['bucket_count_'])]
        node_ptr = first_node['next_']

        n = 0
        while int(node_ptr) != 0 and int(node_ptr) not in visited and n < count:
            visited.add(int(node_ptr))
            node = node_ptr.dereference()
            node_ptr = node['next_']
            buf = node.cast(node_type)['value_base_']['data_']['data_']['buf']
            yield buf.dereference().cast(value_type)
            n += 1

    def children(self):
        """Return an interator to map content."""
        for n, pair in enumerate(self.values()):
            yield str(2 * n), pair['first']
            yield str(2 * n + 1), pair['second']

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'map'


@trace_class
class BoostUnorderedSetPrinter(BoostUnorderedMapPrinter):
    """Pretty Printer for boost::unordered_set."""

    def to_string(self):
        """Convert value to string."""
        return f"set of size {int(self.val['table_']['size_'])}"

    def children(self):
        """Return an interator to set content."""
        for n, value in enumerate(self.values()):
            yield str(n), value

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'array'


@trace
def build_boost_pretty_printer() -> gdb.printing.RegexpCollectionPrettyPrinter:
    """Build boost pretty printer collection."""
    pp = SafeRegexpCollectionPrettyPrinter('Boost')
    pp.add_printer('Optional', '^boost::optional<.*$', BoostOptionalPrinter)
    pp.add_printer('UnorderedMap', '^boost::unordered::unordered_map<.*$', BoostUnorderedMapPrinter)
    pp.add_printer('UnorderedSet', '^boost::unordered::unordered_set<.*$', BoostUnorderedSetPrinter)
    pp.add_printer('SmartPointer', '^boost::(shared_ptr|weak_ptr|scoped_ptr|intrusive_ptr)<.*$', SmartPointerPrinter)
    for sp in pp.subprinters:
        safe_printer(sp.gen_printer)
    return pp


@trace
def register_boost_printers(obj):
    """Register boost pretty printers."""
    gdb.printing.register_pretty_printer(obj, build_boost_pretty_printer())


register_boost_printers(None)


# Qt pretty printers


@trace_class
class QStringPrinter:
    """Pretty printer for QString."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def to_string(self) -> str:
        """Convert value to string."""
        d = self.val['d']
        data_len = int(d['size'])
        truncated = False
        global maxstrlen
        if data_len > maxstrlen:
            data_len = maxstrlen
            truncated = True
        if has_field(d, 'ptr'):  # Qt6: DataPointer {d, ptr, size}
            data_offset = 0
            data = d['ptr'].cast(gdb.lookup_type('unsigned short int').pointer())
        elif has_field(d, 'offset'):  # Qt5: QArrayData with byte offset
            data_offset = int(d['offset']/2)
            data = d.cast(gdb.lookup_type('unsigned short int').pointer())
        else:  # Qt4: inline data pointer
            data_offset = 0
            data = d['data']
        result = b''
        for offset in range(data_len):
            ch = int((data + data_offset + offset).dereference())
            result += ch.to_bytes(2, sys.byteorder)
        encoding = 'utf-16-le' if sys.byteorder == 'little' else 'utf-16-be'
        if truncated:
            result += '[...]'.encode(encoding)
        return result.decode(encoding, errors='replace')

    def display_hint(self) -> str:
        """Return display hint (string/array/map)."""
        return 'string'


def format_jd(jd: int) -> str:
    """Convert QDates 'jd' value to a date string."""
    # maths from http://www.tondering.dk/claus/cal/julperiod.php
    a = jd + 32044
    b = (4 * a + 3) // 146097
    c = a - ((146097 * b) // 4)
    d = (4 * c + 3) // 1461
    e = c - ((1461 * d) // 4)
    m = (5 * e + 2) // 153
    day = e - ((153 * m + 2) // 5) + 1
    month = m + 3 - 12 * (m // 10)
    year = 100 * b + d - 4800 + (m // 10)
    return f'{day:0=2}.{month:0=2}.{year:0=4}'


@trace_class
class QDatePrinter:
    """Pretty printer for QDate."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def jd_is_valid(self, jd: int) -> bool:
        """Check wether QDates 'jd' value represents a valid date."""
        return jd >= -784350574879 and jd <= 784354017364 and jd > 0

    def to_string(self) -> str:
        """Convert value to string."""
        jd = int(self.val['jd'])
        if not self.jd_is_valid(jd):
            return '<invalid date>'
        return format_jd(int(jd))


def format_ds(ds: int):
    """Convert QTimes 'ds' value to a time string."""
    if ds >= 0:
        seconds = 0
        minutes = 0
        hours = 0
        if ds >= 3600000:
            hours = int(ds / 3600000)
            ds = ds - hours * 3600000
        if ds >= 60000:
            minutes = int(ds / 60000)
            ds = ds - minutes * 60000
        if ds >= 1000:
            seconds = int(ds / 1000)
            ds = ds - seconds * 1000
        return f'{hours:0=2}:{minutes:0=2}:{seconds:0=2}.{ds:0=3}'
    else:
        return '<invalid time>'


@trace_class
class QTimePrinter:
    """Pretty printer for QTime."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def to_string(self) -> str:
        """Convert value to string."""
        mds = int(self.val['mds'])
        return format_ds(mds)


def format_msecs(msecs: int) -> str:
    """Convert milliseconds since 1970-01-01T00:00 UTC to a date/time string."""
    msecs_per_day = 24*60*60*1000
    jd = 2440588
    ds = 0
    if msecs >= msecs_per_day or msecs <= -msecs_per_day:
        jd += msecs // msecs_per_day
        msecs %= msecs_per_day
    if msecs < 0:
        ds = msecs_per_day - msecs - 1
        jd -= ds // msecs_per_day
        ds = ds % msecs_per_day
        ds = msecs_per_day - ds - 1
    else:
        ds = msecs
    return f'{format_jd(jd)}/{format_ds(ds)}'


@trace_class
class QDateTimePrinter:
    """Pretty printer for QDateTime."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def to_string(self) -> str:
        """Convert value to string."""
        d = self.val['d']
        if has_field(d, 'data') and has_field(d, 'd'):
            # Qt >= 5.14 and Qt6: union Data { QDateTimePrivate *d; ShortData data; }
            status = int(d['data']['status'])
            if status & 1:  # ShortData
                if status & 0xe != 0xe:  # ValidityMask
                    return '<invalid datetime>'
                msecs = int(d['data']['msecs'])
            else:
                # QDateTimePrivate is an incomplete type in debug info
                # (private header). shortcut: msecs is its first field
                # after the QSharedData base, at offset sizeof(void*).
                addr = d['d'].cast(gdb.lookup_type('char').pointer()) \
                    + gdb.lookup_type('void').pointer().sizeof
                msecs = int(addr.cast(gdb.lookup_type('long long').pointer()).dereference())
            return format_msecs(msecs)
        priv = d['d']  # older Qt: shared pointer to QDateTimePrivate
        if has_field(priv, 'data'):  # Qt5 < 5.14
            return format_msecs(int(priv['data']['msecs']))
        return f"{pp(priv['date'])}/{pp(priv['time'])}"  # Qt4


@trace_class
class QListIterator:
    """Iterator for QList."""

    def __init__(self, val: gdb.Value, typ: gdb.Type):
        """Initialize."""
        d = val['d']
        self.element_type = typ.template_argument(0)
        self.i = 0
        if has_field(d, 'ptr'):  # Qt6: contiguous array {d, ptr, size}
            self.qt6 = True
            self.data = d['ptr']
            self.count = int(d['size'])
        else:  # Qt5: array of void* slots
            self.qt6 = False
            self.d = d
            self.ptr_size = gdb.lookup_type('void').pointer().sizeof
            self.count = int(d['end'])
            self.i = int(d['begin'])
        self.begin = self.i  # child names count from 0
        self.count = min(self.count, self.i + maxchildren)

    def __next__(self):
        """Return next value from list."""
        if self.i >= self.count:
            raise StopIteration
        i = self.i
        self.i += 1
        if self.qt6:
            return (str(i - self.begin), (self.data + i).dereference())
        node = self.d['array'][i]
        if self.element_type.sizeof > self.ptr_size:
            # shortcut: movability not detectable in gdb; assumes every large
            # element is pointer-stored (true unless Q_DECLARE_TYPEINFO Movable)
            elem = node.cast(self.element_type.pointer()).dereference()
        else:
            elem = node.address.cast(self.element_type.pointer()).dereference()
        return (str(i - self.begin), elem)


@trace_class
class QListPrinter:
    """Pretty printer for QList."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def __iter__(self):
        """Return an interator to list content."""
        return QListIterator(self.val, self.val.type.strip_typedefs())

    def to_string(self) -> str:
        """Convert value to string."""
        d = self.val['d']
        if has_field(d, 'ptr'):  # Qt6
            n = int(d['size'])
        else:  # Qt5
            n = int(d['end']) - int(d['begin'])
        return f"QList with {n} elements"

    def children(self):
        """Return an interator to list content."""
        return self

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'array'


# QMetaType::Type (Qt5) -> type name, for the types QVariantPrinter shows
qvariant_types = {
    1: 'bool', 2: 'int', 3: 'unsigned int', 4: 'long long', 5: 'unsigned long long', 6: 'double',
    7: 'QChar', 8: 'QVariantMap', 9: 'QVariantList', 10: 'QString', 11: 'QStringList',
    12: 'QByteArray', 14: 'QDate', 15: 'QTime', 16: 'QDateTime', 28: 'QVariantHash',
    32: 'long', 33: 'short', 34: 'char', 35: 'unsigned long', 36: 'unsigned short',
    37: 'unsigned char', 38: 'float', 40: 'signed char',
}

# typedef -> the type itself, if only that is in the debug info
qvariant_typedefs = {
    'QVariantMap': ('QMap<QString, QVariant>',),
    'QVariantList': ('QList<QVariant>',),
    'QVariantHash': ('QHash<QString, QVariant>',),
}


@trace_class
class QVariantPrinter:
    """Pretty printer for QVariant (Qt5: types from qvariant_types)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def value(self):
        """Return type name and stored value (None: type not shown)."""
        d = self.val['d']
        typ = int(d['type'])
        name = qvariant_types.get(typ)
        if name is None:
            return f'type {typ}', None
        stored_type = None
        for typename in (name,) + qvariant_typedefs.get(name, ()):
            with contextlib.suppress(Exception):  # not in the debug info
                stored_type = gdb.lookup_type(typename)
                break
        if stored_type is None:
            return name, None
        if d['is_shared']:  # too big for the data union: separate allocation
            addr = d['data']['shared']['ptr']
        else:
            addr = d['data'].address
        return name, addr.cast(stored_type.pointer()).dereference()

    def to_string(self) -> str:
        """Convert value to string."""
        d = self.val['d']
        if not has_field(d, 'type'):
            return '<QVariant>'  # Qt6 stores packedType/QMetaType, not implemented
        typ = int(d['type'])

        if typ == 0:
            return '<invalid QVariant>'
        name, value = self.value()
        if value is None:
            return f'<QVariant {name}>'
        return f'({name}) {pp(value)}'

    def children(self):
        """Return the stored value."""
        d = self.val['d']
        if has_field(d, 'type') and int(d['type']) != 0:
            _, value = self.value()
            if value is not None:
                yield 'value', value


def qt5_array_data(d: gdb.Value, elem_type: gdb.Type) -> gdb.Value:
    """Return a pointer to the elements of a Qt5 QArrayData (QByteArray, QVector)."""
    offset = int(d['offset'])  # byte offset from d to the elements
    return (d.cast(gdb.lookup_type('char').pointer()) + offset).cast(elem_type.pointer())


def align(offset: int, typ: gdb.Type) -> int:
    """Round a byte offset up to the alignment of a type."""
    alignment = getattr(typ, 'alignof', 0) or min(typ.sizeof, gdb.lookup_type('void').pointer().sizeof) or 1
    return (offset + alignment - 1) // alignment * alignment


def value_at(ptr: gdb.Value, offset: int, typ: gdb.Type) -> gdb.Value:
    """Return the value of a type at a byte offset from a pointer."""
    return (ptr.cast(gdb.lookup_type('char').pointer()) + offset).cast(typ.pointer()).dereference()


@trace_class
class QByteArrayPrinter:
    """Pretty printer for QByteArray."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def to_string(self) -> str:
        """Convert value to string."""
        d = self.val['d']
        size = int(d['size'])
        if has_field(d, 'ptr'):  # Qt6: DataPointer {d, ptr, size}
            data = d['ptr']
        elif has_field(d, 'offset'):  # Qt5: QArrayData with byte offset
            data = qt5_array_data(d, gdb.lookup_type('char'))
        else:  # Qt4: inline data pointer
            data = d['data']
        result = bytes(int((data + i).dereference()) & 0xff for i in range(min(size, maxstrlen)))
        text = result.decode('utf-8', errors='replace')
        if size > maxstrlen:
            text += '[...]'
        return text

    def display_hint(self) -> str:
        """Return display hint (string/array/map)."""
        return 'string'


@trace_class
class QStringListPrinter(QListPrinter):
    """Pretty printer for QStringList (Qt5: derived from QList<QString>, Qt6: a typedef)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        base = next(f for f in gdb.types.get_basic_type(val.type).fields() if f.is_base_class)
        super().__init__(val.cast(base.type))


@trace_class
class QVectorPrinter:
    """Pretty printer for QVector (Qt5; in Qt6 QVector is QList)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val
        if not has_field(self.val['d'], 'offset'):
            raise gdb.error('QVector: Qt5 only')  # no printer: shown natively

    def to_string(self) -> str:
        """Convert value to string."""
        return f"QVector with {int(self.val['d']['size'])} elements"

    def children(self):
        """Return an interator to vector content."""
        elem_type = self.val.type.strip_typedefs().template_argument(0)
        d = self.val['d']
        data = qt5_array_data(d, elem_type)
        for i in range(min(int(d['size']), maxchildren)):
            yield str(i), (data + i).dereference()

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'array'


@trace_class
class QPairPrinter:
    """Pretty printer for QPair (Qt5; in Qt6 QPair is std::pair)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def to_string(self) -> str:
        """Convert value to string."""
        return f"({pp(self.val['first'])}, {pp(self.val['second'])})"

    def children(self):
        """Return first and second."""
        yield 'first', self.val['first']
        yield 'second', self.val['second']


@trace_class
class QMapPrinter:
    """Pretty printer for QMap (Qt5)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val
        if not has_field(self.val['d'], 'header'):
            raise gdb.error('QMap: Qt5 only')  # no printer: shown natively

    def to_string(self) -> str:
        """Convert value to string."""
        return f"QMap with {int(self.val['d']['size'])} elements"

    def children(self):
        """Return an interator to map content."""
        typ = self.val.type.strip_typedefs()
        key_type = typ.template_argument(0)
        value_type = typ.template_argument(1)
        # QMapNode<Key, T> : QMapNodeBase {quintptr p; left; right;} {Key key; T value;}
        key_offset = align(3 * gdb.lookup_type('void').pointer().sizeof, key_type)
        value_offset = align(key_offset + key_type.sizeof, value_type)
        d = self.val['d']
        count = min(int(d['size']), maxchildren)
        # in-order walk of the red-black tree; visited guards against cycles
        stack = []
        visited = set()
        node = d['header']['left']  # root
        n = 0
        while n < count:
            while int(node) != 0:
                if int(node) in visited or len(visited) > count + 128:
                    raise gdb.error('QMap: invalid tree')
                visited.add(int(node))
                stack.append(node)
                node = node['left']
            if not stack:
                return
            node = stack.pop()
            yield str(2 * n), value_at(node, key_offset, key_type)
            yield str(2 * n + 1), value_at(node, value_offset, value_type)
            n += 1
            node = node['right']

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'map'


def qt5_hash_nodes(d: gdb.Value, count: int):
    """Return an iterator to the first count nodes of a Qt5 QHashData."""
    end = int(d)  # the QHashData itself ends each bucket chain
    buckets = d['buckets']
    visited = set()
    n = 0
    for i in range(int(d['numBuckets'])):
        if n >= count:
            return
        node = (buckets + i).dereference()
        while int(node) not in (0, end) and n < count:
            if int(node) in visited:
                raise gdb.error('QHash: cyclic bucket chain')
            visited.add(int(node))
            yield node
            n += 1
            node = node['next']


def qt5_hash_key_offset(key_type: gdb.Type) -> int:
    """Return the byte offset of the key in a Qt5 QHashNode."""
    # QHashNode<Key, T> {QHashNode *next; const uint h; const Key key; T value;}
    return align(gdb.lookup_type('void').pointer().sizeof + gdb.lookup_type('unsigned int').sizeof, key_type)


@trace_class
class QHashPrinter:
    """Pretty printer for QHash (Qt5)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val
        if not has_field(self.val['d'], 'buckets'):  # Qt6: spans
            raise gdb.error('QHash: Qt5 only')  # no printer: shown natively

    def to_string(self) -> str:
        """Convert value to string."""
        return f"QHash with {int(self.val['d']['size'])} elements"

    def children(self):
        """Return an interator to hash content."""
        typ = self.val.type.strip_typedefs()
        key_type = typ.template_argument(0)
        value_type = typ.template_argument(1)
        key_offset = qt5_hash_key_offset(key_type)
        value_offset = align(key_offset + key_type.sizeof, value_type)
        d = self.val['d']
        for n, node in enumerate(qt5_hash_nodes(d, min(int(d['size']), maxchildren))):
            yield str(2 * n), value_at(node, key_offset, key_type)
            yield str(2 * n + 1), value_at(node, value_offset, value_type)

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'map'


@trace_class
class QSetPrinter:
    """Pretty printer for QSet (Qt5: QHash<T, QHashDummyValue>)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val
        if not has_field(self.val['q_hash']['d'], 'buckets'):  # Qt6: spans
            raise gdb.error('QSet: Qt5 only')  # no printer: shown natively

    def to_string(self) -> str:
        """Convert value to string."""
        return f"QSet with {int(self.val['q_hash']['d']['size'])} elements"

    def children(self):
        """Return an interator to set content."""
        key_type = self.val.type.strip_typedefs().template_argument(0)
        key_offset = qt5_hash_key_offset(key_type)
        d = self.val['q_hash']['d']
        for n, node in enumerate(qt5_hash_nodes(d, min(int(d['size']), maxchildren))):
            yield str(n), value_at(node, key_offset, key_type)

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'array'


@trace
def build_qt_pretty_printer() -> gdb.printing.RegexpCollectionPrettyPrinter:
    """Build Qt pretty printer collection."""
    pp = SafeRegexpCollectionPrettyPrinter('Qt')
    pp.add_printer('QDate', '^QDate$', QDatePrinter)
    pp.add_printer('QTime', '^QTime$', QTimePrinter)
    pp.add_printer('QDateTime', '^QDateTime$', QDateTimePrinter)
    pp.add_printer('QString', '^QString$', QStringPrinter)
    pp.add_printer('QVariant', '^QVariant$', QVariantPrinter)
    pp.add_printer('QList', '^QList<.*>$', QListPrinter)
    pp.add_printer('QByteArray', '^QByteArray$', QByteArrayPrinter)
    pp.add_printer('QStringList', '^QStringList$', QStringListPrinter)
    pp.add_printer('QVector', '^QVector<.*>$', QVectorPrinter)
    pp.add_printer('QPair', '^QPair<.*>$', QPairPrinter)
    pp.add_printer('QMap', '^QMap<.*>$', QMapPrinter)
    pp.add_printer('QHash', '^QHash<.*>$', QHashPrinter)
    pp.add_printer('QSet', '^QSet<.*>$', QSetPrinter)
    pp.add_printer('SmartPointer', '^(Q(Shared|Weak|Scoped)Pointer|QPointer)<.*>$', SmartPointerPrinter)
    for sp in pp.subprinters:
        safe_printer(sp.gen_printer)
    return pp


@trace
def register_qt_printers(obj):
    """Register Qt pretty printers."""
    gdb.printing.register_pretty_printer(obj, build_qt_pretty_printer())


register_qt_printers(None)


# Auto dereference pointers, references and typdefs.

@safe_printer
class DynamicPtrPrinter:
    def __init__(self, val):
        self.val = val
    def to_string(self):
        return f'({self.val.dynamic_type}) {int(self.val):#x}'

    def children(self):
        try:
            obj = self.val.cast(self.val.dynamic_type).dereference()
        except Exception:
            return iter(())
        return struct_children(obj)


@safe_printer
class AddrPrinter:
    """Printer of a dereferenced value with its address in front (printaddr)."""

    def __init__(self, printer, ptr: gdb.Value):
        self.printer = printer
        self.ptr = ptr
        if hasattr(printer, 'children'):
            self.children = printer.children

    def to_string(self):
        s = self.printer.to_string() if hasattr(self.printer, 'to_string') else None
        if isinstance(s, gdb.LazyString):
            s = s.value()
        addr = f'@{int(self.ptr):#x}'
        return addr if s is None else f'{addr}: {s}'

    def display_hint(self):
        hint = self.printer.display_hint() if hasattr(self.printer, 'display_hint') else None
        return None if hint == 'string' else hint  # 'string' would quote the address, too


def addr_printer(printer, ptr: gdb.Value):
    """Return printer; with printaddr its to_string() shows the address ptr in front."""
    if printaddr and printer is not None and ptr is not None:
        return AddrPrinter(printer, ptr)
    return printer


def deref_target(target: gdb.Value, ptr: gdb.Value):
    """Return the printer for the target of a dereference of ptr (None: no printer)."""
    if deref_probe:
        target.fetch_lazy()  # unreadable memory raises: show the pointer natively
    return addr_printer(gdb.default_visualizer(target), ptr)


# current nesting depth of deref_printers()
deref_depth = 0


@trace
def deref_printers(val: gdb.Value):
    """Auto dereference pointers, references and typdefs."""
    global deref_depth
    if not deref or deref_depth >= maxdepth:
        return None
    # Must never raise (see safe_printer). Without a printer of our own
    # (None) gdb shows the value natively. As the first printer it sees
    # every value: everything else returns None quickly.
    deref_depth += 1
    try:
        typ = val.type
        if typ.code == gdb.TYPE_CODE_TYPEDEF:
            # typedef'd structs: the other printers strip typedefs themselves
            typ = typ.strip_typedefs()
            if typ.code not in (gdb.TYPE_CODE_PTR, gdb.TYPE_CODE_REF, gdb.TYPE_CODE_RVALUE_REF,
                                gdb.TYPE_CODE_STRUCT):
                return None
            val = val.cast(typ)
        if typ.code == gdb.TYPE_CODE_PTR:
            if int(val) == 0:
                return None
            target_type = typ.target().unqualified().strip_typedefs()
            # cast to derived type (dynamic_type drops cv-qualifiers)
            dyn = val.dynamic_type
            if dyn.target().unqualified().strip_typedefs() != target_type:
                derived = val.cast(dyn).dereference()
                if deref_probe:
                    derived.fetch_lazy()  # unreadable memory: show the pointer natively
                printer = gdb.default_visualizer(derived)
                return addr_printer(printer, val) if printer is not None else DynamicPtrPrinter(val)
            # dereference pointers (except void* and function pointers)
            if target_type.code not in (gdb.TYPE_CODE_VOID, gdb.TYPE_CODE_FUNC):
                return deref_target(val.referenced_value(), val)
            return None
        if typ.code == gdb.TYPE_CODE_REF or typ.code == gdb.TYPE_CODE_RVALUE_REF:
            target = val.referenced_value()
            dyn = target.dynamic_type
            if dyn.strip_typedefs().unqualified() != target.type.strip_typedefs().unqualified():
                target = target.cast(dyn)
            return deref_target(target, target.address)
        if typ.code != gdb.TYPE_CODE_STRUCT:
            return None
        # smart pointers (std, Qt, boost; also const, typedef'd, libc++)
        tag = typ.tag or ''
        if '_ptr<' not in tag and 'Pointer<' not in tag:  # quick exit for all other structs
            return None
        get_pointer = smart_pointers.get(template_name(typ))
        if get_pointer is None:
            return None
        ptr = get_pointer(val)
        if ptr is None or int(ptr) == 0:  # expired or null
            return None
        return deref_target(ptr.dereference(), ptr)
    except Exception:
        return None
    finally:
        deref_depth -= 1


deref_printers.safe = True  # harden_printers() leaves it alone


def ensure_deref_first():
    """Keep deref_printers the very first global printer (also after later registrations)."""
    printers = gdb.pretty_printers
    if deref_printers in printers and printers[0] is not deref_printers:
        printers.remove(deref_printers)
        printers.insert(0, deref_printers)


# RailSys pretty printers

# RSBase

@trace_class
class UUIDPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        if self.val['m_bValid']:
            data1 = int(self.val['m_uiData1'])
            data2 = int(self.val['m_uiData2'])
            data3 = int(self.val['m_uiData3'])
            data4 = int(self.val['m_uiData4'])
            return f'{data1:0=8x}-{data2:0=4x}-{data3:0=4x}-{data4:0=4x}'
        else:
            return '<invalid UUID>'


@trace_class
class KeyOrPtrPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        key = pp(self.val['m_Key'])
        ptr = pp(self.val['m_pPtr'])
        return f'{key}: {ptr}'

    def children(self):
        yield "Key", self.val['m_Key']
        yield "Ptr", self.val['m_pPtr']


@trace_class
class BigIntPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        if self.val['m_bIsNull']:
            return 'Null'
        else:
            return str(int(self.val['m_Value']))


@trace_class
class ReferencingIdentifierPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        etype = pp(self.val['m_eType'])
        id_ = str(int(self.val['m_iId']))
        return f'[ {etype}, {id_} ]'


@trace_class
class LongFlagsPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        enum_type = self.val.type.template_argument(0)
        length = int(str(self.val.type.template_argument(1)))
        words = self.val['m_bits']['_M_w']  # std::bitset: one word, or an array for > 64 bits
        words_type = words.type.strip_typedefs()
        if words_type.code == gdb.TYPE_CODE_ARRAY:
            low, high = words_type.range()
            word_bits = words_type.target().sizeof * 8
            value = 0
            for k in range(low, high + 1):
                value |= (int(words[k]) & ((1 << word_bits) - 1)) << ((k - low) * word_bits)
        else:
            value = int(words)
        result = ''
        for i in range(0, length):
            if (1 << i) & value != 0:
                result += f'{pp(gdb.Value(i.to_bytes(enum_type.sizeof, byteorder=sys.byteorder, signed=False), enum_type))}|'
        if len(result) > 0:
            result = result[:-1]
        return result


@trace_class
class BoolArrayPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        enum_type = self.val.type.template_argument(0)
        bit_count = int(str(self.val.type.template_argument(1)))
        base = int(str(self.val.type.template_argument(2)))
        values = self.val['m_iBits']
        result = ''
        for i in range(0, bit_count):
            index = int((i - base) / 32)
            shift = (i - base) % 32
            mask = 1 << (32 - 1 - shift)
            if values[index] & mask != 0:
                result += f'{pp(gdb.Value(i.to_bytes(enum_type.sizeof, byteorder=sys.byteorder, signed=False), enum_type))}|'
        if len(result) > 0:
            result = result[:-1]
        return result


@trace_class
class SetVectorPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val
        self.printer = None  # no vector member or no printer for it: show raw fields
        try:
            self.printer = gdb.default_visualizer(self.val['m_vecData'])
        except Exception:
            try:
                self.printer = gdb.default_visualizer(self.val['m_impl']['m_data'])
            except Exception:
                pass

    def __iter__(self):
        return self.printer.__iter__()

    def to_string(self) -> str:
        if self.printer is None:
            return None
        return self.printer.to_string()

    def children(self):
        if self.printer is None:
            return raw_children(self)
        return itertools.islice(self.printer.children(), maxchildren)

    def display_hint(self):
        if self.printer is None:
            return None
        return self.printer.display_hint()


@trace_class
class PointPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        x = float(self.val['m_dXPos'])
        y = float(self.val['m_dYPos'])
        return f'{x}, {y}'


@trace_class
class MultiLanguageStringPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return pp(self.val['m_sFallback'])


@trace_class
class UnitPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        typename = basic_typename(self.val.type)  # without typedefs, const, &
        if 'Acceleration' in typename:
            return str(self.val['m_Value']) + ' m/s^2'
        elif 'Duration' in typename or 'Time' in typename:
            seconds = int(self.val['m_Value'])
            minutes = 0
            hours = 0
            days = 0
            result = ''
            if seconds >= 86400:
                days = int(seconds / 86400)
                seconds = seconds - days * 86400
            if seconds >= 3600:
                hours = int(seconds / 3600)
                seconds = seconds - hours * 3600
            if seconds >= 60:
                minutes = int(seconds / 60)
                seconds = seconds - minutes * 60
            if 'Duration' in typename:
                if days > 0:
                    result += str(days) + 'd '
                if hours > 0:
                    result += str(hours) + 'h '
                if minutes > 0:
                    result += str(minutes) + 'm '
                if seconds > 0 or result == '':
                    result += str(seconds) + 's '
            elif 'Time' in typename:
                if days > 0:
                    result += str(days) + 'd '
                result += f'{hours:02}:{minutes:02}:{seconds:02}'
            return result
        elif 'Length' in typename:
            return str(self.val['m_Value']) + ' m'
        elif 'Mass' in typename:
            return str(self.val['m_Value']) + ' kg'
        elif 'Speed' in typename:
            return str(self.val['m_Value'] * 3.6) + ' km/h'
        elif 'Force' in typename:
            return str(self.val['m_Value']) + ' N'
        elif 'Energy' in typename:
            return str(self.val['m_Value']) + ' W'
        return str(self.val['m_Value'])


@trace_class
class DiscreteUnitPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:  # 'str | gdb.LazyString' needs Python 3.10
        amount = float(self.val['m_amount'])
        factor = float(str(self.val.type.template_argument(2)))
        return str(amount / factor)


@trace_class
class ZeitPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        seconds = int(self.val['m_iSeconds'])
        if seconds == -2147483648:
            return '<invalid>'
        minutes = 0
        hours = 0
        days = 0
        result = ''
        if (seconds < 0):
            result += '-'
            seconds = -seconds
        if seconds >= 86400:
            days = int(seconds / 86400)
            seconds = seconds - days * 86400
        if seconds >= 3600:
            hours = int(seconds / 3600)
            seconds = seconds - hours * 3600
        if seconds >= 60:
            minutes = int(seconds / 60)
            seconds = seconds - minutes * 60
        if days > 0:
            result += str(days) + 'd'
        result += f'{hours:02}:{minutes:02}:{seconds:02}'
        return result


@trace_class
class DezimalZeitPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        seconds = int(self.val['m_iNumber'] / self.val['s_iFaktor'])
        minutes = 0
        hours = 0
        days = 0
        result = ''
        if seconds < 0:
            result += '-'
            seconds = -seconds
        if seconds >= 86400:
            days = int(seconds / 86400)
            seconds = seconds - days * 86400
        if seconds >= 3600:
            hours = int(seconds / 3600)
            seconds = seconds - hours * 3600
        if seconds >= 60:
            minutes = int(seconds / 60)
            seconds = seconds - minutes * 60
        if days > 0:
            result += str(days) + 'd '
        result += f'{hours:02}:{minutes:02}:{seconds:02}'
        return result


@trace_class
class DateTimePrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return pp(self.val['m_utc'])


@trace_class
class DateRangePrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        if self.val['m_bIsForever']:
            return '<forever>'
        else:
            return f"{pp(self.val['m_dateStart'])} - {pp(self.val['m_dateEnd'])}"


@trace_class
class ZeitlicheGueltigkeitPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return f"{pp(self.val['m_Ab'])} - {pp(self.val['m_Bis'])}"


@trace_class
class IntervallPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return f"{pp(self.val['m_From'])} - {pp(self.val['m_To'])}"


@trace_class
class OpDayNumberCodeGermanPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        wochentage = self.val['m_iWochentagCode']
        feiertage = self.val['m_iFeiertagCode']
        days = ''
        if wochentage & 0x40:
            days = days + 'Mo,'
        if wochentage & 0x20:
            days = days + 'Di,'
        if wochentage & 0x10:
            days = days + 'Mi,'
        if wochentage & 0x08:
            days = days + 'Do,'
        if wochentage & 0x04:
            days = days + 'Fr,'
        if wochentage & 0x02:
            days = days + 'Sa,'
        if wochentage & 0x01:
            days = days + 'So,'
        if feiertage & 0x0f:  # +/- only together with holidays, else the last ',' is cut
            if feiertage & 0x10:
                days = days + '+'
            else:
                days = days + '-'
        if feiertage & 0x08:
            days = days + 'vF,'
        if feiertage & 0x04:
            days = days + 'F,'
        if feiertage & 0x02:
            days = days + 'nF,'
        if feiertage & 0x01:
            days = days + 'nnF,'
        if len(days) > 0:
            days = days[0:-1]
        if len(days) == 0:
            days = '<leer>'
        return days


# RSInfra

@trace_class
class StreckePrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        gb = bool(self.val['m_bIsGlobalerBereich'])
        name = pp(self.val['m_sKuerzel'])
        return f'{name}{" (g)" if gb else ""}'


@trace_class
class OrdnungsRahmenStreckePrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return pp(self.val['m_stKey'])


@trace_class
class KnotenPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def print_id(self) -> str:
        try:
            strecke = pp(self.val['m_pStrecke'])
            kid = int(self.val['m_stId']['m_uiValueArray'][1])
            return f'{strecke}/{kid}'
        except Exception as e:
            return error_text(e)

    def print_name(self) -> str:
        if self.val['m_eKnotenTyp'] == 1:
            return 'Auflösekontakt'
        elif self.val['m_eKnotenTyp'] == 2:
            return 'Balise'
        elif self.val['m_eKnotenTyp'] == 3:
            return 'LinienleiterBeginn'
        elif self.val['m_eKnotenTyp'] == 4:
            return 'Sichtpunkt'
        elif self.val['m_eKnotenTyp'] == 5:
            return 'Vorsignal'
        elif self.val['m_eKnotenTyp'] == 6:
            return 'AspectTrigger'
        elif self.val['m_eKnotenTyp'] == 7:
            return 'EuroLoop'
        elif self.val['m_eKnotenTyp'] == 8:
            return 'OverlapTrigger'
        elif self.val['m_eKnotenTyp'] == 9:
            return 'SonstigesSignal'
        elif self.val['m_eKnotenTyp'] == 10:
            return 'Achszähler'
        else:
            try:
                try:
                    typ = self.val.dynamic_type  # most derived class
                except Exception:
                    typ = self.val.type
                type_name = basic_typename(typ)  # also for references, typedefs, const
                if not type_name:
                    return 'Unbekannt'
                colon_pos = type_name.rfind('::')
                if colon_pos != -1:
                    type_name = type_name[colon_pos + 2:]
                return type_name
            except Exception:
                return 'Unbekannt'

    def to_string(self) -> str:
        return f'{self.print_name()} {self.print_id()}'


@trace_class
class SignalPrinter(KnotenPrinter):
    def __init__(self, val: gdb.Value):
        self.val = val

    def print_name(self) -> str:
        return 'Signal'


@trace_class
class GleisPrinter(KnotenPrinter):
    def __init__(self, val: gdb.Value):
        self.val = val

    def print_name(self) -> str:
        return 'Gleis'

    def print_id(self) -> str:
        haltepunkt = pp(self.val['m_stId']['m_sHaltepunkt'])
        gleisnummer = pp(self.val['m_stId']['m_sGleisnummer'])
        return f'{haltepunkt}-{gleisnummer}'


@trace_class
class KantenPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        startknoten = pp(self.val['m_pStartKnoten'])
        zielknoten = pp(self.val['m_pZielKnoten'])
        try:
            laenge = int(self.val['m_iLaenge']) # Meter
        except gdb.error:
            laenge = pp(self.val['m_Laenge'])
        return f'({startknoten}..{zielknoten}, {laenge}m)'


@trace_class
class KantenListePrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        try:
            startknoten = pp(self.val['m_pStartKnoten'])
            zielknoten = pp(self.val['m_pZielKnoten'])
        except gdb.error:
            kantenzug = self.val['m_KantenZug']
            startknoten = pp(kantenzug['m_pStartKnoten'])
            zielknoten = pp(kantenzug['m_pZielKnoten'])
        try:
            laenge = int(self.val['m_iLaenge'])
        except gdb.error:
            laenge = pp(self.val['m_laenge'])
        return f'{startknoten}..{zielknoten},{laenge}m'

@trace_class
class BlockPrinter(KantenListePrinter):
    def __init__(self, val: gdb.Value):
        super().__init__(val)

    def to_string(self) -> str:
        kantenliste = super().to_string()
        #try:
        #    signalsysteme = pp(self.val['m_signalSysteme'])  # TODO
        #except gdb.error:
        #    signalsysteme = pp(self.val['m_eSignalSystem'])
        return kantenliste


@trace_class
class BstFahrwegPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return pp(self.val['m_sName'])


@trace_class
class BahnhofPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        try:  # RailSys >=12.25
            temporal_data = std_vector_at(self.val['m_temporalAttributes']['m_temporalData'], 0)
            name = pp(temporal_data['second']['m_sBeschreibung'])
            if name == '' or name == '""':  # WTF?
                return pp(self.val['m_sKuerzel'])
            return name
        except Exception:  # RailSys <12.25
            return pp(self.val['m_sKuerzel'])


# RSBetrieb

@trace_class
class TaktPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        if int(self.val['m_pParentTakt']) == 0:  # nullptr
            return '/'
        else:
            parenttakt = pp(self.val['m_pParentTakt'])
            name = pp(self.val['m_sName'])
            return f'{parenttakt}{name}/'


@trace_class
class LinkedListIterator:
    def __init__(self, val: gdb.Value):
        self.val = val
        self.current = self.val['m_pFront']
        self.i = 0
        self.visited = set()  # guards against cyclic lists

    def __next__(self):
        if int(self.current) == 0 or int(self.current) in self.visited or self.i >= maxchildren:
            raise StopIteration
        current = self.current
        self.visited.add(int(current))
        self.current = self.current.dereference()['m_pNext']
        self.i += 1
        return (str(self.i), current)


@trace_class
class LinkedListPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def __iter__(self):
        return LinkedListIterator(self.val)

    def to_string(self) -> str:
        return f'LinkedList with {int(self.val["m_uiAnzahl"])} elements'

    def children(self):
        return self

    def display_hint(self):
        return 'array'


@trace_class
class LaufwegKnotenPositionPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        anzahl = int(self.val['m_uiAnzahlKanten'])
        position = pp(self.val['m_positionInMetern'])
        return f'({anzahl}K {position})'


@trace_class
class LaufwegblockPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        index = str(self.val['m_iIndex'])
        block = pp(self.val['m_pBlock'])
        #signalsystem = pp(self.val['m_stData']['m_stBits']['m_eSignalSystem'])  # TODO
        return f'{index} {block}'


@trace_class
class FahrwegBlockPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        sbloecke = '[ '
        for child in printer_children(self.val['m_stBloecke']):
            sbloecke += pp(child[1]) + ', '
        if sbloecke[-2] == ',':
            sbloecke = sbloecke[:-2]
            sbloecke += ' ]'
        else:
            sbloecke += ']'
        try:
            laenge = int(self.val['m_iLaenge'])
        except gdb.error:
            laenge = pp(self.val['m_dLaenge'])
        return f'{sbloecke} {laenge}m'


@trace_class
class LaufwegFahrwegBlockPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return pp(self.val['m_rFahrwegBlock'])


@trace_class
class StationsZeitPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        ankunft = pp(self.val['m_zAnkunft'])
        abfahrt = pp(self.val['m_zAbfahrt'])
        return f'{ankunft} -> {abfahrt}'


@trace_class
class StationsZeitenPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return f'Stationszeiten'

    def children(self):
        zeiten = self.val['m_arZeiten']
        yield 'Planzeit', std_array_at(zeiten, 0)
        yield 'Realzeit', std_array_at(zeiten, 1)
        yield 'Wunschzeit', std_array_at(zeiten, 2)
        yield 'BfoZeit', std_array_at(zeiten, 3)
        yield 'EsfZeit', std_array_at(zeiten, 4)
        yield 'Mindestfahrzeit', std_array_at(zeiten, 5)
        yield 'MindestfahrzeitAnkunft', std_array_at(zeiten, 6)
        yield 'Ausrollenzeit', std_array_at(zeiten, 7)


@trace_class
class StationPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        bahnhof = pp(self.val['m_pBahnhof'])
        fahrplan = self.val['m_pFahrplan']
        if int(fahrplan) != 0:
            zug = pp(fahrplan['m_pZug'])
        else:
            zug = '<kein Zug>'
        pgleis = self.val['m_pSollfahrplanGleis']
        if int(pgleis) != 0:
            gleis = pp(pgleis)
        else:
            gleis = '<kein Gleis>'
        pbstfahrweg = self.val['m_pBstFahrweg']
        if int(pbstfahrweg) != 0:
            bstfahrweg = pp(pbstfahrweg)
        else:
            bstfahrweg = '<kein BstFahrweg>'

        stuetze = ' '
        try:
            stuetze = '+' if bool(self.val['m_bIsStuetzstation']) else ' '
        except gdb.error:
            pass
        return f'Station{stuetze} {bahnhof} ({zug}, {gleis}, {bstfahrweg})'


@trace_class
class BerechnungsStationPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        bahnhof = pp(self.val['m_rStation']['m_pBahnhof'])
        zug = pp(self.val['m_pFahrplan']['m_rZug'])
        gleis = pp(self.val['m_rStation']['m_pSollfahrplanGleis'])
        try:
            stuetze = '+' if bool(self.val['m_bFahrzeitStuetze']) else ' '
        except gdb.error:
            stuetze = '+' if int(self.val['m_eStuetzStationTyp']) != 0 else ' '
        return f'Station{stuetze} {bahnhof} {gleis} {zug}'


@trace_class
class BerechnungsFahrplanPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def __iter__(self):
        return LinkedListIterator(self.val['m_Stationen'])

    def to_string(self) -> str:
        anzahl = int(self.val['m_Stationen']['m_uiAnzahl'])
        return f'BerechnungsFahrplan mit {anzahl} Stationen'

    def children(self):
        return self

    def display_hint(self):
        return 'array'


@trace_class
class FahrplanPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def __iter__(self):
        return LinkedListIterator(self.val['m_seqStation'])

    def to_string(self) -> str:
        anzahl = int(self.val['m_seqStation']['m_uiAnzahl'])
        return f'Fahrplan mit {anzahl} Stationen'

    def children(self):
        return self

    def display_hint(self):
        return 'array'


@trace_class
class ZugPrinter:  # RailSys <= 11
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return f'Zug {pp(self.val["m_stNummer"]["m_sNummer"])}'


@trace_class
class PlanungsZugPrinter:  # RailSys >= 12
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        nummer = pp(self.val['m_stNummer']['m_sNummer'])
        variante = int(self.val['m_stNummer']['m_uiVariante'])
        return f'Zug {nummer}-{variante}'


@trace_class
class BerechnungsZugPrinter:  # RailSys >= 12.6
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        private = dereference_unique_ptr(self.val['m_pPrivate'])
        zuege = private['m_PlanungsZuege']
        typ = int(private['m_eTyp'])
        styp = '?'
        if typ == enum_value('RSBetrieb::EBerechnungsZugTyp::RegelzugVt'):
            styp = 'R'
        elif typ == enum_value('RSBetrieb::EBerechnungsZugTyp::RegelzugAngebotsVt'):
            styp = 'RA'
        elif typ == enum_value('RSBetrieb::EBerechnungsZugTyp::BerechnungsZug'):
            styp = 'B'
        elif typ == enum_value('RSBetrieb::EBerechnungsZugTyp::AngebotsZug'):
            styp = 'A'
        elif typ == enum_value('RSBetrieb::EBerechnungsZugTyp::TemporaererZug'):
            styp = 'T'
        zuegestr = ''
        for child in printer_children(zuege):
            zugstr = pp(child[1])
            zuegestr += zugstr + ','
        zuegestr = zuegestr[:-1]
        return f'{zuegestr}({styp})'


@trace_class
class KantenBelegungPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def print_zeiten(self) -> str:
        current: gdb.Value = self.val
        result: list[str] = []
        visited = {getaddr(current)}  # guards against cyclic m_pFolgeKante chains
        while True:
            if len(result) >= maxchildren:
                result.append('...')
                break
            try:
                typ = int(current['m_stData']['m_stBits']['m_eBelegungsTyp'])
                reservierungszeit = pp(current['m_zReservierungszeit'])
                belegzeit = pp(current['m_zBelegzeit'])
                endebildezeit = pp(current['m_zEndeBildezeit'])
                kantenankunft = pp(current['m_zKantenankunft'])
                aufloesezeit = pp(current['m_zAufloesezeit'])
                result.append(f'{"Block" if typ == 0 else "DWeg"} {reservierungszeit} {belegzeit} {endebildezeit} {kantenankunft} {aufloesezeit}')
                folgekante = int(current['m_pFolgeKante'])
            except Exception as e:
                result.append(error_text(e))
                break
            if folgekante == 0:
                result.append('nullptr')
                break
            if folgekante in visited:
                result.append('<Zyklus>')
                break
            visited.add(folgekante)
            try:
                current = current['m_pFolgeKante'].dereference()
            except Exception:
                result.append('<invalid m_pFolgeKante>')
                break
        return ', '.join(result)

    def to_string(self) -> str:
        return f"{self.print_zeiten()} ({pp(self.val['m_pKantenliste'])})"


# @trace_class
# class KantenBelegungenPrinter:
#     def __init__(self, val: gdb.Value):
#         self.val = val
#         obj = gdb.default_visualizer(self.val['m_map'])
#         self.kbs = []
#         for kanten, kb in obj.children():
#             self.kbs.append([kanten, kb])
#         self.kbs.sort(key=lambda kb: int(kb[1]['m_zBelegzeit']['m_iSeconds']))

#     def to_string(self) -> str:
#         return 'Kantenbelegungen'

#     def children(self):
#         for kanten, kb in self.kbs:
#             yield kanten, kb


@trace_class
class PositionInfoPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        position = pp(self.val['m_fPosition'])
        laufwegblock = pp(self.val['m_pLaufwegBlock'])
        startstation = pp(self.val['m_pStartStation'])
        zielstation = pp(self.val['m_pZielStation'])
        return f'{position}, {laufwegblock}, {startstation} -> {zielstation}'


@trace_class
class AktualParameterPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        v = pp(self.val['m_fV'])
        position = pp(self.val['m_PositionInfo'])
        return f'{v}, {position}'


@trace_class
class ZugfahrtPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        try:
            zug_ptr = dereference_shared_ptr(self.val['m_pZug'])
            zug = pp(zug_ptr) if int(zug_ptr) != 0 else '<kein Zug>'
        except Exception as e:
            zug = error_text(e)
        try:
            aktpar_ptr = dereference_unique_ptr(self.val['m_pAktPar'])
            aktpar = pp(aktpar_ptr) if int(aktpar_ptr) != 0 else '<keine AktPar>'
        except Exception as e:
            aktpar = error_text(e)
        return f'Zugfahrt {zug}, {aktpar}'


# Misc

@trace_class
class OpDayAbschnittPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        gueltigkeit = pp(self.val['m_stGueltigkeitsZeitraum'])
        zusatztage = '{ '
        if has_field(self.val['m_stZusatztage'], 'm_vecData'):
            for day in printer_children(self.val['m_stZusatztage']['m_vecData']):
                zusatztage = zusatztage + pp(day[1]) + ', '
        else:
            zusatztage += pp(self.val['m_stZusatztage']) + ' '
        zusatztage += '}'
        ausnahmetage = '{ '
        if has_field(self.val['m_stAusnahmetage'], 'm_vecData'):
            for day in printer_children(self.val['m_stAusnahmetage']['m_vecData']):
                ausnahmetage = ausnahmetage + pp(day[1]) + ', '
        else:
            ausnahmetage += pp(self.val['m_stAusnahmetage']) + ' '
        ausnahmetage += '}'
        days = pp(self.val['m_stNummernCode'])
        return f'[ {gueltigkeit} {days} Z: {zusatztage} A: {ausnahmetage} ]'


@trace_class
class OpDayPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        result = '[ Abschnitte: { '
        for abschnitt in printer_children(self.val['m_stVtAbschnitte']):
            result = result + pp(abschnitt[1]) + ', '
        return result + '} VT-Text: "' + pp(self.val['m_sVerkehrstageText']) + '" ]'


@trace_class
class VerkehrsTageBausteinPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        key = pp(self.val['m_Key'])
        opday = pp(self.val['m_OpDay'])
        return f'"{key}" {opday}'


@trace_class
class BausteinDataPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        return pp(self.val['m_sKuerzel'])


@trace_class
class TWennXPrinter:
    def __init__(self, val: gdb.Value):
        self.val = val

    def to_string(self) -> str:
        item = pp(self.val['m_item'])
        werktags = bool(self.val['m_bNurWerktags'])
        return item + (' w.X' if werktags else '')


@trace
def build_rs_pretty_printer() -> gdb.printing.RegexpCollectionPrettyPrinter:
    pp = SafeRegexpCollectionPrettyPrinter('RailSys')
    pp.add_printer('AktualParameter', '^RSBetrieb::Zugfahrt::AktualParameter$', AktualParameterPrinter)
    pp.add_printer('Anzeiger', '^RSInfra::Anzeiger$', KnotenPrinter)  # TODO
    pp.add_printer('Bahnhof', '^RSInfra::Bahnhof$', BahnhofPrinter)
    pp.add_printer('BausteinData', '^RSInfra::Tools::VTTextCompute::BausteinData$', BausteinDataPrinter)
    pp.add_printer('BerechnungsFahrplan', '^RSBetrieb::BerechnungsFahrplan$', BerechnungsFahrplanPrinter)
    pp.add_printer('BerechnungsStation', '^RSBetrieb::BerechnungsStation$', BerechnungsStationPrinter)
    pp.add_printer('BerechnungsZug', '^RSBetrieb::BerechnungsZug$', BerechnungsZugPrinter)
    pp.add_printer('BigInt', '^RSBase::SqlIo::BigInt<.*>$', BigIntPrinter)
    pp.add_printer('Block', '^RSInfra::Block$', BlockPrinter)
    pp.add_printer('BoolArray', '^RSBase::BoolArray<.*>$', BoolArrayPrinter)
    pp.add_printer('BstFahrweg', '^RSInfra::BstFahrweg$', BstFahrwegPrinter)
    pp.add_printer('BstGrenze', '^RSInfra::BstGrenze$', KnotenPrinter)  # TODO
    pp.add_printer('DWeg', '^RSInfra::DWeg$', KantenListePrinter)  # TODO
    pp.add_printer('DateRange', '^RSBase::DateRange$', DateRangePrinter)
    pp.add_printer('DezimalZeit', '^RSBase::DezimalZeit$', DezimalZeitPrinter)
    pp.add_printer('DiscreteUnit', '^RSBase::Units::DiscreteUnit<.*>$', DiscreteUnitPrinter)
    pp.add_printer('DynamischerBlock', '^RSInfra::DynamischerBlock$', KantenListePrinter)  # TODO
    pp.add_printer('Fahrplan', '^RSBetrieb::Fahrplan$', FahrplanPrinter)
    pp.add_printer('FahrwegBlock', '^RSInfra::FahrwegBlock$', FahrwegBlockPrinter)
    pp.add_printer('Gleis', '^RSInfra::Gleis$', GleisPrinter)
    pp.add_printer('Intervall', '^RSBase::Intervall<.*>$', IntervallPrinter)
    pp.add_printer('Kante', '^RSInfra::Kante$', KantenPrinter)
    pp.add_printer('KantenBelegung', '^RSBetrieb::KantenBelegung$', KantenBelegungPrinter)
    #pp.add_printer('KantenBelegungen', '^RSBetrieb::KantenBelegungen$', KantenBelegungenPrinter)
    pp.add_printer('KantenListe', '^RSInfra::KantenListe$', KantenListePrinter)
    pp.add_printer('KantenListeMitUuid', '^RSInfra::KantenListeMitUuid$', KantenListePrinter)  # TODO
    pp.add_printer('KeyOrPtr', '^RSBase::KeyOrPtr<.*>$', KeyOrPtrPrinter)
    pp.add_printer('KeyOrPtrBase', '^RSBase::KeyOrPtrBase<.*>$', KeyOrPtrPrinter)
    pp.add_printer('KeyOrRawPtr', '^RSBase::KeyOrRawPtr<.*>$', KeyOrPtrPrinter)
    pp.add_printer('Kilometrierungssprung', '^RSInfra::Kilometrierungssprung$', KnotenPrinter)  # TODO
    pp.add_printer('Knoten', '^RSInfra::Knoten$', KnotenPrinter)
    pp.add_printer('Kreuzung', '^RSInfra::Kreuzung$', KnotenPrinter)  # TODO
    pp.add_printer('LaufwegBlock', '^RSBetrieb::LaufwegBlock$', LaufwegblockPrinter)
    pp.add_printer('LaufwegFahrwegBlock', '^RSBetrieb::LaufwegFahrwegBlock$', LaufwegFahrwegBlockPrinter)
    pp.add_printer('LaufwegKnotenPosition', '^RSBetrieb::LaufwegKnotenPosition$', LaufwegKnotenPositionPrinter)
    pp.add_printer('LinkedList', '^RSBetrieb::LinkedList<.*>$', LinkedListPrinter)
    pp.add_printer('LongFlags', '^RSBase::LongFlags<.*>$', LongFlagsPrinter)
    pp.add_printer('MultiLanguageString', '^RSBase::MultiLanguageString$', MultiLanguageStringPrinter)
    pp.add_printer('OpDay', '^RSBase::Rail::(Base|Temp)?OpDay$', OpDayPrinter)
    pp.add_printer('OpDayAbschnitt', '^RSBase::Rail::OpDayAbschnitt$', OpDayAbschnittPrinter)
    pp.add_printer('OpDayNumberCodeGerman', '^RSBase::Rail::OpDayNumberCodeGerman$', OpDayNumberCodeGermanPrinter)
    pp.add_printer('OrdnungsRahmenStrecke', '^RSInfra::OrdnungsRahmenStrecke$', OrdnungsRahmenStreckePrinter)
    pp.add_printer('PlanungsZug', '^RSBetrieb::PlanungsZug$', PlanungsZugPrinter)
    pp.add_printer('Point', '^RSBase::Geometry::Point$', PointPrinter)
    pp.add_printer('PositionInfo', '^RSBetrieb::Zugfahrt::PositionInfo$', PositionInfoPrinter)
    pp.add_printer('ReferencingIdentifier', '^RSBase::SqlIo::ReferencingIdentifier<.*>$', ReferencingIdentifierPrinter)
    pp.add_printer('SetVector', '^RSBase::SetVector<.*>$', SetVectorPrinter)
    pp.add_printer('Signal', '^RSInfra::Signal$', SignalPrinter)
    pp.add_printer('Station', '^RSBetrieb::Station$', StationPrinter)
    pp.add_printer('StationsZeit', '^RSBetrieb::StationsZeiten::StationsZeit$', StationsZeitPrinter)
    pp.add_printer('StationsZeiten', '^RSBetrieb::StationsZeiten$', StationsZeitenPrinter)
    pp.add_printer('Strecke', '^RSInfra::Strecke$', StreckePrinter)
    pp.add_printer('TWennX', '^RSInfra::Tools::VTTextCompute::TWennX<.*>$', TWennXPrinter)
    pp.add_printer('Takt', '^RSBetrieb::Takt$', TaktPrinter)
    pp.add_printer('UUID', '^RSBase::UUID$', UUIDPrinter)  # TODO
    pp.add_printer('Unit', '^RSBase::Units::(Int)?(Acceleration|Duration|Time|Length|Mass|Speed|Force)$', UnitPrinter)
    pp.add_printer('VerkehrsTageBaustein', '^RSInfra::VerkehrsTageBaustein$', VerkehrsTageBausteinPrinter)
    pp.add_printer('Weiche', '^RSInfra::Weiche$', KnotenPrinter)  # TODO
    pp.add_printer('Zeit', '^RSBase::Zeit$', ZeitPrinter)
    pp.add_printer('ZeitlicheGueltigkeit', '^RSBase::ZeitlicheGueltigkeit$', ZeitlicheGueltigkeitPrinter)
    pp.add_printer('Zug', '^RSBetrieb::Zug$', ZugPrinter)
    pp.add_printer('Zugfahrt', '^(RSBetrieb::Zugfahrt::(((VSoll)?Base|Belegung|VMax)Zugfahrt)|RSSimu::(ZugfahrtMitVerspaetungsBerechner|PrognoseZugfahrt|Zugfahrt)|Mock::Zugfahrt)$', ZugfahrtPrinter)
    for sp in pp.subprinters:
        safe_printer(with_children(sp.gen_printer))
    return pp




@trace
def register_rs_printers(obj):
    gdb.printing.register_pretty_printer(obj, build_rs_pretty_printer())


register_rs_printers(None)


# deref_printers needs to be the very first printer: pointers and references
# are resolved (to their dynamic type) before any other printer sees them.
# register_pretty_printer() inserts at the front, so it comes last.
gdb.pretty_printers.insert(0, deref_printers)


# Exception safety of foreign printers (libstdc++), also of those registered
# later for new objfiles (auto-load of libstdc++.so).


def harden_all_printers():
    """Harden the printers of gdb, the progspaces and the objfiles; keep deref_printers first."""
    lists = [gdb.pretty_printers]
    with contextlib.suppress(Exception):
        lists.append(gdb.current_progspace().pretty_printers)
    with contextlib.suppress(Exception):
        lists.extend(objfile.pretty_printers for objfile in gdb.objfiles())
    with contextlib.suppress(Exception):
        for progspace in gdb.progspaces():
            lists.append(progspace.pretty_printers)
            lists.extend(objfile.pretty_printers for objfile in progspace.objfiles())
    for printers in lists:
        with contextlib.suppress(Exception):
            harden_printers(printers)
    with contextlib.suppress(Exception):
        ensure_deref_first()


# re-source: replace the hooks of the previous run instead of adding more
with contextlib.suppress(Exception):
    gdb.events.new_objfile.disconnect(harden_new_objfile)
with contextlib.suppress(Exception):
    gdb.events.stop.disconnect(harden_on_stop)


def harden_new_objfile(event):
    """new_objfile hook: harden the printers registered since (gdb >= 11: after auto-load)."""
    harden_all_printers()


def harden_on_stop(event):
    """stop hook: catch up before the variables are shown (older gdb may report
    new_objfile before the auto-load script of the objfile ran)."""
    harden_all_printers()


with contextlib.suppress(Exception):
    gdb.events.new_objfile.connect(harden_new_objfile)
with contextlib.suppress(Exception):
    gdb.events.stop.connect(harden_on_stop)
harden_all_printers()
