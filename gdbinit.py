#!/usr/bin/env python
"""GDB pretty printers."""

from __future__ import print_function
import contextlib
import functools
import glob
import itertools
import sys
import gdb
import gdb.printing

print('Python ' + sys.version)
if sys.version_info.major < 3:
    print('Python 3 is required.')
    raise RuntimeError('Python 3 is required.')  # exit() would terminate gdb

# clear pretty printer list
gdb.pretty_printers[:] = []

# max nesting depth (of pp())
maxdepth: int = 10

# max children
maxchildren: int = 50

# indentation width = 4
indent: int = 2

# automatic dereferencing of pointers and references
deref: bool = True

# max string length
maxstrlen: int = 80

# print adresses on each dereference
printaddr: bool = False

print('Options:')
print(f'py maxdepth = {maxdepth}')
print(f'py maxchildren = {maxchildren}')
print(f'py indent = {indent}')
print(f'py deref = {deref}')
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
def dereference_tuple(val: gdb.Value, n: int) -> gdb.Value:
    """Return the nth value fron a tuple."""
    elem_typename = str(val.type.template_argument(n))
    try:
        pointer_typename = f'std::_Head_base<{n}, {elem_typename}, false>'
        pointer_type = gdb.lookup_type(pointer_typename)
    except gdb.error:  # C++20
        pointer_typename = f'std::_Head_base<{n}ul, {elem_typename}, false>'
        pointer_type = gdb.lookup_type(pointer_typename)
    return val.cast(pointer_type)['_M_head_impl']


@trace
def dereference_unique_ptr(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a std::unique_ptr."""
    # Alt: return val['_M_t']['_M_t']['_M_head_impl']
    return dereference_tuple(val['_M_t']['_M_t'], 0)


@trace
def dereference_shared_ptr(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a std::shared_ptr."""
    return val['_M_ptr']


@trace
def dereference_weak_ptr(val: gdb.Value) -> gdb.Value:
    """Return the raw pointer contained in a std::weak_ptr."""
    return val['_M_ptr']


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
    if val.type.code == gdb.TYPE_CODE_PTR:
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
    for f in fields:
        if not hasattr(f, 'bitpos'):  # static member
            continue
        try:
            if f.is_base_class:
                yield f.name, val.cast(f.type)
            else:
                yield f.name or '<anon>', val[f]
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
    """Wrap children(): stop at the first error instead of raising."""
    @functools.wraps(fn)
    def wrapper(self):
        try:
            for child in fn(self):
                yield child
        except Exception:
            return
    wrapper.safe = True
    return wrapper


def safe_display_hint(fn):
    """Wrap display_hint(): no hint instead of raising."""
    @functools.wraps(fn)
    def wrapper(self):
        try:
            return fn(self)
        except Exception:
            return None
    wrapper.safe = True
    return wrapper


def safe_printer(cls):
    """Make to_string(), children() and display_hint() of a printer class exception safe."""
    for name, wrap in (('to_string', safe_to_string),
                       ('children', safe_children),
                       ('display_hint', safe_display_hint)):
        fn = cls.__dict__.get(name)
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


# STL pretty printers


path = glob.glob('/usr/share/*/python/libstdcxx/v6/printers.py')
if len(path) == 0:
    path = glob.glob('/usr/share/*/*/python/libstdcxx/v6/printers.py')
if len(path) == 0:
    path = glob.glob('/usr/share/*/*/*/python/libstdcxx/v6/printers.py')
if len(path) > 0:
    sys.path.insert(0, path[0][:-25])
    from libstdcxx.v6.printers import register_libstdcxx_printers
    register_libstdcxx_printers(None)
else:
    print('libstc++ pretty printers not found')


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

    def children(self):
        """Return an interator to map content."""
        table = self.val['table_']
        buckets_arr = table['buckets_']
        # at most maxchildren entries (two children each); visited guards
        # against cyclic node chains
        count = min(int(table['size_']), maxchildren)
        visited = set()

        if has_field(buckets_arr, 'buckets'):  # boost >= 1.87 (fca)
            # bucket array with one node chain per bucket; the bucket at
            # index size_ is an always-empty sentinel
            buckets = buckets_arr['buckets']
            n = 0
            for i in range(int(buckets_arr['size_'])):
                if n >= 2 * count:
                    return
                node_ptr = (buckets + i).dereference()['next']
                while int(node_ptr) != 0 and int(node_ptr) not in visited and n < 2 * count:
                    visited.add(int(node_ptr))
                    node = node_ptr.dereference()
                    pair = node['buf']['t_']
                    yield str(n), pair['first']
                    yield str(n+1), pair['second']
                    n += 2
                    node_ptr = node['next']
            return

        # boost < 1.87
        # find types
        allocators_type = table['allocators_'].type
        node_allocator_type = allocators_type.template_argument(1)
        node_type = node_allocator_type.template_argument(0)
        pair_type = node_type.template_argument(0)

        # find first node
        buckets = table['buckets_']
        first_node = buckets[int(table['bucket_count_'])]
        node_ptr = first_node['next_']

        n = 0
        while int(node_ptr) != 0 and int(node_ptr) not in visited and n < 2 * count:
            visited.add(int(node_ptr))
            node = node_ptr.dereference()
            node_ptr = node['next_']
            buf = node.cast(node_type)['value_base_']['data_']['data_']['buf']
            pair = buf.dereference().cast(pair_type)
            yield str(n), pair['first']
            yield str(n+1), pair['second']
            n += 2

    def display_hint(self):
        """Return display hint (string/array/map)."""
        return 'map'


@trace
def build_boost_pretty_printer() -> gdb.printing.RegexpCollectionPrettyPrinter:
    """Build boost pretty printer collection."""
    pp = SafeRegexpCollectionPrettyPrinter('Boost')
    pp.add_printer('Optional', '^boost::optional<.*$', BoostOptionalPrinter)
    pp.add_printer('UnorderedMap', '^boost::unordered::unordered_map<.*$', BoostUnorderedMapPrinter)
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
        self.count = min(self.count, self.i + maxchildren)

    def __next__(self):
        """Return next value from list."""
        if self.i >= self.count:
            raise StopIteration
        i = self.i
        self.i += 1
        if self.qt6:
            return (str(i), (self.data + i).dereference())
        node = self.d['array'][i]
        if self.element_type.sizeof > self.ptr_size:
            # shortcut: movability not detectable in gdb; assumes every large
            # element is pointer-stored (true unless Q_DECLARE_TYPEINFO Movable)
            elem = node.cast(self.element_type.pointer()).dereference()
        else:
            elem = node.address.cast(self.element_type.pointer()).dereference()
        return (str(i), elem)


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


@trace_class
class QVariantPrinter:
    """Pretty printer for QVariant (WIP)."""

    def __init__(self, val: gdb.Value):
        """Initialize."""
        self.val = val

    def to_string(self) -> str:
        """Convert value to string."""
        d = self.val['d']
        if not has_field(d, 'type'):
            return '<QVariant>'  # Qt6 stores packedType/QMetaType, not implemented
        typ = int(d['type'])

        if typ == 0:
            return '<invalid QVariant>'
        else:
            return '<TODO>'


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


@trace
def deref_printers(val: gdb.Value):
    """Auto dereference pointers, references and typdefs."""
    if not deref:
        return None
    # Must never raise (see safe_printer). Without a printer of our own
    # (None) gdb shows the value natively.
    try:
        if val.type.code == gdb.TYPE_CODE_PTR:
            if int(val) == 0:
                return None
            # cast to derived type
            if val.dynamic_type != val.type:
                derived = val.cast(val.dynamic_type).dereference()
                derived.fetch_lazy()  # unreadable memory: show the pointer natively
                printer = gdb.default_visualizer(derived)
                return printer if printer is not None else DynamicPtrPrinter(val)
            # dereference pointers (except void*)
            if val.type.target().strip_typedefs().code != gdb.TYPE_CODE_VOID:
                target = val.referenced_value()
                target.fetch_lazy()
                return gdb.default_visualizer(target)
            return None
        if val.type.code == gdb.TYPE_CODE_REF or val.type.code == gdb.TYPE_CODE_RVALUE_REF:
            target = val.referenced_value()
            dyn = target.dynamic_type
            if dyn.strip_typedefs().unqualified() != target.type.strip_typedefs().unqualified():
                target = target.cast(dyn)
            target.fetch_lazy()
            return gdb.default_visualizer(target)
        if val.type.code == gdb.TYPE_CODE_TYPEDEF:
            return gdb.default_visualizer(val.cast(val.type.strip_typedefs()))
        typename = str(val.type)
        if typename.startswith('std::shared_ptr<'):
            ptr = dereference_shared_ptr(val)
        elif typename.startswith('std::unique_ptr<'):
            ptr = dereference_unique_ptr(val)
        elif typename.startswith('std::weak_ptr<'):
            ptr = dereference_weak_ptr(val)
        else:
            return None
        if int(ptr) == 0:
            return None
        target = ptr.dereference()
        target.fetch_lazy()
        return gdb.default_visualizer(target)
    except Exception:
        return None


# Needs to be the very first printer.
gdb.pretty_printers.insert(0, deref_printers)


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
        if 'Acceleration' in str(self.val.type):
            return str(self.val['m_Value']) + ' m/s^2'
        elif 'Duration' in str(self.val.type) or 'Time' in str(self.val.type):
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
            if 'Duration' in str(self.val.type):
                if days > 0:
                    result += str(days) + 'd '
                if hours > 0:
                    result += str(hours) + 'h '
                if minutes > 0:
                    result += str(minutes) + 'm '
                if seconds > 0 or result == '':
                    result += str(seconds) + 's '
            elif 'Time' in str(self.val.type):
                if days > 0:
                    result += str(days) + 'd '
                result += f'{hours:02}:{minutes:02}:{seconds:02}'
            return result
        elif 'Length' in str(self.val.type):
            return str(self.val['m_Value']) + ' m'
        elif 'Mass' in str(self.val.type):
            return str(self.val['m_Value']) + ' kg'
        elif 'Speed' in str(self.val.type):
            return str(self.val['m_Value'] * 3.6) + ' km/h'
        elif 'Force' in str(self.val.type):
            return str(self.val['m_Value']) + ' N'
        elif 'Energy' in str(self.val.type):
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
                type_name = self.val.type.name
                if not type_name:  # e.g. reference type
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
