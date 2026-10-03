# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Compact, streamed +,-,* DAG with exact fixed-integer numeral recipes.

Inputs, constants and gates have disjoint signed-64-bit operand namespaces.
No recipe may contain an input or a gate. Fixed powers are compile-time numerals;
power(base,n) and repunit(base,n) emit charged runtime multiplication/addition.
"""
from array import array
from pathlib import Path
import hashlib, json, mmap, os, resource, struct, time
INPUT_BASE = 1 << 50
MAGIC = b'CDAGv1\x00\x00'
ROW = struct.Struct('<Bqq')
OPCODES = {'+': 0, '-': 1, '*': 2}

class Limits:

    def __init__(self, max_nodes=6000000, max_constants=200000, max_seconds=600, max_rss_bytes=1800 * 1024 ** 2):
        self.max_nodes = max_nodes
        self.max_constants = max_constants
        self.max_seconds = max_seconds
        self.max_rss_bytes = max_rss_bytes

    def as_dict(self):
        return vars(self).copy()

class ConstantPool:

    def __init__(self, max_constants=200000, small_bits=1024):
        self.rows = []
        self.index = {}
        self.bounds = []
        self.small = []
        self.mods = {}
        self.max_constants = max_constants
        self.small_bits = small_bits
        self.zero = self.const(0)
        self.one = self.const(1)

    def _id(self, h):
        if type(h) is not int or h >= 0 or -h > len(self.rows):
            raise ValueError('Constant-only handle required')
        return -h - 1

    def _append(self, key, bound, value=None):
        if key in self.index:
            return self.index[key]
        if len(self.rows) >= self.max_constants:
            raise RuntimeError('Constant recipe resource limit')
        h = -len(self.rows) - 1
        self.index[key] = h
        self.rows.append(key)
        self.bounds.append(bound)
        self.small.append(value)
        return h

    def const(self, v):
        if type(v) is not int:
            raise TypeError('Exact integer numeral required')
        if v.bit_length() > self.small_bits:
            raise ValueError('Large fixed integers must use an explicit recipe')
        return self._append(('int', str(v)), abs(v).bit_length(), v)

    def recipe(self, op, *args):
        if op == 'pow2':
            e, = args
            if type(e) is not int or e < 0:
                raise ValueError('Fixed natural exponent required')
            return self.const(1 << e) if e + 1 <= self.small_bits else self._append(('pow2', e), e + 1)
        if op == 'geom4':
            n, = args
            if type(n) is not int or n < 0:
                raise ValueError('Fixed natural exponent required')
            return self.const(((1 << 2 * n) - 1) // 3) if 2 * n <= self.small_bits else self._append(('geom4', n), 2 * n)
        if op == 'affine_offset':
            return self.recipe('mul', self.const(2), self.recipe('geom4', args[0]))
        if op == 'affine_slope_minus_one':
            return self.recipe('sub', self.recipe('pow2', 2 * args[0] + 1), self.one)
        if op not in ('add', 'sub', 'mul') or len(args) != 2:
            raise ValueError('Unknown fixed numeral recipe')
        a, b = args
        ia = self._id(a)
        ib = self._id(b)
        if op == 'add':
            if a == self.zero:
                return b
            if b == self.zero:
                return a
        if op == 'sub':
            if b == self.zero:
                return a
            if a == b:
                return self.zero
        if op == 'mul':
            if a == self.zero or b == self.zero:
                return self.zero
            if a == self.one:
                return b
            if b == self.one:
                return a
        bound = self.bounds[ia] + self.bounds[ib] if op == 'mul' else max(self.bounds[ia], self.bounds[ib]) + 1
        if self.small[ia] is not None and self.small[ib] is not None and (bound <= self.small_bits):
            va, vb = (self.small[ia], self.small[ib])
            return self.const(va + vb if op == 'add' else va - vb if op == 'sub' else va * vb)
        if op in ('add', 'mul') and a > b:
            a, b = (b, a)
        return self._append((op, a, b), bound)

    def value_mod(self, h, modulus):
        target = self._id(h)
        if type(modulus) is not int or modulus < 2:
            raise ValueError('Modulus >=2 required')
        v = self.mods.setdefault(modulus, [])
        while len(v) <= target:
            row = self.rows[len(v)]
            op = row[0]
            if op == 'int':
                z = int(row[1]) % modulus
            elif op == 'pow2':
                z = pow(2, row[1], modulus)
            elif op == 'geom4':
                z = (pow(4, row[1], 3 * modulus) - 1) // 3 % modulus
            else:
                a, b = (v[-row[1] - 1], v[-row[2] - 1])
                z = (a + b if op == 'add' else a - b if op == 'sub' else a * b) % modulus
            v.append(z)
        return v[target]

    def value_exact(self, h, max_bits=2000000):
        target = self._id(h)
        if self.bounds[target] > max_bits:
            raise RuntimeError('Exact numeral bit limit')
        need = {target}
        stack = [target]
        while stack:
            i = stack.pop()
            row = self.rows[i]
            if row[0] in ('add', 'sub', 'mul'):
                for a in row[1:]:
                    j = -a - 1
                    if j not in need:
                        need.add(j)
                        stack.append(j)
        vals = {}
        for i in sorted(need):
            row = self.rows[i]
            op = row[0]
            if self.bounds[i] > max_bits:
                raise RuntimeError('Exact numeral intermediate bit limit')
            if op == 'int':
                z = int(row[1])
            elif op == 'pow2':
                z = 1 << row[1]
            elif op == 'geom4':
                z = ((1 << 2 * row[1]) - 1) // 3
            else:
                a, b = (vals[-row[1] - 1], vals[-row[2] - 1])
                z = a + b if op == 'add' else a - b if op == 'sub' else a * b
            vals[i] = z
        return vals[target]

class DAG:

    def __init__(self, path, limits=None):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.limits = limits or Limits()
        self.pool = ConstantPool(self.limits.max_constants)
        self.file = self.path.open('wb')
        self.file.write(MAGIC)
        self.buffer = bytearray()
        self.inputs = []
        self.input_names = {}
        self.input_count = 0
        self.input_roles = CounterLite()
        self.degrees = array('Q')
        self.counts = {'+': 0, '-': 0, '*': 0}
        self.powers = {}
        self.repunits = {}
        self.started = time.monotonic()
        self.closed = False
        self.snapshots = []

    def const(self, v):
        return self.pool.const(v)

    def recipe(self, op, *args):
        return self.pool.recipe(op, *args)

    def input(self, name, role='witness'):
        if name in self.input_names:
            ref, oldrole = self.input_names[name]
            if role != oldrole:
                raise ValueError('Input role mismatch')
            return ref
        if not isinstance(name, str) or role not in ('witness', 'external'):
            raise ValueError('Input name/role')
        ref = INPUT_BASE + self.input_count
        self.inputs.append(dict(name=name, start=self.input_count, count=1, role=role, domain='positive_integer'))
        self.input_names[name] = (ref, role)
        self.input_count += 1
        self.input_roles.add(role, 1)
        return ref

    def input_range(self, prefix, count, role='witness'):
        if type(count) is not int or count < 0 or prefix in self.input_names:
            raise ValueError('Fresh input range')
        start = self.input_count
        self.inputs.append(dict(name=prefix, start=start, count=count, role=role, domain='positive_integer', indexed=True))
        self.input_names[prefix] = (range(INPUT_BASE + start, INPUT_BASE + start + count), role)
        self.input_count += count
        self.input_roles.add(role, count)
        return range(INPUT_BASE + start, INPUT_BASE + start + count)

    def _degree(self, h):
        if type(h) is not int:
            raise TypeError('Integer operand handle required')
        if h < 0:
            self.pool._id(h)
            return 0
        if h >= INPUT_BASE:
            if h - INPUT_BASE >= self.input_count:
                raise ValueError('Undeclared input')
            return 1
        if h >= len(self.degrees):
            raise ValueError('Forward/unavailable gate')
        return self.degrees[h]

    def _gate(self, op, a, b):
        da, db = (self._degree(a), self._degree(b))
        h = len(self.degrees)
        if h >= self.limits.max_nodes:
            raise RuntimeError('Gate resource limit')
        degree = da + db if op == '*' else max(da, db)
        if degree >= 1 << 64:
            raise RuntimeError('Formal degree storage limit')
        self.degrees.append(degree)
        self.counts[op] += 1
        self.buffer.extend(ROW.pack(OPCODES[op], a, b))
        if len(self.buffer) >= 1024 * 1024:
            self.file.write(self.buffer)
            self.buffer.clear()
        if h % 100000 == 0:
            self.check_resources()
        return h

    def add(self, a, b, *_):
        if a == self.pool.zero:
            return b
        if b == self.pool.zero:
            return a
        if a < 0 and b < 0:
            return self.recipe('add', a, b)
        return self._gate('+', a, b)

    def sub(self, a, b, *_):
        if b == self.pool.zero:
            return a
        if a == b:
            return self.pool.zero
        if a < 0 and b < 0:
            return self.recipe('sub', a, b)
        return self._gate('-', a, b)

    def mul(self, a, b, *_):
        if a == self.pool.zero or b == self.pool.zero:
            return self.pool.zero
        if a == self.pool.one:
            return b
        if b == self.pool.one:
            return a
        if a < 0 and b < 0:
            return self.recipe('mul', a, b)
        return self._gate('*', a, b)

    def total(self, values, *_):
        out = self.pool.zero
        for a in values:
            out = self.add(out, a)
        return out

    def power(self, base, n):
        if type(n) is not int or n < 0:
            raise ValueError('Fixed runtime exponent required')
        key = (base, n)
        if key in self.powers:
            return self.powers[key]
        if n == 0:
            return self.pool.one
        if n == 1:
            return base
        out = base
        e = 1
        for bit in bin(n)[3:]:
            e *= 2
            k = (base, e)
            if k not in self.powers:
                self.powers[k] = self.mul(out, out)
            out = self.powers[k]
            if bit == '1':
                e += 1
                k = (base, e)
                if k not in self.powers:
                    self.powers[k] = self.mul(out, base)
                out = self.powers[k]
        self.powers[key] = out
        return out

    def repunit(self, base, n):
        if type(n) is not int or n < 0:
            raise ValueError('Fixed repunit length')
        key = (base, n)
        if key in self.repunits:
            return self.repunits[key]
        self.repunits[base, 0] = self.pool.zero
        self.repunits[base, 1] = self.pool.one
        chain = []
        k = n
        while (base, k) not in self.repunits:
            chain.append(k)
            k //= 2
        for k in reversed(chain):
            h = k // 2
            out = self.mul(self.repunits[base, h], self.add(self.pool.one, self.power(base, h)))
            if k % 2:
                out = self.add(out, self.power(base, k - 1))
            self.repunits[base, k] = out
        return self.repunits[key]

    def pack(self, values, base):
        if not hasattr(values, '__len__'):
            values = list(values)
        if not values:
            return self.pool.zero
        out = values[-1]
        for a in reversed(values[:-1]):
            out = self.add(a, self.mul(base, out))
        return out

    def hatpack(self, values, base):
        return self.sub(self.pack(values, base), self.repunit(base, len(values)))

    def check_resources(self):
        elapsed = time.monotonic() - self.started
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
        if elapsed > self.limits.max_seconds:
            raise RuntimeError('Wall-time resource limit')
        if rss > self.limits.max_rss_bytes:
            raise RuntimeError('RSS resource limit')
        return dict(elapsed_seconds=elapsed, max_rss_bytes=rss, gates=len(self.degrees), constants=len(self.pool.rows))

    def snapshot(self, label):
        s = dict(label=label, **self.check_resources())
        self.snapshots.append(s)
        return s

    def flush(self):
        if self.buffer:
            self.file.write(self.buffer)
            self.buffer.clear()
        self.file.flush()

    def finish(self, output, extra=None):
        self._degree(output)
        self.flush()
        self.file.close()
        self.closed = True
        n = len(self.degrees)
        expected = len(MAGIC) + ROW.size * n
        if self.path.stat().st_size != expected:
            raise ValueError('Truncated streamed DAG')
        live = bytearray((n + 7) // 8)
        used = bytearray((self.input_count + 7) // 8)

        def mark(a):
            if a < 0:
                return
            if a >= INPUT_BASE:
                q = a - INPUT_BASE
                used[q >> 3] |= 1 << (q & 7)
            else:
                live[a >> 3] |= 1 << (a & 7)
        mark(output)
        dead = 0
        with self.path.open('rb') as f:
            with mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as mm:
                for i in range(n - 1, -1, -1):
                    if live[i >> 3] & 1 << (i & 7):
                        op, a, b = ROW.unpack_from(mm, len(MAGIC) + ROW.size * i)
                        mark(a)
                        mark(b)
                    else:
                        dead += 1
        unused = [i for i in range(self.input_count) if not used[i >> 3] & 1 << (i & 7)]
        if dead or unused:
            raise ValueError(f'Dead source: {dead} gates, {len(unused)} inputs (first {unused[:8]})')
        manifest = dict(format='compact_dag_v1', magic_hex=MAGIC.hex(), row_struct='<Bqq', row_bytes=ROW.size, input_base=INPUT_BASE, input_count=self.input_count, inputs=self.inputs, constants=self.pool.rows, constant_count=len(self.pool.rows), output=output, ledger=dict(operations=n, multiplications=self.counts['*'], additions_subtractions=self.counts['+'] + self.counts['-'], positive_witnesses=self.input_roles.get('witness'), external_positive_coordinates=self.input_roles.get('external'), degree_upper=self._degree(output), all_gates_live=True, all_inputs_live=True), source_sha256=hash_file(self.path), source_bytes=expected, limits=self.limits.as_dict(), snapshots=self.snapshots, resources=self.check_resources(), extra=extra or {})
        self.path.with_suffix('.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
        return manifest

class CounterLite:

    def __init__(self):
        self.values = {}

    def add(self, k, v):
        self.values[k] = self.values.get(k, 0) + v

    def get(self, k):
        return self.values.get(k, 0)

def hash_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        while True:
            b = f.read(1024 * 1024)
            if not b:
                break
            h.update(b)
    return h.hexdigest()

def load_pool(rows):
    pool = ConstantPool()
    pool.rows = []
    pool.index = {}
    pool.bounds = []
    pool.small = []
    for r in rows:
        if r[0] == 'int':
            h = pool.const(int(r[1]))
        else:
            h = pool.recipe(r[0], *r[1:])
        if h != -len(pool.rows):
            raise ValueError('Noncanonical or duplicate recipe table')
    if pool.rows != [tuple(r) for r in rows]:
        raise ValueError('Noncanonical recipe table')
    return pool

def evaluate_mod(path, manifest, modulus, input_value):
    """Iterative evaluation; input_value receives zero-based input index."""
    pool = load_pool(manifest['constants'])
    vals = array('Q')
    count = manifest['ledger']['operations']

    def at(h):
        if h < 0:
            return pool.value_mod(h, modulus)
        if h >= INPUT_BASE:
            return input_value(h - INPUT_BASE) % modulus
        return vals[h]
    with open(path, 'rb') as f:
        if f.read(len(MAGIC)) != MAGIC:
            raise ValueError('Bad DAG magic')
        for i in range(count):
            row = f.read(ROW.size)
            if len(row) != ROW.size:
                raise ValueError('Truncated DAG row')
            op, a, b = ROW.unpack(row)
            aa, bb = (at(a), at(b))
            vals.append((aa + bb if op == 0 else aa - bb if op == 1 else aa * bb) % modulus)
        if f.read(1):
            raise ValueError('Trailing DAG bytes')
    return at(manifest['output'])
