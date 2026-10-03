"""Exact sparse quartic certificates for finite-mass partitioned lattice histories.

No dependencies. All exported residuals are explicit integer polynomials of
degree at most two; the scalar certificate is their sum of squares.
Research implementation, not a formal proof. See the accompanying mathematical report.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
import json
import gzip
from pathlib import Path
from typing import Iterable, Mapping


def nat(x, name="value"):
    if type(x) is not int or x < 0:
        raise ValueError(f"{name} must be an exact nonnegative Python integer")
    return x


def integer(x, name="value"):
    if type(x) is not int:
        raise ValueError(f"{name} must be an exact Python integer")
    return x


@dataclass(frozen=True)
class Poly:
    """Canonical sparse polynomial; negative variable indices are free inputs."""
    terms: tuple[tuple[tuple[int, ...], int], ...]

    @staticmethod
    def make(terms):
        acc = {}
        for monomial, coefficient in terms:
            coefficient = integer(coefficient, "coefficient")
            key = tuple(sorted(monomial))
            if any(type(v) is not int for v in key):
                raise ValueError("invalid polynomial variable")
            acc[key] = acc.get(key, 0) + coefficient
        return Poly(tuple(sorted((m, c) for m, c in acc.items() if c)))

    @staticmethod
    def constant(value):
        integer(value)
        return Poly(()) if value == 0 else Poly((((), value),))

    @staticmethod
    def variable(index):
        return Poly((((integer(index),), 1),))

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Poly) else Poly.constant(x)

    def __add__(self, other):
        return Poly.make(self.terms + self.coerce(other).terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly(tuple((m, -c) for m, c in self.terms))

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return Poly.make((m + n, a * b)
                         for m, a in self.terms for n, b in other.terms)

    __rmul__ = __mul__

    def evaluate(self, witnesses, parameters=()):
        out = 0
        for monomial, coefficient in self.terms:
            value = coefficient
            for index in monomial:
                value *= witnesses[index] if index >= 0 else parameters[-1-index]
            out += value
        return out

    @property
    def degree(self):
        return max((len(m) for m, _ in self.terms), default=0)

    def json(self):
        return [[list(m), c] for m, c in self.terms]

    @staticmethod
    def from_json(data, witness_count, parameter_count):
        if not isinstance(data, list):
            raise ValueError("polynomial must be an explicit term list")
        terms = []
        for item in data:
            if not isinstance(item, list) or len(item) != 2:
                raise ValueError("invalid term")
            monomial, coefficient = item
            if not isinstance(monomial, list):
                raise ValueError("invalid monomial")
            for index in monomial:
                integer(index, "variable index")
                if not -parameter_count <= index < witness_count:
                    raise ValueError("variable index out of range")
            terms.append((monomial, integer(coefficient)))
        answer = Poly.make(terms)
        if answer.degree > 2:
            raise ValueError("residual degree exceeds two")
        return answer


def psum(expressions):
    return Poly.make(term for expression in expressions
                     for term in Poly.coerce(expression).terms)


@dataclass(frozen=True)
class LocalTable:
    """Input (R,C,L), output (L,C,R). Mutable caller tables are copied."""
    K: int
    rows: tuple[tuple[tuple[int, int, int], tuple[int, int, int]], ...]

    def __post_init__(self):
        nat(self.K, "K")
        if self.K < 1 or type(self.rows) is not tuple:
            raise ValueError("K>=1 and immutable rows are required")
        expected = tuple(product(range(self.K + 1), repeat=3))
        if len(self.rows) != len(expected):
            raise ValueError("local table is not total")
        for index, item in enumerate(self.rows):
            if type(item) is not tuple or len(item) != 2:
                raise ValueError("invalid row")
            key, value = item
            if type(key) is not tuple or type(value) is not tuple:
                raise ValueError("immutable triples are required")
            if key != expected[index] or len(value) != 3:
                raise ValueError("table keys must be exact canonical triples")
            if any(type(x) is not int or not 0 <= x <= self.K for x in key + value):
                raise ValueError("invalid table scalar")
            if sum(key) != sum(value):
                raise ValueError("table fails mass conservation")

    @classmethod
    def from_mapping(cls, K, table):
        nat(K, "K")
        if not isinstance(table, Mapping):
            raise ValueError("table must be a mapping")
        if any(type(key) is not tuple or len(key) != 3 or any(type(x) is not int for x in key) for key in table):
            raise ValueError("table keys must be exact integer triples")
        expected = set(product(range(K+1), repeat=3))
        if set(table) != expected:
            raise ValueError("table is not total or has extra keys")
        return cls(K, tuple((tuple(key), tuple(table[key])) for key in sorted(expected)))

    def __call__(self, r, c, l):
        for x in (r, c, l):
            nat(x)
            if x > self.K:
                raise ValueError("channel mass exceeds local cap")
        q = self.K + 1
        return self.rows[(r*q+c)*q+l][1]

    @property
    def reversible(self):
        return len({value for _, value in self.rows}) == len(self.rows)

    def inverse_collision(self, l, c, r):
        if not self.reversible:
            raise ValueError("local table is not a permutation")
        target = (l, c, r)
        for key, value in self.rows:
            if value == target:
                return key
        raise ValueError("invalid output triple")


def validate_config(table: LocalTable, configuration):
    if not isinstance(configuration, Mapping):
        raise ValueError("configuration must be a finite mapping")
    out = {}
    for position, value in configuration.items():
        integer(position, "position")
        if not isinstance(value, (tuple, list)) or len(value) != 3:
            raise ValueError("each cell must have three masses")
        triple = tuple(nat(x, "channel mass") for x in value)
        if max(triple) > table.K:
            raise ValueError("channel mass exceeds local cap")
        if sum(triple):
            out[position] = triple
    return out


def unit_records(table, configuration, shift=0):
    configuration = validate_config(table, configuration)
    integer(shift)
    return sorted((x + shift, channel)
                  for x, state in configuration.items()
                  for channel, mass in enumerate(state)
                  for _ in range(mass))


def records_to_config(records, shift=0):
    integer(shift)
    out = {}
    for x, channel in records:
        integer(x)
        nat(channel, "channel")
        if channel > 2:
            raise ValueError("invalid channel")
        out.setdefault(x-shift, [0, 0, 0])[channel] += 1
    return {x: tuple(state) for x, state in sorted(out.items())}


def physical_step(table, configuration):
    configuration = validate_config(table, configuration)
    candidates = {x+d for x in configuration for d in (-1, 0, 1)}
    zero = (0, 0, 0)
    out = {}
    for x in candidates:
        output = table(configuration.get(x-1, zero)[2],
                       configuration.get(x, zero)[1],
                       configuration.get(x+1, zero)[0])
        if any(output):
            out[x] = output
    return dict(sorted(out.items()))


def physical_inverse(table, configuration):
    configuration = validate_config(table, configuration)
    out = {}
    for x, state in configuration.items():
        r, c, l = table.inverse_collision(*state)
        if r:
            out.setdefault(x-1, [0, 0, 0])[2] = r
        if c:
            out.setdefault(x, [0, 0, 0])[1] = c
        if l:
            out.setdefault(x+1, [0, 0, 0])[0] = l
    return {x: tuple(state) for x, state in sorted(out.items())}


class Builder:
    def __init__(self, parameters=(), orthant_exact=False, lookup_backend="rows", allowed_inputs=None):
        if type(orthant_exact) is not bool:
            raise ValueError("orthant_exact must be a Boolean")
        self.orthant_exact = orthant_exact
        if lookup_backend not in ("rows", "factorized"):
            raise ValueError("unsupported lookup backend")
        if allowed_inputs is not None and lookup_backend != "rows":
            raise ValueError("partial table contract requires row lookup")
        self.lookup_backend = lookup_backend
        self.allowed_inputs = allowed_inputs
        self._row_cache = None
        self.parameters = tuple(nat(x, "parameter") for x in parameters)
        self.values = []
        self.names = []
        self.residuals = []
        self.residual_names = []
        self.rows = []
        self.sections = []

    def value(self, expression):
        return Poly.coerce(expression).evaluate(self.values, self.parameters)

    def new(self, name, value):
        nat(value, name)
        out = Poly.variable(len(self.values))
        self.names.append(name)
        self.values.append(value)
        return out

    def constrain(self, name, expression):
        expression = Poly.coerce(expression)
        if expression.degree > 2:
            raise AssertionError(f"degree error in {name}")
        self.residual_names.append(name)
        self.residuals.append(expression)

    def wire(self, name, expression):
        expression = Poly.coerce(expression)
        variable = self.new(name, self.value(expression))
        self.constrain(name, variable-expression)
        return variable

    def cmp(self, name, x, y):
        x, y = Poly.coerce(x), Poly.coerce(y)
        xv, yv = self.value(x), self.value(y)
        nat(xv, name+".x")
        nat(yv, name+".y")
        flag = int(yv >= xv)
        gap = yv-xv if flag else xv-yv-1
        b = self.new(name+".b", flag)
        d = self.new(name+".d", gap)
        self.constrain(name+".boolean", b*(b-1))
        self.constrain(name+".gap", y-x-(2*b-1)*d-b+1)
        return b

    def eq(self, name, x, y):
        return self.cmp(name+".weak", x, y)-self.cmp(name+".strict", Poly.coerce(x)+1, y)

    def channel(self, name, z):
        value = self.value(z)
        if value not in range(3):
            raise ValueError("invalid channel while constructing witness")
        l, c, r = [self.new(name+suffix, int(value == i))
                   for i, suffix in enumerate((".L", ".C", ".R"))]
        self.constrain(name+".simplex", l+c+r-1)
        self.constrain(name+".code", Poly.coerce(z)-c-2*r)
        if self.orthant_exact:
            self.constrain(name+".onehot_norm", l*l+c*c+r*r-1)
        return l, c, r

    def sort(self, name, rows):
        rows = list(rows)
        for end in range(len(rows)-1, 0, -1):
            for index in range(end):
                tag = f"{name}.{end}.{index}"
                x, z = rows[index]
                y, w = rows[index+1]
                b = self.cmp(tag+".order", 3*x+z, 3*y+w)
                xmin = self.wire(tag+".xmin", y+b*(x-y))
                zmin = self.wire(tag+".zmin", w+b*(z-w))
                xmax = self.wire(tag+".xmax", x+y-xmin)
                zmax = self.wire(tag+".zmax", z+w-zmin)
                rows[index:index+2] = [(xmin, zmin), (xmax, zmax)]
        return rows

    def lookup(self, name, table, incoming):
        if self.lookup_backend == "rows":
            if self._row_cache is None or self._row_cache[0] is not table:
                allowed = None if self.allowed_inputs is None else frozenset(self.allowed_inputs)
                rows = table.rows if allowed is None else tuple(row for row in table.rows if row[0] in allowed)
                self._row_cache = (table, rows)
            rows = self._row_cache[1]
            target = tuple(self.value(v) for v in incoming)
            if target not in {key for key, _ in rows}:
                raise ValueError("witness trajectory leaves the declared partial-table domain")
            selector = [self.new(f"{name}.row.{i}", int(key == target)) for i, (key, _) in enumerate(rows)]
            self.constrain(name+".row_simplex", psum(selector)-1)
            if self.orthant_exact:
                self.constrain(name+".row_norm", psum(s*s for s in selector)-1)
            for channel in range(3):
                self.constrain(f"{name}.input.{channel}", incoming[channel]-psum(key[channel]*s for (key, _), s in zip(rows, selector)))
            return tuple(self.wire(f"{name}.out.{channel}", psum(value[channel]*s for (_, value), s in zip(rows, selector))) for channel in range(3))
        return self.lookup_factorized(name, table, incoming)

    def lookup_factorized(self, name, table, incoming):
        q = table.K+1
        vectors = []
        for label, value in zip(("R", "C", "L"), incoming):
            known = self.value(value)
            if not 0 <= known <= table.K:
                raise ValueError("incoming lane outside table")
            vector = [self.new(f"{name}.{label}.{a}", int(a == known)) for a in range(q)]
            self.constrain(name+label+".simplex", psum(vector)-1)
            self.constrain(name+label+".value", value-psum(a*v for a, v in enumerate(vector)))
            if self.orthant_exact:
                self.constrain(name+label+".onehot_norm", psum(v*v for v in vector)-1)
            vectors.append(vector)
        U, V, W = vectors
        pairs = {(a, b): self.wire(f"{name}.pair.{a}.{b}", U[a]*V[b])
                 for a in range(q) for b in range(q)}
        triples = {(a, b, c): self.wire(f"{name}.triple.{a}.{b}.{c}", pairs[a, b]*W[c])
                   for a in range(q) for b in range(q) for c in range(q)}
        return tuple(self.wire(f"{name}.out.{channel}",
                               psum(output[channel]*triples[key] for key, output in table.rows))
                     for channel in range(3))

    def layer(self, table, rows, t):
        before = (len(self.values), len(self.residuals))
        M = len(rows)
        prefix = f"t{t}"
        channels = [self.channel(f"{prefix}.ch.{i}", z) for i, (_, z) in enumerate(rows)]
        destinations = [self.wire(f"{prefix}.stream.{i}", x+channels[i][2]-channels[i][0])
                        for i, (x, _) in enumerate(rows)]
        equality = {(i, i): Poly.constant(1) for i in range(M)}
        for i in range(M):
            for j in range(i+1, M):
                equality[i, j] = equality[j, i] = self.eq(f"{prefix}.eq.{i}.{j}", destinations[i], destinations[j])
        outgoing = []
        for i in range(M):
            incoming = tuple(self.wire(f"{prefix}.mass.{i}.{channel}",
                                      psum(equality[i, j]*channels[j][channel] for j in range(M)))
                             for channel in (2, 1, 0))
            a, b, c = self.lookup(f"{prefix}.g.{i}", table, incoming)
            rank = psum(equality[i, j] for j in range(i+1))
            h = self.cmp(f"{prefix}.rankL.{i}", rank, a)
            k = self.cmp(f"{prefix}.rankLC.{i}", rank, a+b)
            outgoing.append((destinations[i], 2-h-k))
        answer = self.sort(prefix+".sort", outgoing)
        q = table.K+1
        if self.lookup_backend == "rows":
            s = q**3 if self.allowed_inputs is None else len(self.allowed_inputs)
            expected = (M*(s+14)+5*M*(M-1),
                        17*M+5*M*(M-1)+2*M*int(self.orthant_exact))
        else:
            expected = (M*(q**3+q**2+3*q+14)+5*M*(M-1),
                        M*(q**3+q**2+19)+5*M*(M-1)+4*M*int(self.orthant_exact))
        actual = (len(self.values)-before[0], len(self.residuals)-before[1])
        if actual != expected:
            raise AssertionError((actual, expected))
        self.sections.append({"name": prefix, "witnesses": actual[0], "residuals": actual[1]})
        return answer, channels

    def validate_witness(self, witnesses=None, parameters=None):
        witnesses = self.values if witnesses is None else witnesses
        parameters = self.parameters if parameters is None else parameters
        if len(witnesses) != len(self.values) or len(parameters) != len(self.parameters):
            raise ValueError("incorrect witness or parameter length")
        for value in witnesses:
            nat(value, "witness")
        for value in parameters:
            nat(value, "parameter")
        return all(res.evaluate(witnesses, parameters) == 0 for res in self.residuals)

    def score(self, witnesses=None, parameters=None):
        witnesses = self.values if witnesses is None else witnesses
        parameters = self.parameters if parameters is None else parameters
        return sum(res.evaluate(witnesses, parameters)**2 for res in self.residuals)

    def decode(self, physical_shift):
        return [records_to_config([(self.value(x), self.value(z)) for x, z in row], physical_shift)
                for row in self.rows]

    def decode_solution(self, physical_shift, witnesses, parameters=None):
        parameters = self.parameters if parameters is None else parameters
        if not self.validate_witness(witnesses, parameters):
            raise ValueError("tuple is not a natural zero of the certificate")
        return [records_to_config([(x.evaluate(witnesses, parameters), z.evaluate(witnesses, parameters))
                                   for x, z in row], physical_shift) for row in self.rows]

    def accounting(self):
        terms = sum(len(r.terms) for r in self.residuals)
        occurrences = sum(len(m) for r in self.residuals for m, _ in r.terms)
        R = len(self.residuals)
        return {"witnesses": len(self.values), "residuals": R,
                "nonzero_residual_terms": terms,
                "literal_multiplications": occurrences+R,
                "literal_additions": terms+R,
                "literal_evaluator": "Each monomial starts at its integer coefficient and multiplies each listed variable; each residual accumulates terms starting at zero; square all residuals and add starting at zero. No gates omitted.",
                "max_coefficient_bits": max((abs(c).bit_length() for r in self.residuals for _, c in r.terms), default=0),
                "residual_degree": max((r.degree for r in self.residuals), default=0),
                "polynomial_degree_upper_bound": 4}

    def export(self, path, metadata):
        """Exports every coefficient, full witness, endpoint aliases, and input binding."""
        payload = {"format": "sparse-mass-residuals-v1", "domain": "natural",
                   "polynomial": "sum_of_squares_of_all_residuals", "metadata": metadata,
                   "parameter_values": list(self.parameters), "witness_values": list(self.values),
                   "witness_names": list(self.names), "residual_names": list(self.residual_names),
                   "residuals": [p.json() for p in self.residuals],
                   "rows": [[[x.json(), z.json()] for x, z in row] for row in self.rows],
                   "sections": self.sections,
                   "counts": self.accounting()}
        path = Path(path)
        if path.suffix == ".gz":
            with gzip.open(path, "wt", encoding="utf-8") as stream:
                json.dump(payload, stream, separators=(",", ":"))
                stream.write("\n")
        else:
            path.write_text(json.dumps(payload, indent=2)+"\n")
        return payload


def normalize_allowed_inputs(table, allowed_inputs):
    if allowed_inputs is None:
        return None
    keys = []
    for key in allowed_inputs:
        if not isinstance(key, (tuple, list)) or len(key) != 3 or any(type(x) is not int or not 0 <= x <= table.K for x in key):
            raise ValueError("invalid partial-table input key")
        keys.append(tuple(key))
    if len(set(keys)) != len(keys) or not keys or (0,0,0) not in keys:
        raise ValueError("partial table must contain vacuum and distinct keys")
    return tuple(sorted(keys))


def compile_history(table, configuration, T, endpoint=None, orthant_exact=False,
                    lookup_backend="rows", allowed_inputs=None):
    nat(T, "T")
    configuration = validate_config(table, configuration)
    if not configuration:
        raise ValueError("M=0 is a separate trivial vacuum case")
    origin = min(configuration)
    D = max(configuration)-origin
    shift = T-origin
    records = unit_records(table, configuration, shift)
    allowed_inputs = normalize_allowed_inputs(table, allowed_inputs)
    builder = Builder(orthant_exact=orthant_exact, lookup_backend=lookup_backend, allowed_inputs=allowed_inputs)
    rows = [(Poly.constant(x), Poly.constant(z)) for x, z in records]
    builder.rows.append(rows)
    for t in range(T):
        rows, _ = builder.layer(table, rows, t)
        builder.rows.append(rows)
    if endpoint is not None:
        target = unit_records(table, endpoint, shift)
        if len(target) != len(records):
            builder.constrain("endpoint.mass_mismatch", 1)
        else:
            for i, ((x, z), (a, b)) in enumerate(zip(rows, target)):
                builder.constrain(f"endpoint.{i}.position", x-a)
                builder.constrain(f"endpoint.{i}.channel", z-b)
    metadata = {"K": table.K, "M": len(records), "T": T, "D": D, "origin": origin,
                "physical_shift": shift, "reversible": table.reversible,
                "orthant_exact": orthant_exact,
                "lookup_backend": lookup_backend,
                "allowed_inputs": None if allowed_inputs is None else [list(key) for key in allowed_inputs],
                "initial_configuration": [[x, list(s)] for x, s in sorted(configuration.items())],
                "local_table": [[list(k), list(v)] for k, v in table.rows],
                "witness_height_bound": 3*(D+2*T)+len(records)+3*table.K+3,
                "scope": "fixed valid initial configuration and external horizon",
                "observation": "prescribed endpoint" if endpoint is not None else "none"}
    if endpoint is not None:
        metadata["endpoint_configuration"] = [[x, list(s)] for x, s in sorted(validate_config(table, endpoint).items())]
    return builder, metadata


def compile_morita_inputs(table, m, gamma, initial_increment_counter, n0, n1, T,
                          first_pulse=False, orthant_exact=False, lookup_backend="rows", allowed_inputs=None):
    """Paid two-counter loader; semantic transport requires an audited local table.

    This API makes no claim that an arbitrary table is a Morita simulator. It
    emits the exact phi-shaped input and (optionally) the stated observation.
    """
    for name, value in (("m", m), ("n0", n0), ("n1", n1), ("T", T)):
        nat(value, name)
    if m < 2 or table.K != m+18:
        raise ValueError("requires m>=2 and K=m+18")
    if gamma not in (0, 2, 4, 6, 7) or type(gamma) is not int:
        raise ValueError("invalid opcode")
    if initial_increment_counter is not None and (type(initial_increment_counter) is not int or initial_increment_counter not in (0, 1)):
        raise ValueError("invalid increment counter")
    if (gamma == 2) != (initial_increment_counter == 0) or (gamma == 6) != (initial_increment_counter == 1):
        raise ValueError("increment opcode mismatch")
    if type(first_pulse) is not bool or first_pulse and T < 1:
        raise ValueError("pulse observation requires T>=1")
    allowed_inputs = normalize_allowed_inputs(table, allowed_inputs)
    builder = Builder((n0, n1), orthant_exact=orthant_exact, lookup_backend=lookup_backend, allowed_inputs=allowed_inputs)
    n = [Poly.variable(-1), Poly.variable(-2)]
    zero = [builder.cmp(f"loader.zero.{j}", n[j], 0) for j in range(2)]
    rows = [(Poly.constant(T), Poly.constant(channel))
            for channel, mass in enumerate((10, m+6-gamma, gamma)) for _ in range(mass)]
    for j in range(2):
        channel = 1+zero[j] if initial_increment_counter == j else Poly.constant(1)
        rows.extend((n[j]+T, channel) for _ in range(2**j))
    M = m+19
    assert len(rows) == M
    rows = builder.sort("loader.sort", rows)
    assert len(builder.values) == len(builder.residuals) == 4+3*M*(M-1)
    builder.sections.append({"name": "loader", "witnesses": len(builder.values), "residuals": len(builder.residuals)})
    builder.rows.append(rows)
    channel_rows = []
    for t in range(T):
        rows, channels = builder.layer(table, rows, t)
        channel_rows.append(channels)
        builder.rows.append(rows)
    if first_pulse:
        before = (len(builder.values), len(builder.residuals))
        channel_rows.append([builder.channel(f"observe.final.{i}", z) for i, (_, z) in enumerate(rows)])
        for t in range(1, T+1):
            hits = [builder.eq(f"observe.eq.{t}.{i}", x, T-1)
                    for i, (x, _) in enumerate(builder.rows[t])]
            mass = psum(hits[i]*channel_rows[t][i][0] for i in range(M))
            builder.constrain(f"observe.leftmass.{t}", mass-int(t == T))
        actual = (len(builder.values)-before[0], len(builder.residuals)-before[1])
        expected = (4*M*T+3*M, 4*M*T+2*M+T+M*int(orthant_exact))
        assert actual == expected
        builder.sections.append({"name": "first_pulse", "witnesses": actual[0], "residuals": actual[1]})
    metadata = {"K": table.K, "M": M, "T": T, "D": max(n0, n1), "origin": 0,
                "physical_shift": T, "reversible": table.reversible,
                "orthant_exact": orthant_exact,
                "lookup_backend": lookup_backend,
                "allowed_inputs": None if allowed_inputs is None else [list(key) for key in allowed_inputs],
                "input_contract": {"type": "Morita_phi_q0", "m": m, "gamma": gamma,
                                   "initial_increment_counter": initial_increment_counter},
                "local_table": [[list(k), list(v)] for k, v in table.rows],
                "witness_height_bound": 3*(max(n0,n1)+2*T)+M+3*table.K+3,
                "scope": "natural n0,n1 parameters, fixed external T; no unaudited simulation claim",
                "observation": "left channel at -1: zero before T, one at T" if first_pulse else "none"}
    return builder, metadata


def read_export(path):
    path = Path(path)
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            return json.load(stream)
    return json.loads(path.read_text())


def verify_export(path):
    """Replay the exported polynomial, not the original transition evaluator.

    This verifies the stated sum of squares and aliases. Rebinding a file to an
    intended automaton/input requires regenerate-and-compare, supplied by tests.
    """
    payload = read_export(path)
    if payload.get("format") != "sparse-mass-residuals-v1" or payload.get("domain") != "natural":
        raise ValueError("unknown export contract")
    if payload.get("polynomial") != "sum_of_squares_of_all_residuals":
        raise ValueError("invalid polynomial declaration")
    witnesses = payload["witness_values"]
    parameters = payload["parameter_values"]
    for value in witnesses+parameters:
        nat(value)
    V, P = len(witnesses), len(parameters)
    residuals = [Poly.from_json(data, V, P) for data in payload["residuals"]]
    if payload["counts"]["witnesses"] != V or payload["counts"]["residuals"] != len(residuals):
        raise ValueError("incorrect declared counts")
    values = [r.evaluate(witnesses, parameters) for r in residuals]
    rows = [[tuple(Poly.from_json(poly, V, P).evaluate(witnesses, parameters) for poly in record)
             for record in row] for row in payload["rows"]]
    return {"valid": all(v == 0 for v in values), "polynomial_value": sum(v*v for v in values),
            "witnesses": V, "residuals": len(residuals), "rows": rows}


def verify_bound_export(path):
    """Verify input/table/endpoint binding by exact deterministic regeneration.

    The object being certified is the public descriptor in metadata. A caller
    requiring one particular object must compare that descriptor with its own
    requested input; no certificate format can infer an unstated intention.
    """
    payload = read_export(path)
    metadata = payload["metadata"]
    K = metadata["K"]
    table = LocalTable(K, tuple((tuple(k), tuple(v)) for k, v in metadata["local_table"]))
    orthant = metadata["orthant_exact"]
    if "input_contract" in metadata:
        contract = metadata["input_contract"]
        if contract["type"] != "Morita_phi_q0":
            raise ValueError("unsupported loader")
        if metadata["observation"] not in ("none", "left channel at -1: zero before T, one at T"):
            raise ValueError("unsupported observation")
        n0, n1 = payload["parameter_values"]
        builder, expected_metadata = compile_morita_inputs(
            table, contract["m"], contract["gamma"], contract["initial_increment_counter"],
            n0, n1, metadata["T"], metadata["observation"] != "none", orthant,
            metadata["lookup_backend"], metadata["allowed_inputs"])
    else:
        if metadata["observation"] not in ("none", "prescribed endpoint"):
            raise ValueError("unsupported observation")
        def decode_descriptor(rows):
            if len({x for x, _ in rows}) != len(rows):
                raise ValueError("duplicate configuration sites")
            return {x: tuple(s) for x, s in rows}
        initial = decode_descriptor(metadata["initial_configuration"])
        endpoint = decode_descriptor(metadata["endpoint_configuration"]) if metadata["observation"] == "prescribed endpoint" else None
        builder, expected_metadata = compile_history(table, initial, metadata["T"], endpoint, orthant,
                                                     metadata["lookup_backend"], metadata["allowed_inputs"])
    if metadata != expected_metadata:
        raise ValueError("descriptor inconsistent with regenerated semantics")
    if payload["residuals"] != [p.json() for p in builder.residuals]:
        raise ValueError("residuals do not implement the stated input/table/observation")
    if payload["rows"] != [[[x.json(), z.json()] for x, z in row] for row in builder.rows]:
        raise ValueError("row aliases do not match the stated circuit")
    if payload["witness_names"] != builder.names or payload["residual_names"] != builder.residual_names or payload["sections"] != builder.sections:
        raise ValueError("named gate structure mismatch")
    if payload["parameter_values"] != list(builder.parameters):
        raise ValueError("parameter binding mismatch")
    if payload["counts"] != builder.accounting():
        raise ValueError("exported accounting mismatch")
    return verify_export(path)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("export", help="explicit exported residual JSON to verify")
    args = parser.parse_args()
    result = verify_bound_export(args.export)
    print(json.dumps({k: v for k, v in result.items() if k != "rows"}, indent=2))
    raise SystemExit(0 if result["valid"] else 1)
