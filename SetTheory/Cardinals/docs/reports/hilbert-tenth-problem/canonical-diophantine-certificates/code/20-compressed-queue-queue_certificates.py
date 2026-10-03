"""Exact, history-free quartic certificates for grammar-compressed FIFO traces.

Python 3.10+, standard library only. This constructs and checks certificates;
it is not a general Diophantine solver. A grammar is a topologically ordered
sequence of Leaf/Concat nodes. Its root is its last node. All arithmetic is exact.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import gcd
from typing import Iterable, Sequence
import json


@dataclass(frozen=True)
class Action:
    read: str
    write: str
    source: int = 0
    target: int = 0


@dataclass(frozen=True)
class Leaf:
    action: Action


@dataclass(frozen=True)
class Concat:
    left: int
    right: int


Node = Leaf | Concat


def encode(word: str, alphabet: str = "01") -> tuple[int, int]:
    """Return (B**length, most-significant-first radix value), digits 1..s."""
    if not alphabet or len(set(alphabet)) != len(alphabet):
        raise ValueError("alphabet must be nonempty and have distinct characters")
    digits = {a: i + 1 for i, a in enumerate(alphabet)}
    base = len(alphabet) + 1
    p, c = 1, 0
    for a in word:
        if a not in digits:
            raise ValueError(f"symbol {a!r} is not in the alphabet")
        p, c = base * p, base * c + digits[a]
    return p, c


def compose_resource(first: tuple[int, int], second: tuple[int, int]) -> tuple[int, int]:
    r1, s1 = first
    r2, s2 = second
    if min(r1, s1, r2, s2) < 0:
        raise ValueError("resource coordinates must be natural numbers")
    cancel = min(s1, r2)
    return r1 + r2 - cancel, s2 + s1 - cancel


def power_resource(pair: tuple[int, int], exponent: int) -> tuple[int, int]:
    if exponent < 1:
        raise ValueError("the powered-grammar convention requires exponent >= 1")
    r, s = pair
    if min(r, s) < 0:
        raise ValueError("resource coordinates must be natural numbers")
    return r + (exponent - 1) * max(r - s, 0), s + (exponent - 1) * max(s - r, 0)


def power_word(pair: tuple[int, int], exponent: int) -> tuple[int, int]:
    """Evaluate the geometric-sum construction, including the empty-word case."""
    p, c = pair
    if exponent < 1 or p < 1 or c < 0:
        raise ValueError("invalid power input")
    if p == 1:
        if c != 0:
            raise ValueError("the only empty-word pair is (1, 0)")
        return 1, 0
    pk = p ** exponent
    return pk, c * ((pk - 1) // (p - 1))


@dataclass(frozen=True)
class Summary:
    pu: int
    cu: int
    pv: int
    cv: int
    r: int
    s: int
    source: int
    target: int
    steps: int

    def six(self) -> tuple[int, ...]:
        return self.pu, self.cu, self.pv, self.cv, self.r, self.s


def summarize(nodes: Sequence[Node], alphabet: str = "01") -> list[Summary]:
    if not nodes:
        raise ValueError("use an identity leaf Action('', '') for an empty trace")
    out: list[Summary] = []
    for i, node in enumerate(nodes):
        if isinstance(node, Leaf):
            a = node.action
            pu, cu = encode(a.read, alphabet)
            pv, cv = encode(a.write, alphabet)
            out.append(Summary(pu, cu, pv, cv, len(a.read), len(a.write),
                               a.source, a.target, 1))
        elif isinstance(node, Concat):
            if not (0 <= node.left < i and 0 <= node.right < i):
                raise ValueError(f"node {i}: references must point backward")
            x, y = out[node.left], out[node.right]
            if x.target != y.source:
                raise ValueError(f"node {i}: incompatible control endpoints")
            r, s = compose_resource((x.r, x.s), (y.r, y.s))
            out.append(Summary(x.pu * y.pu, x.cu * y.pu + y.cu,
                               x.pv * y.pv, x.cv * y.pv + y.cv,
                               r, s, x.source, y.target, x.steps + y.steps))
        else:
            raise TypeError(f"unsupported grammar node {node!r}")
    return out


class Poly:
    """Sparse integer polynomial. A monomial is a sorted tuple of indices."""
    def __init__(self, terms: dict[tuple[int, ...], int] | None = None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @staticmethod
    def coerce(value: Poly | int) -> Poly:
        if isinstance(value, Poly):
            return value
        if type(value) is not int:
            raise TypeError("polynomial constants must be exact integers")
        return Poly({(): value})

    @staticmethod
    def variable(index: int) -> Poly:
        return Poly({(index,): 1})

    def __add__(self, other: Poly | int) -> Poly:
        terms = self.terms.copy()
        for monomial, coefficient in self.coerce(other).terms.items():
            terms[monomial] = terms.get(monomial, 0) + coefficient
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self) -> Poly:
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other: Poly | int) -> Poly:
        return self + -self.coerce(other)

    def __rsub__(self, other: Poly | int) -> Poly:
        return self.coerce(other) + -self

    def __mul__(self, other: Poly | int) -> Poly:
        terms: dict[tuple[int, ...], int] = {}
        for m, c in self.terms.items():
            for n, d in self.coerce(other).terms.items():
                mn = tuple(sorted(m + n))
                terms[mn] = terms.get(mn, 0) + c * d
        return Poly(terms)

    __rmul__ = __mul__

    @property
    def degree(self) -> int:
        return max(map(len, self.terms), default=0)

    def evaluate(self, values: Sequence[int]) -> int:
        total = 0
        for monomial, coefficient in self.terms.items():
            term = coefficient
            for index in monomial:
                term *= values[index]
            total += term
        return total

    def export(self) -> list[dict]:
        return [{"coefficient": c, "variables": list(m)}
                for m, c in sorted(self.terms.items())]


@dataclass
class Certificate:
    names: list[str]
    residuals: list[Poly]
    witness: list[int]
    summaries: list[Summary]

    def accepts(self, values: Sequence[int] | None = None) -> bool:
        values = self.witness if values is None else values
        if len(values) != len(self.names) or any(type(x) is not int or x < 0 for x in values):
            return False
        return all(p.evaluate(values) == 0 for p in self.residuals)

    def polynomial(self) -> Poly:
        return sum((p * p for p in self.residuals), Poly())

    def export(self, filename: str, include_witness: bool = True) -> None:
        data = {"format": "fifo-quartic-v1", "domain": "natural numbers including zero",
                "variables": self.names,
                "residuals": [p.export() for p in self.residuals],
                "polynomial": self.polynomial().export(),
                "degree": self.polynomial().degree}
        if include_witness:
            data["witness"] = self.witness
        # Hex strings bypass Python's decimal-conversion limit for huge natural
        # witnesses; small integers retain the usual human-readable JSON form.
        data["integer_encoding"] = "JSON integers, or 0x/-0x hexadecimal strings for large values"
        def safe(obj):
            if type(obj) is int:
                return hex(obj) if obj.bit_length() > 2000 else obj
            if isinstance(obj, list):
                return [safe(x) for x in obj]
            if isinstance(obj, dict):
                return {k: safe(v) for k, v in obj.items()}
            return obj
        with open(filename, "w", encoding="utf-8") as f:
            json.dump(safe(data), f, indent=2)
            f.write("\n")


def compile_certificate(nodes: Sequence[Node], initial: str, final: str,
                        alphabet: str = "01") -> Certificate:
    """Compile exact root execution. Invalid syntax/control raises ValueError.

    All variables, including summary coordinates of leaves, are retained for
    the article's exact count: 6g+3c+1 variables, 6l+9c+3 residuals.
    For an invalid execution, `witness` is only a candidate and fails checking.
    """
    summaries = summarize(nodes, alphabet)
    names: list[str] = []
    values: list[int] = []
    residuals: list[Poly] = []
    variables: list[list[Poly]] = []

    def fresh(name: str, value: int) -> Poly:
        p = Poly.variable(len(names))
        names.append(name)
        values.append(value)
        return p

    for i, (node, summary) in enumerate(zip(nodes, summaries)):
        row = [fresh(f"n{i}_{name}", value) for name, value in
               zip(("PU", "CU", "PV", "CV", "R", "S"), summary.six())]
        variables.append(row)
        pu, cu, pv, cv, r, s = row
        if isinstance(node, Leaf):
            residuals.extend(p - v for p, v in zip(row, summary.six()))
        else:
            x, y = variables[node.left], variables[node.right]
            sx, sy = summaries[node.left], summaries[node.right]
            cancel_value = min(sx.s, sy.r)
            cancel = fresh(f"n{i}_cancel", cancel_value)
            alpha = fresh(f"n{i}_alpha", sx.s - cancel_value)
            beta = fresh(f"n{i}_beta", sy.r - cancel_value)
            residuals.extend((pu - x[0] * y[0], cu - x[1] * y[0] - y[1],
                              pv - x[2] * y[2], cv - x[3] * y[2] - y[3],
                              x[5] - cancel - alpha, y[4] - cancel - beta,
                              alpha * beta, r - x[4] - beta, s - y[5] - alpha))
    pq, cq = encode(initial, alphabet)
    pf, cf = encode(final, alphabet)
    root = variables[-1]
    slack = fresh("root_slack", max(0, len(initial) - summaries[-1].r))
    residuals.extend((pq * root[2] - root[0] * pf,
                      cq * root[2] + root[3] - root[1] * pf - cf,
                      len(initial) - root[4] - slack))
    return Certificate(names, residuals, values, summaries)


def chain(actions: Sequence[Action]) -> list[Node]:
    if not actions:
        return [Leaf(Action("", ""))]
    nodes: list[Node] = [Leaf(actions[0])]
    root = 0
    for action in actions[1:]:
        nodes.append(Leaf(action))
        nodes.append(Concat(root, len(nodes) - 1))
        root = len(nodes) - 1
    return nodes


def expand(nodes: Sequence[Node], limit: int = 100000) -> list[Action]:
    """Expand only for small diagnostic examples, not needed by the compiler."""
    lengths: list[int] = []
    for i, node in enumerate(nodes):
        if isinstance(node, Leaf):
            lengths.append(1)
        else:
            if not 0 <= node.left < i or not 0 <= node.right < i:
                raise ValueError("references must point backward")
            lengths.append(lengths[node.left] + lengths[node.right])
    if not lengths or lengths[-1] > limit:
        raise ValueError("expanded trace exceeds the diagnostic limit")
    out: list[Action] = []
    stack = [len(nodes) - 1]
    while stack:
        node = nodes[stack.pop()]
        if isinstance(node, Leaf):
            out.append(node.action)
        else:
            stack.extend((node.right, node.left))
    return out


def run(actions: Iterable[Action], initial: str) -> str | None:
    queue = initial
    state: int | None = None
    for action in actions:
        if state is not None and state != action.source:
            return None
        if not queue.startswith(action.read):
            return None
        queue = queue[len(action.read):] + action.write
        state = action.target
    return queue


def trace_data(actions: Sequence[Action]) -> tuple[str, str, int, int]:
    r, s = 0, 0
    for i, action in enumerate(actions):
        if i and actions[i - 1].target != action.source:
            raise ValueError("invalid control path")
        r, s = compose_resource((r, s), (len(action.read), len(action.write)))
    return "".join(a.read for a in actions), "".join(a.write for a in actions), r, s


def lcp_eventual(initial: str, written: str, read: str) -> int | None:
    """LCP(initial + written**omega, read**omega); None denotes infinity.

    When written is empty the first stream is just the finite initial word.
    The finite threshold is justified by Fine--Wilf, not by a heuristic cap.
    """
    a, b, length = len(read), len(written), len(initial)
    if a == 0:
        raise ValueError("the loop theorem requires a nonempty total read word")
    for i, letter in enumerate(initial):
        if letter != read[i % a]:
            return i
    if b == 0:
        return length
    threshold = a + b - gcd(a, b)
    for j in range(threshold):
        if written[j % b] != read[(length + j) % a]:
            return length + j
    return None


def maximum_repetitions(actions: Sequence[Action], initial: str) -> int | None:
    """Exact number of executable whole copies, or None for indefinitely many."""
    if not actions or actions[0].source != actions[-1].target:
        raise ValueError("the macro must be a nonempty closed control path")
    read, written, r, _ = trace_data(actions)
    a, b, length = len(read), len(written), len(initial)
    if a == 0:
        raise ValueError("the theorem requires a nonempty total read word")
    if length < r:
        return 0
    n_length = None if b >= a else 1 + (length - r) // (a - b)
    match = lcp_eventual(initial, written, read)
    n_content = None if match is None else match // a
    finite = [x for x in (n_length, n_content) if x is not None]
    return min(finite) if finite else None


def pumping_bound(actions: Sequence[Action], initial: str) -> int:
    read, written, _, _ = trace_data(actions)
    a, b = len(read), len(written)
    if a == 0 or b < a:
        raise ValueError("the pumping bound assumes 0 < total read <= total write")
    return (len(initial) + a + b - gcd(a, b) + a - 1) // a


def periodic_conjugacy(actions: Sequence[Action], initial: str) -> bool:
    """Finite-word characterization of an infinite closed macro run."""
    read, written, r, _ = trace_data(actions)
    a, b = len(read), len(written)
    if not actions or actions[0].source != actions[-1].target or not a:
        raise ValueError("requires a closed macro with nonempty read word")
    if len(initial) < r or b < a:
        return False
    d = gcd(a, b)
    return read * (b // d) + initial == initial + written * (a // d)


def binary_chain_length(exponent: int) -> int:
    """Number of word concatenations in left-to-right binary exponentiation."""
    if exponent < 1:
        raise ValueError("positive exponent required")
    return exponent.bit_length() + exponent.bit_count() - 2


def compile_infinite_certificate(nodes: Sequence[Node], initial: str,
                                 alphabet: str = "01") -> Certificate:
    """Unique quartic certificate that the root macro repeats indefinitely.

    The root must be a closed control path. No exponentiation predicate is used:
    the two fixed exponents from the conjugacy criterion are expanded into
    binary word-concatenation circuits. This does not decide arbitrary divergence.
    """
    cert = compile_certificate(nodes, initial, initial, alphabet)
    summary = cert.summaries[-1]
    if summary.source != summary.target:
        raise ValueError("infinite repetition requires a closed control path")
    lengths: list[tuple[int, int]] = []
    for node in nodes:
        if isinstance(node, Leaf):
            lengths.append((len(node.action.read), len(node.action.write)))
        else:
            x, y = lengths[node.left], lengths[node.right]
            lengths.append((x[0] + y[0], x[1] + y[1]))
    a, b = lengths[-1]
    if a == 0:
        return Certificate([], [], [], cert.summaries)
    if b < a:
        return Certificate([], [Poly({(): 1})], [], cert.summaries)
    # Keep all node equations, discard the finite endpoint equations/slack.
    del cert.residuals[-3:]
    cert.names.pop()
    cert.witness.pop()

    def named(name: str) -> Poly:
        return Poly.variable(cert.names.index(name))

    def fresh(name: str, value: int) -> Poly:
        p = Poly.variable(len(cert.names))
        cert.names.append(name)
        cert.witness.append(value)
        return p

    def word_power(base: tuple[Poly, Poly], numeric: tuple[int, int],
                   exponent: int, label: str) -> tuple[Poly, Poly]:
        pair, number = base, numeric
        gate = 0

        def cat(left: tuple[Poly, Poly], right: tuple[Poly, Poly],
                x: tuple[int, int], y: tuple[int, int]) -> tuple[tuple[Poly, Poly], tuple[int, int]]:
            nonlocal gate
            pval, cval = x[0] * y[0], x[1] * y[0] + y[1]
            p = fresh(f"{label}_{gate}_P", pval)
            c = fresh(f"{label}_{gate}_C", cval)
            gate += 1
            cert.residuals.extend((p-left[0]*right[0], c-left[1]*right[0]-right[1]))
            return (p, c), (pval, cval)

        for bit in bin(exponent)[3:]:
            pair, number = cat(pair, pair, number, number)
            if bit == "1":
                pair, number = cat(pair, base, number, numeric)
        return pair

    prefix = f"n{len(nodes)-1}_"
    pu, cu, pv, cv, r = (named(prefix+x) for x in ("PU", "CU", "PV", "CV", "R"))
    d = gcd(a, b)
    read_power = word_power((pu, cu), (summary.pu, summary.cu), b//d, "repeat_read")
    write_power = word_power((pv, cv), (summary.pv, summary.cv), a//d, "repeat_write")
    pq, cq = encode(initial, alphabet)
    slack = fresh("infinite_root_slack", max(0, len(initial)-summary.r))
    cert.residuals.extend((read_power[0]*pq-pq*write_power[0],
                          read_power[1]*pq+cq-cq*write_power[0]-write_power[1],
                          len(initial)-r-slack))
    return cert
