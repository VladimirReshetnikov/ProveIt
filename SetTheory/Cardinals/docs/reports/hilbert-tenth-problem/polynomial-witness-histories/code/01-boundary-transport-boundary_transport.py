"""Exact linear boundary-transport compiler (Python 3.10+, standard library).

Coordinates of a polynomial monomial are (X exponent, Y exponent, Z exponent).
Instruction TEST means: decrement and take `target` when positive; take `zero`
without decrement when zero. HALT configurations are included in certificates.
All polynomial witnesses have finite support. No truncation may discard spill rows.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Mapping, TypeAlias

Coeff: TypeAlias = int | Fraction
Exp: TypeAlias = tuple[int, int, int]
Poly: TypeAlias = dict[Exp, Coeff]
Config: TypeAlias = tuple[int, int, int]
Node: TypeAlias = tuple[int, int, int, int]  # state, X, Y, time


def clean(p: Mapping[Exp, Coeff], modulus: int | None = None) -> Poly:
    if modulus is not None and (type(modulus) is not int or modulus < 2):
        raise ValueError('modulus must be an integer at least 2')
    out: Poly = {}
    for e, c in p.items():
        if len(e) != 3 or any(type(n) is not int or n < 0 for n in e):
            raise ValueError('exponents must be three nonnegative integers')
        if not isinstance(c, (int, Fraction)):
            raise TypeError('only integer or exact Fraction coefficients are supported')
        if modulus is not None:
            if Fraction(c).denominator != 1:
                raise ValueError('modular coefficients must be integral')
            c = int(c) % modulus
        if c:
            out[e] = c
    return out


def add(*terms: Mapping[Exp, Coeff], modulus: int | None = None) -> Poly:
    out: Poly = {}
    for p in terms:
        for e, c in p.items():
            out[e] = out.get(e, 0) + c
    return clean(out, modulus)


def shift(p: Mapping[Exp, Coeff], e: Exp = (0, 0, 0), c: Coeff = 1,
          modulus: int | None = None) -> Poly:
    if len(e) != 3 or any(type(n) is not int or n < 0 for n in e):
        raise ValueError('shift must have three nonnegative integral exponents')
    return clean({tuple(a+b for a, b in zip(k, e)): c*v
                  for k, v in clean(p).items()}, modulus)


def mul(p: Mapping[Exp, Coeff], q: Mapping[Exp, Coeff],
        modulus: int | None = None) -> Poly:
    out: Poly = {}
    pp, qq = clean(p), clean(q)
    for e, a in pp.items():
        for f, b in qq.items():
            k = tuple(x+y for x, y in zip(e, f))
            out[k] = out.get(k, 0) + a*b
    return clean(out, modulus)


def split(p: Mapping[Exp, Coeff], counter: int) -> tuple[Poly, Poly]:
    """Return (D_counter p, P_counter p); p = X_counter*D + P."""
    if type(counter) is not int or counter not in (0, 1):
        raise ValueError('counter must be 0 or 1')
    d: Poly = {}; b: Poly = {}
    for e, c in clean(p).items():
        if e[counter] == 0:
            b[e] = c
        else:
            v = list(e); v[counter] -= 1
            d[tuple(v)] = c
    return d, b


@dataclass(frozen=True)
class Instruction:
    op: str
    counter: int = 0
    target: int = 0
    zero: int = 0


@dataclass(frozen=True)
class Program:
    instructions: tuple[Instruction, ...]

    def __post_init__(self) -> None:
        # Copy callers' sequences: a frozen dataclass must not retain a mutable list.
        object.__setattr__(self, 'instructions', tuple(self.instructions))
        if not self.instructions:
            raise ValueError('program must contain at least one state')
        for ins in self.instructions:
            if not isinstance(ins, Instruction):
                raise TypeError('every program entry must be an Instruction')
            if ins.op not in ('INC', 'TEST', 'HALT'):
                raise ValueError(f'unknown instruction: {ins.op}')
            if ins.op != 'HALT':
                if type(ins.counter) is not int or ins.counter not in (0, 1):
                    raise ValueError('counter must be 0 or 1')
                if type(ins.target) is not int or not 0 <= ins.target < len(self.instructions):
                    raise ValueError('invalid target')
                if ins.op == 'TEST' and (type(ins.zero) is not int or
                                         not 0 <= ins.zero < len(self.instructions)):
                    raise ValueError('invalid zero target')

    def validate_config(self, c: Config) -> None:
        if len(c) != 3 or any(type(v) is not int for v in c):
            raise ValueError('configuration must consist of three integers')
        if not 0 <= c[0] < len(self.instructions) or min(c[1:]) < 0:
            raise ValueError('invalid configuration')

    def step(self, c: Config) -> Config | None:
        self.validate_config(c)
        q, a, b = c
        ins = self.instructions[q]
        if ins.op == 'HALT':
            return None
        counters = [a, b]
        if ins.op == 'INC':
            counters[ins.counter] += 1; q = ins.target
        elif counters[ins.counter]:
            counters[ins.counter] -= 1; q = ins.target
        else:
            q = ins.zero
        return q, counters[0], counters[1]

    def run(self, start: Config, max_steps: int) -> tuple[list[Config], bool]:
        """Return c_0,...,c_k, k<=max_steps, and whether c_k is HALT."""
        self.validate_config(start)
        if type(max_steps) is not int or max_steps < 0:
            raise ValueError('max_steps must be nonnegative')
        path = [start]
        for _ in range(max_steps):
            nxt = self.step(path[-1])
            if nxt is None:
                return path, True
            path.append(nxt)
        return path, self.step(path[-1]) is None

    def transport(self, v: list[Poly], modulus: int | None = None) -> list[Poly]:
        if len(v) != len(self.instructions):
            raise ValueError('incorrect state-vector length')
        out: list[Poly] = [{} for _ in v]
        for q, ins in enumerate(self.instructions):
            if ins.op == 'HALT':
                continue
            if ins.op == 'INC':
                e = [0, 0, 0]; e[ins.counter] = 1
                out[ins.target] = add(out[ins.target], shift(v[q], tuple(e)), modulus=modulus)
            else:
                d, b = split(v[q], ins.counter)
                out[ins.target] = add(out[ins.target], d, modulus=modulus)
                out[ins.zero] = add(out[ins.zero], b, modulus=modulus)
        return out


def history(program: Program, path: Iterable[Config], clocked: bool = True) -> list[Poly]:
    out: list[Poly] = [{} for _ in program.instructions]
    for t, c in enumerate(path):
        program.validate_config(c)
        q, a, b = c
        e = (a, b, t if clocked else 0)
        out[q][e] = out[q].get(e, 0) + 1
    return out


def residual(program: Program, start: Config, h: list[Poly],
             clocked: bool = True, modulus: int | None = None) -> list[Poly]:
    program.validate_config(start)
    u = program.transport(h, modulus)
    out = [add(p, shift(v, (0, 0, int(clocked)), -1), modulus=modulus)
           for p, v in zip(h, u)]
    q, a, b = start
    out[q] = add(out[q], {(a, b, 0): -1}, modulus=modulus)
    return out


def energy(program: Program, start: Config, h: list[Poly]) -> Coeff:
    return sum(c*c for p in residual(program, start, h) for c in p.values())


@dataclass
class LinearSystem:
    program: Program
    start: Config
    sorts: dict[str, frozenset[int]]
    rows: list[dict[str, Poly]]
    rhs: list[Poly]
    clocked: bool

    def witness(self, h: list[Poly]) -> dict[str, Poly]:
        if len(h) != len(self.program.instructions):
            raise ValueError('incorrect state-vector length')
        w = {f'H{q}': clean(p) for q, p in enumerate(h)}
        for q, ins in enumerate(self.program.instructions):
            if ins.op == 'TEST':
                w[f'D{q}'], w[f'B{q}'] = split(h[q], ins.counter)
        return w

    def evaluate(self, witness: Mapping[str, Poly], modulus: int | None = None,
                 enforce_sorts: bool = True) -> list[Poly]:
        if set(witness) != set(self.sorts):
            raise ValueError('witness variable names differ from the system')
        w = {k: clean(v, modulus) for k, v in witness.items()}
        if enforce_sorts:
            for var, p in w.items():
                for e in p:
                    if any(e[j] and j not in self.sorts[var] for j in range(3)):
                        raise ValueError(f'{var} violates its polynomial subring sort')
        out = []
        for row, rhs in zip(self.rows, self.rhs):
            terms = [mul(coef, w[var], modulus) for var, coef in row.items()]
            out.append(add(*terms, shift(rhs, c=-1), modulus=modulus))
        return out

    def accepts(self, witness: Mapping[str, Poly], modulus: int | None = None) -> bool:
        return not any(self.evaluate(witness, modulus))

    def tagged_equation(self) -> str:
        """Exact one-equation rendering; every witness is independent of W."""
        pieces = []
        for j, (row, rhs) in enumerate(zip(self.rows, self.rhs)):
            expr = ' + '.join(f'({poly_text(p)})*{v}' for v, p in row.items())
            expr += f' - ({poly_text(rhs)})'
            pieces.append(f'W^{j}*({expr})')
        return ' +\n'.join(pieces) + ' = 0\n'


def compile_system(program: Program, start: Config, clocked: bool = True) -> LinearSystem:
    program.validate_config(start)
    n = len(program.instructions)
    base = frozenset((0, 1, 2) if clocked else (0, 1))
    sorts = {f'H{q}': base for q in range(n)}
    rows: list[dict[str, Poly]] = [{f'H{q}': {(0, 0, 0): 1}} for q in range(n)]
    rhs: list[Poly] = [{} for _ in range(n)]
    q0, a, b = start; rhs[q0] = {(a, b, 0): 1}
    z = (0, 0, int(clocked))

    def put(row: int, var: str, coefficient: Poly) -> None:
        rows[row][var] = add(rows[row].get(var, {}), coefficient)

    for q, ins in enumerate(program.instructions):
        if ins.op == 'HALT':
            continue
        if ins.op == 'INC':
            e = list(z); e[ins.counter] += 1
            put(ins.target, f'H{q}', {tuple(e): -1})
        else:
            sorts[f'D{q}'] = base
            sorts[f'B{q}'] = base - {ins.counter}
            put(ins.target, f'D{q}', {z: -1})
            put(ins.zero, f'B{q}', {z: -1})
            e = [0, 0, 0]; e[ins.counter] = 1
            rows.append({f'H{q}': {(0, 0, 0): 1},
                         f'D{q}': {tuple(e): -1}, f'B{q}': {(0, 0, 0): -1}})
            rhs.append({})
    return LinearSystem(program, start, sorts, rows, rhs, clocked)


def gf2_bounded_solve(program: Program, start: Config, amax: int, bmax: int, tmax: int
                      ) -> tuple[int, int, bool]:
    """Independent finite-box incidence-matrix solver over F_2.

    Returns (column rank, number of columns, consistency). Output rows include
    successors OUTSIDE the box, preventing a false certificate at its boundary.
    """
    program.validate_config(start)
    if any(type(n) is not int or n < 0 for n in (amax, bmax, tmax)):
        raise ValueError('box bounds must be nonnegative integers')
    nodes: list[Node] = [(q, a, b, t) for q in range(len(program.instructions))
                        for a in range(amax+1) for b in range(bmax+1)
                        for t in range(tmax+1)]
    m = len(nodes); equations: dict[Node, int] = {}
    for j, node in enumerate(nodes):
        equations[node] = equations.get(node, 0) ^ (1 << j)
        nxt = program.step(node[:3])
        if nxt is not None:
            out = (*nxt, node[3]+1)
            equations[out] = equations.get(out, 0) ^ (1 << j)
    source = (*start, 0)
    equations[source] = equations.get(source, 0) ^ (1 << m)
    pivots: dict[int, int] = {}; mask = (1 << m)-1
    inconsistent = False
    for row in equations.values():
        while row & mask:
            p = (row & mask).bit_length()-1
            if p in pivots:
                row ^= pivots[p]
            else:
                pivots[p] = row
                break
        else:
            if row >> m:
                inconsistent = True
    return len(pivots), m, not inconsistent


def poly_text(p: Mapping[Exp, Coeff]) -> str:
    if not p:
        return '0'
    terms = []
    for ex, c in sorted(p.items(), key=lambda kv: (kv[0][2], kv[0][0], kv[0][1])):
        mon = '*'.join(v if n == 1 else f'{v}^{n}'
                       for v, n in zip(('X', 'Y', 'Z'), ex) if n)
        terms.append(str(c) if not mon else f'{c}*{mon}')
    return ' + '.join(terms).replace('+ -', '- ')


TRANSFER = Program((Instruction('TEST', 0, 1, 2), Instruction('INC', 1, 0),
                    Instruction('HALT')))
FALSE_BOUNDARY = Program((Instruction('TEST', 0, 1, 2), Instruction('INC', 0, 0),
                          Instruction('HALT')))

if __name__ == '__main__':
    start = (0, 2, 0)
    path, halted = TRANSFER.run(start, 100)
    system = compile_system(TRANSFER, start)
    w = system.witness(history(TRANSFER, path))
    assert halted and system.accepts(w)
    print(system.tagged_equation())
    for var, p in w.items():
        print(f'{var} = {poly_text(p)}')
