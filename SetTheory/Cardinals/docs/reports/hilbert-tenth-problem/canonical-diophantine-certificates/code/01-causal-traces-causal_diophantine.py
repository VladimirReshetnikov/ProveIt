#!/usr/bin/env python3
"""Exact, witness-canonical Diophantine compilers for guarded translations.

Python 3.10+, standard library only.  All variables range over NONNEGATIVE
integers; residual polynomials are evaluated over the integers.  A system
represents the single polynomial sum(residual**2).  No modular arithmetic,
relaxed inequalities, floating point arithmetic, or polynomial solver is used.

This is an executable reference implementation, not a machine-checked proof.
See the accompanying article for the correctness and uniqueness proofs.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from itertools import combinations
import json
from pathlib import Path
from typing import Iterable, Mapping, Optional, Sequence


@dataclass(frozen=True)
class Action:
    name: str
    lower: tuple[int, ...]
    delta: tuple[int, ...]
    upper: tuple[Optional[int], ...]  # None = +infinity

    def __post_init__(self) -> None:
        p = len(self.lower)
        if not p or len(self.delta) != p or len(self.upper) != p:
            raise ValueError('Action vectors must have the same positive dimension')
        for lo, v, hi in zip(self.lower, self.delta, self.upper):
            if not isinstance(lo, int) or not isinstance(v, int):
                raise TypeError('Guards and displacements must be integers')
            if lo < max(0, -v):
                raise ValueError('Lower guard must ensure nonnegative outputs')
            if hi is not None and (not isinstance(hi, int) or hi < lo):
                raise ValueError('A finite upper guard must be >= lower guard')

    @property
    def p(self) -> int:
        return len(self.lower)

    def apply(self, x: Sequence[int]) -> Optional[tuple[int, ...]]:
        if len(x) != self.p or any(not isinstance(t, int) or t < 0 for t in x):
            raise ValueError('State must be a nonnegative integer vector')
        if any(t < lo or (hi is not None and t > hi)
               for t, lo, hi in zip(x, self.lower, self.upper)):
            return None
        return tuple(t + v for t, v in zip(x, self.delta))

    @classmethod
    def petri(cls, name: str, consume: Sequence[int], produce: Sequence[int]) -> Action:
        if len(consume) != len(produce) or any(t < 0 for t in (*consume, *produce)):
            raise ValueError('Petri input/output vectors must be nonnegative')
        return cls(name, tuple(consume), tuple(b-a for a, b in zip(consume, produce)),
                   (None,) * len(consume))


def validate_actions(actions: Sequence[Action]) -> tuple[Action, ...]:
    a = tuple(actions)
    if not a or any(t.p != a[0].p for t in a):
        raise ValueError('Need a nonempty action alphabet of one dimension')
    if len({t.name for t in a}) != len(a):
        raise ValueError('Action names must be distinct')
    return a


def composition_box(a: Action, b: Action):
    """Domain box of 'first a, then b'; None means the empty domain."""
    if a.p != b.p:
        raise ValueError('Dimension mismatch')
    lower, upper = [], []
    for la, lb, va, ua, ub in zip(a.lower, b.lower, a.delta, a.upper, b.upper):
        lo = max(la, lb - va)
        candidates = [t for t in (ua, None if ub is None else ub-va) if t is not None]
        hi = min(candidates) if candidates else None
        if hi is not None and lo > hi:
            return None
        lower.append(lo)
        upper.append(hi)
    return tuple(lower), tuple(upper)


def commute(a: Action, b: Action) -> bool:
    return composition_box(a, b) == composition_box(b, a)


def independence(actions: Sequence[Action]) -> frozenset[tuple[int, int]]:
    a = validate_actions(actions)
    return frozenset((i, j) for i, j in combinations(range(len(a)), 2)
                     if commute(a[i], a[j]))


def check_independence(actions: Sequence[Action], pairs=None) -> frozenset[tuple[int, int]]:
    allowed = independence(actions)
    if pairs is None:
        return allowed
    normalized = frozenset((min(i, j), max(i, j)) for i, j in pairs)
    if any(i == j for i, j in normalized) or not normalized <= allowed:
        raise ValueError('Independence must be an irreflexive subrelation of commutation')
    return normalized


def independent(i: int, j: int, pairs) -> bool:
    return i != j and (min(i, j), max(i, j)) in pairs


def execute(actions: Sequence[Action], x: Sequence[int], word: Sequence[int]):
    state = tuple(x)
    for a in word:
        nxt = actions[a].apply(state)
        if nxt is None:
            return None
        state = nxt
    return state


def envelope(actions: Sequence[Action], counts: Sequence[int]):
    """Domain where EVERY serialization of a multiset is executable.

    This formula does not require commutation. Under pairwise commutation
    of the active actions it is also the domain where SOME serialization works.
    """
    actions = validate_actions(actions)
    if len(counts) != len(actions) or any(not isinstance(n, int) or n < 0 for n in counts):
        raise ValueError('Multiplicities must be nonnegative integers')
    active = [a for a, n in zip(actions, counts) if n]
    p = actions[0].p
    loss = tuple(sum(n * max(-a.delta[j], 0) for a, n in zip(actions, counts))
                 for j in range(p))
    gain = tuple(sum(n * max(a.delta[j], 0) for a, n in zip(actions, counts))
                 for j in range(p))
    lower = tuple(loss[j] + max((a.lower[j]-max(-a.delta[j], 0) for a in active), default=0)
                  for j in range(p))
    upper = []
    for j in range(p):
        caps = [a.upper[j] + max(a.delta[j], 0) - gain[j]
                for a in active if a.upper[j] is not None]
        upper.append(min(caps) if caps else None)
    return lower, tuple(upper), loss, gain


def envelope_apply(actions: Sequence[Action], x: Sequence[int], counts: Sequence[int]):
    lo, hi, loss, gain = envelope(actions, counts)
    if len(x) != len(lo) or any(not isinstance(t, int) or t < 0 for t in x):
        raise ValueError('Invalid natural state')
    if any(t < l or (u is not None and t > u) for t, l, u in zip(x, lo, hi)):
        return None
    return tuple(t-l+g for t, l, g in zip(x, loss, gain))


def foata(word: Sequence[int], pairs) -> tuple[tuple[int, ...], ...]:
    """Cartier--Foata layers, sorted within each layer."""
    layers: list[list[int]] = []
    prior: list[tuple[int, int]] = []
    for a in word:
        level = 1 + max((h for b, h in prior if not independent(a, b, pairs)), default=0)
        while len(layers) < level:
            layers.append([])
        layers[level-1].append(a)
        prior.append((a, level))
    return tuple(tuple(sorted(c)) for c in layers)


def canonical_layers(layers: Sequence[Sequence[int]], m: int, pairs) -> bool:
    previous = None
    for layer in layers:
        c = tuple(layer)
        if len(set(c)) != len(c) or any(a < 0 or a >= m for a in c):
            return False
        if any(not independent(a, b, pairs) for a, b in combinations(c, 2)):
            return False
        if previous is not None and any(
                not any(not independent(a, b, pairs) for b in previous) for a in c):
            return False
        previous = c
    return True


@dataclass
class Poly:
    # Monomials are sorted tuples with repeated variable names, e.g. ('x','x','y').
    terms: dict[tuple[str, ...], int] = field(default_factory=dict)

    def __post_init__(self):
        merged = {}
        for k, v in self.terms.items():
            mon = tuple(sorted(k))
            merged[mon] = merged.get(mon, 0) + int(v)
        self.terms = {k: v for k, v in merged.items() if v}

    @staticmethod
    def cast(value):
        if isinstance(value, Poly):
            return value
        if isinstance(value, int):
            return Poly({(): value})
        raise TypeError(f'Not a polynomial or integer: {type(value).__name__}')

    def __add__(self, other):
        other = Poly.cast(other)
        out = self.terms.copy()
        for k, v in other.terms.items():
            out[k] = out.get(k, 0) + v
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -Poly.cast(other)

    def __rsub__(self, other):
        return Poly.cast(other) + -self

    def __mul__(self, other):
        other = Poly.cast(other)
        out = {}
        for k, v in self.terms.items():
            for l, w in other.terms.items():
                mon = tuple(sorted(k+l))
                out[mon] = out.get(mon, 0) + v*w
        return Poly(out)

    __rmul__ = __mul__

    @property
    def degree(self):
        return max(map(len, self.terms), default=0)

    def evaluate(self, assignment: Mapping[str, int]) -> int:
        total = 0
        for mon, coefficient in self.terms.items():
            term = coefficient
            for variable in mon:
                term *= assignment[variable]
            total += term
        return total

    def json_terms(self):
        return [{'coefficient': c, 'variables': list(mon)}
                for mon, c in sorted(self.terms.items(), key=lambda x: (len(x[0]), x[0]))]


def V(name: str) -> Poly:
    return Poly({(name,): 1})


@dataclass
class System:
    parameters: list[str] = field(default_factory=list)
    witnesses: list[str] = field(default_factory=list)
    residuals: list[tuple[str, Poly]] = field(default_factory=list)
    metadata: dict = field(default_factory=dict)

    def parameter(self, name):
        if name in self.parameters or name in self.witnesses:
            raise ValueError(f'Duplicate variable {name}')
        self.parameters.append(name)
        return V(name)

    def witness(self, name):
        if name in self.parameters or name in self.witnesses:
            raise ValueError(f'Duplicate variable {name}')
        self.witnesses.append(name)
        return V(name)

    def add(self, label: str, residual):
        residual = Poly.cast(residual)
        if residual.degree > 2:
            raise ValueError(f'Residual {label} exceeds degree two')
        self.residuals.append((label, residual))

    def check(self, assignment: Mapping[str, int]) -> bool:
        names = self.parameters + self.witnesses
        if set(assignment) != set(names):
            return False
        if any(not isinstance(assignment[v], int) or assignment[v] < 0 for v in names):
            return False
        return all(r.evaluate(assignment) == 0 for _, r in self.residuals)

    def value(self, assignment: Mapping[str, int]) -> int:
        return sum(r.evaluate(assignment)**2 for _, r in self.residuals)

    def expanded(self) -> Poly:
        return sum((r*r for _, r in self.residuals), Poly())

    def export(self, path: str | Path, assignment=None, expand=False) -> None:
        data = {'domain': 'nonnegative integers',
                'single_polynomial': 'sum of squares of all listed residuals',
                'metadata': self.metadata, 'parameters': self.parameters,
                'witnesses': self.witnesses,
                'residuals': [{'label': label, 'terms': r.json_terms()}
                              for label, r in self.residuals]}
        if assignment is not None:
            if not self.check(assignment):
                raise ValueError('Refusing to export an invalid certificate')
            data['valid_certificate'] = dict(assignment)
        if expand:
            data['expanded_polynomial'] = self.expanded().json_terms()
        Path(path).write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')


def compile_accelerator(actions: Sequence[Action]) -> System:
    """Compile universal-serialization relation; existential also if actions commute."""
    a = validate_actions(actions)
    m, p = len(a), a[0].p
    sys = System(metadata={'kind': 'all_serializations_accelerator',
                           'actions': [t.name for t in a],
                           'pairwise_commuting': len(independence(a)) == m*(m-1)//2})
    x = [sys.parameter(f'x_{j}') for j in range(p)]
    y = [sys.parameter(f'y_{j}') for j in range(p)]
    n = [sys.parameter(f'n_{i}') for i in range(m)]
    z = [sys.witness(f'z_{i}') for i in range(m)]
    k = [sys.witness(f'k_{i}') for i in range(m)]
    loss = [sys.witness(f'loss_{j}') for j in range(p)]
    gain = [sys.witness(f'gain_{j}') for j in range(p)]
    for i in range(m):
        sys.add(f'boolean_{i}', z[i]*(z[i]-1))
        sys.add(f'support_{i}', n[i]-z[i]*(1+k[i]))
        sys.add(f'inactive_count_{i}', (1-z[i])*k[i])
    for j in range(p):
        sys.add(f'loss_total_{j}', loss[j]-sum(max(-a[i].delta[j], 0)*n[i] for i in range(m)))
        sys.add(f'gain_total_{j}', gain[j]-sum(max(a[i].delta[j], 0)*n[i] for i in range(m)))
        sys.add(f'endpoint_{j}', y[j]+loss[j]-x[j]-gain[j])
        for i in range(m):
            r = a[i].lower[j]-max(-a[i].delta[j], 0)
            s = sys.witness(f'low_{i}_{j}')
            sys.add(f'lower_active_{i}_{j}', z[i]*(x[j]-loss[j]-r-s))
            sys.add(f'lower_inactive_{i}_{j}', (1-z[i])*s)
            if a[i].upper[j] is not None:
                cap = a[i].upper[j]+max(a[i].delta[j], 0)
                t = sys.witness(f'up_{i}_{j}')
                sys.add(f'upper_active_{i}_{j}', z[i]*(cap-gain[j]-x[j]-t))
                sys.add(f'upper_inactive_{i}_{j}', (1-z[i])*t)
    return sys


def complete_accelerator(actions: Sequence[Action], x: Sequence[int], counts: Sequence[int]):
    a = validate_actions(actions)
    y = envelope_apply(a, x, counts)
    if y is None:
        return None
    _, _, loss, gain = envelope(a, counts)
    ass = {f'x_{j}': t for j, t in enumerate(x)}
    ass.update({f'y_{j}': t for j, t in enumerate(y)})
    for i, n in enumerate(counts):
        ass[f'n_{i}'] = n
        ass[f'z_{i}'] = int(n > 0)
        ass[f'k_{i}'] = max(n-1, 0)
    for j in range(a[0].p):
        ass[f'loss_{j}'], ass[f'gain_{j}'] = loss[j], gain[j]
        for i, action in enumerate(a):
            r = action.lower[j]-max(-action.delta[j], 0)
            ass[f'low_{i}_{j}'] = x[j]-loss[j]-r if counts[i] else 0
            if action.upper[j] is not None:
                cap = action.upper[j]+max(action.delta[j], 0)
                ass[f'up_{i}_{j}'] = cap-gain[j]-x[j] if counts[i] else 0
    return ass


def compile_history(actions: Sequence[Action], height: int, pairs=None) -> System:
    a = validate_actions(actions)
    if not isinstance(height, int) or height < 0:
        raise ValueError('Height must be a nonnegative integer')
    pairs = check_independence(a, pairs)
    m, p, H = len(a), a[0].p, height
    dep = [[b for b in range(m) if not independent(i, b, pairs)] for i in range(m)]
    sys = System(metadata={'kind': 'canonical_trace_history', 'height_bound': H,
                           'actions': [t.name for t in a],
                           'independence': sorted(pairs)})
    x = [sys.parameter(f'x_{j}') for j in range(p)]
    y = [sys.parameter(f'y_{j}') for j in range(p)]
    if H == 0:
        for j in range(p):
            sys.add(f'empty_endpoint_{j}', y[j]-x[j])
        return sys
    state = [x] + [[sys.witness(f'state_{h}_{j}') for j in range(p)]
                    for h in range(1, H)] + [y]
    z = [[sys.witness(f'z_{h}_{i}') for i in range(m)] for h in range(H)]
    loss = [[sys.witness(f'loss_{h}_{j}') for j in range(p)] for h in range(H)]
    gain = [[sys.witness(f'gain_{h}_{j}') for j in range(p)] for h in range(H)]
    for h in range(H):
        for i in range(m):
            sys.add(f'boolean_{h}_{i}', z[h][i]*(z[h][i]-1))
        for i, j in combinations(range(m), 2):
            if not independent(i, j, pairs):
                sys.add(f'clique_{h}_{i}_{j}', z[h][i]*z[h][j])
        for j in range(p):
            sys.add(f'loss_total_{h}_{j}', loss[h][j]-sum(max(-a[i].delta[j], 0)*z[h][i] for i in range(m)))
            sys.add(f'gain_total_{h}_{j}', gain[h][j]-sum(max(a[i].delta[j], 0)*z[h][i] for i in range(m)))
            sys.add(f'endpoint_{h}_{j}', state[h+1][j]+loss[h][j]-state[h][j]-gain[h][j])
            for i in range(m):
                r = a[i].lower[j]-max(-a[i].delta[j], 0)
                s = sys.witness(f'low_{h}_{i}_{j}')
                sys.add(f'lower_active_{h}_{i}_{j}', z[h][i]*(state[h][j]-loss[h][j]-r-s))
                sys.add(f'lower_inactive_{h}_{i}_{j}', (1-z[h][i])*s)
                if a[i].upper[j] is not None:
                    cap = a[i].upper[j]+max(a[i].delta[j], 0)
                    t = sys.witness(f'up_{h}_{i}_{j}')
                    sys.add(f'upper_active_{h}_{i}_{j}', z[h][i]*(cap-gain[h][j]-state[h][j]-t))
                    sys.add(f'upper_inactive_{h}_{i}_{j}', (1-z[h][i])*t)
    for h in range(H-1):
        for i in range(m):
            previous = Poly.cast(1)
            for k, b in enumerate(dep[i]):
                u = sys.witness(f'block_{h}_{i}_{k}')
                sys.add(f'block_product_{h}_{i}_{k}', u-previous*(1-z[h][b]))
                previous = u
            sys.add(f'foata_{h}_{i}', z[h+1][i]*previous)
    return sys


def complete_history(actions: Sequence[Action], x: Sequence[int], layers: Sequence[Sequence[int]],
                     height: int, pairs=None):
    a = validate_actions(actions)
    pairs = check_independence(a, pairs)
    m, p, H = len(a), a[0].p, height
    if not isinstance(H, int) or H < 0 or len(layers) > H:
        raise ValueError('Invalid height bound')
    if len(x) != p or any(not isinstance(t, int) or t < 0 for t in x):
        raise ValueError('Invalid natural state')
    layers = [tuple(c) for c in layers] + [()] * (H-len(layers))
    if not canonical_layers(layers, m, pairs):
        return None
    ass = {f'x_{j}': t for j, t in enumerate(x)}
    state = tuple(x)
    if H == 0:
        ass.update({f'y_{j}': t for j, t in enumerate(x)})
        return ass
    for h, c in enumerate(layers):
        counts = [int(i in c) for i in range(m)]
        nxt = envelope_apply(a, state, counts)
        if nxt is None:
            return None
        _, _, loss, gain = envelope(a, counts)
        for i, v in enumerate(counts):
            ass[f'z_{h}_{i}'] = v
        for j in range(p):
            ass[f'loss_{h}_{j}'], ass[f'gain_{h}_{j}'] = loss[j], gain[j]
            for i, action in enumerate(a):
                r = action.lower[j]-max(-action.delta[j], 0)
                ass[f'low_{h}_{i}_{j}'] = state[j]-loss[j]-r if counts[i] else 0
                if action.upper[j] is not None:
                    cap = action.upper[j]+max(action.delta[j], 0)
                    ass[f'up_{h}_{i}_{j}'] = cap-gain[j]-state[j] if counts[i] else 0
        state = nxt
        if h+1 < H:
            ass.update({f'state_{h+1}_{j}': t for j, t in enumerate(state)})
    ass.update({f'y_{j}': t for j, t in enumerate(state)})
    for h in range(H-1):
        for i in range(m):
            prod = 1
            dep = [b for b in range(m) if not independent(i, b, pairs)]
            for k, b in enumerate(dep):
                prod *= 1-int(b in layers[h])
                ass[f'block_{h}_{i}_{k}'] = prod
    return ass


def compile_blocks(phases: Sequence[Sequence[Action]], existential_counts: bool = False) -> System:
    """Fixed ordered commuting phases, with arbitrary repetition in each phase.

    With counts as parameters, the fibre is empty or a singleton. With counts
    existential, roots correspond to legal phase count vectors; endpoint-level
    single/finite-foldness needs the additional conditions in the article.
    """
    phases = tuple(validate_actions(a) for a in phases)
    if not phases or any(a[0].p != phases[0][0].p for a in phases):
        raise ValueError('Need nonempty phases of the same state dimension')
    for a in phases:
        if len(independence(a)) != len(a)*(len(a)-1)//2:
            raise ValueError('Every phase alphabet must be pairwise commuting')
    p, b = phases[0][0].p, len(phases)
    sys = System(metadata={'kind': 'fixed_commuting_phases', 'phase_count': b,
                           'counts_existential': existential_counts})
    for j in range(p): sys.parameter(f'x_{j}')
    for j in range(p): sys.parameter(f'y_{j}')
    for s in range(1,b):
        for j in range(p): sys.witness(f'boundary_{s}_{j}')
    for s, actions in enumerate(phases):
        local = compile_accelerator(actions)
        rename = {}
        for j in range(p):
            rename[f'x_{j}'] = f'x_{j}' if s == 0 else f'boundary_{s}_{j}'
            rename[f'y_{j}'] = f'y_{j}' if s+1 == b else f'boundary_{s+1}_{j}'
        for i in range(len(actions)):
            name = f'phase_{s}_n_{i}'
            (sys.witness if existential_counts else sys.parameter)(name)
            rename[f'n_{i}'] = name
        for name in local.witnesses:
            rename[name] = f'phase_{s}_{name}'
            sys.witness(rename[name])
        for label, residual in local.residuals:
            out = Poly()
            for mon, c in residual.terms.items():
                out += Poly({tuple(sorted(rename[v] for v in mon)): c})
            sys.add(f'phase_{s}_{label}',out)
    return sys


def complete_blocks(phases: Sequence[Sequence[Action]], x: Sequence[int],
                    multiplicities: Sequence[Sequence[int]]):
    phases = tuple(validate_actions(a) for a in phases)
    if len(phases) != len(multiplicities):
        raise ValueError('One multiplicity vector is required per phase')
    # Validate dimensions and commutation via the public compiler contract.
    compile_blocks(phases)
    ass = {f'x_{j}':t for j,t in enumerate(x)}
    state = tuple(x)
    for s, (actions, ns) in enumerate(zip(phases,multiplicities)):
        local = complete_accelerator(actions,state,ns)
        if local is None: return None
        for name, value in local.items():
            if name.startswith('x_') or name.startswith('y_'): continue
            ass[f'phase_{s}_{name}'] = value
        state = tuple(local[f'y_{j}'] for j in range(actions[0].p))
        if s+1 < len(phases):
            ass.update({f'boundary_{s+1}_{j}':t for j,t in enumerate(state)})
    ass.update({f'y_{j}':t for j,t in enumerate(state)})
    return ass


def word_macro(actions: Sequence[Action], word: Sequence[int], name: str = 'macro'):
    """Exact guarded-translation macro for a fixed word; None for empty domain.

    An empty WORD yields the everywhere-defined identity action. No commutation
    of the letters is assumed, and the macro does not quotient distinct words.
    """
    actions=validate_actions(actions)
    p=actions[0].p
    macro=Action(name,(0,)*p,(0,)*p,(None,)*p)
    for index in word:
        if not isinstance(index,int) or not 0 <= index < len(actions):
            raise ValueError('Word contains an invalid action index')
        action=actions[index]
        box=composition_box(macro,action)
        if box is None: return None
        lo,hi=box
        macro=Action(name,lo,tuple(v+w for v,w in zip(macro.delta,action.delta)),hi)
    return macro


def compile_word_power(actions: Sequence[Action], word: Sequence[int]) -> System:
    """Single-fold ordinary quartic for executing a fixed word n_0 times."""
    actions=validate_actions(actions)
    macro=word_macro(actions,word)
    if macro is not None:
        sys=compile_accelerator([macro])
        sys.metadata.update({'kind':'fixed_word_power','fixed_word':list(word)})
        return sys
    sys=System(metadata={'kind':'fixed_word_power','empty_macro_domain':True})
    x=[sys.parameter(f'x_{j}') for j in range(actions[0].p)]
    y=[sys.parameter(f'y_{j}') for j in range(actions[0].p)]
    n=sys.parameter('n_0')
    sys.add('only_zero_repetitions',n)
    for j in range(actions[0].p): sys.add(f'identity_{j}',y[j]-x[j])
    return sys


def complete_word_power(actions: Sequence[Action], word: Sequence[int],
                        x: Sequence[int], repetitions: int):
    actions=validate_actions(actions)
    if not isinstance(repetitions,int) or repetitions<0:
        raise ValueError('Repetitions must be a nonnegative integer')
    if len(x)!=actions[0].p or any(not isinstance(t,int) or t<0 for t in x):
        raise ValueError('Invalid natural state')
    macro=word_macro(actions,word)
    if macro is not None: return complete_accelerator([macro],x,(repetitions,))
    if repetitions: return None
    ass={'n_0':0}
    ass.update({f'x_{j}':t for j,t in enumerate(x)})
    ass.update({f'y_{j}':t for j,t in enumerate(x)})
    return ass
