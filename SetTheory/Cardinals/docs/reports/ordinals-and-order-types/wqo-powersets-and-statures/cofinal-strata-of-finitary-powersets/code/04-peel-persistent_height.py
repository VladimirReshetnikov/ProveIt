"""Exact heights of finite persistent-coordinate systems and ordinal lex sums.

Run: python code/persistent_height.py examples/weighted_N.json
The implementation is not a proof assistant. The accompanying article proves
its formulas for arbitrary set ordinals; this notation engine covers epsilon_0.
"""
from __future__ import annotations
import argparse
import json
import itertools
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Any
from ordinals import Ordinal, ZERO, ONE


def bits(mask: int) -> Iterable[int]:
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask ^= b


def closure(n: int, edges: Iterable[tuple[int, int]]) -> list[int]:
    """Reflexive transitive closure; reject out-of-range labels and cycles."""
    if type(n) is not int or n < 0:
        raise ValueError('n must be a nonnegative integer')
    le = [1 << i for i in range(n)]
    for i, j in edges:
        if type(i) is not int or type(j) is not int or not (0 <= i < n and 0 <= j < n):
            raise ValueError('Edge endpoint outside 0,...,n-1')
        if i == j:
            raise ValueError('Supply strict edges only')
        le[i] |= 1 << j
    for k in range(n):
        for i in range(n):
            if le[i] >> k & 1:
                le[i] |= le[k]
    for i in range(n):
        for j in bits(le[i] & ~(1 << i)):
            if le[j] >> i & 1:
                raise ValueError('The relation contains a cycle')
    return le


def topological(le: list[int]) -> list[int]:
    # Number of predecessors strictly increases along a strict comparison.
    return sorted(range(len(le)), key=lambda j: (sum(row >> j & 1 for row in le), j))


def antichains(le: list[int], maximal: bool = False) -> list[int]:
    n = len(le)
    result = []
    for mask in range(1 << n):
        if any(le[i] & mask != 1 << i for i in bits(mask)):
            continue
        if maximal:
            comparable = 0
            for i in bits(mask):
                comparable |= le[i]
                comparable |= sum(1 << j for j in range(n) if le[j] >> i & 1)
            if comparable != (1 << n) - 1:
                continue
        result.append(mask)
    return result


def hoare_states(le: list[int], fronts: list[int]) -> list[int]:
    return [sum(1 << j for j, b in enumerate(fronts)
                if all(le[q] & b for q in bits(a))) for a in fronts]


@dataclass
class System:
    le: list[int]
    active: list[int]
    capacities: dict[int, Ordinal]

    def validate(self, pure: bool = True) -> None:
        n = len(self.le)
        if len(self.active) != n:
            raise ValueError('One active-label mask per state is required')
        if any(type(a) is not int or a < 0 for a in self.active):
            raise ValueError('Active-label masks must be nonnegative integers')
        if any(type(row) is not int or row < 0 or row >> n for row in self.le):
            raise ValueError('Invalid relation bit mask')
        for i, row in enumerate(self.le):
            if not row >> i & 1:
                raise ValueError('State relation must be reflexive')
            for j in bits(row):
                if self.le[j] & ~row:
                    raise ValueError('State relation must be transitive')
                if i != j and self.le[j] >> i & 1:
                    raise ValueError('State relation must be antisymmetric')
                # For i <= j <= k, endpoint labels must occur at j.
                for k in bits(self.le[j]):
                    if self.active[i] & self.active[k] & ~self.active[j]:
                        raise ValueError('No-resurrection condition is violated')
        for mask in self.active:
            for q in bits(mask):
                a = self.capacities.get(q)
                if a is None or not a:
                    raise ValueError('Each active capacity must be a nonzero ordinal')
                if pure and (len(a.terms) != 1 or a.terms[0][1] != 1 or not a.terms[0][0]):
                    raise ValueError('Each active capacity must be omega^rho with rho > 0')

    def edge(self, i: int, j: int) -> Ordinal:
        return max([ONE] + [self.capacities[q] for q in bits(self.active[i] & ~self.active[j])])

    def terminal(self, i: int) -> Ordinal:
        return max([ONE] + [self.capacities[q] for q in bits(self.active[i])])

    def height_dp(self, validate: bool = True) -> tuple[Ordinal, list[int]]:
        if validate:
            self.validate()
        n = len(self.le)
        if n == 0:
            return ZERO, []
        best = [ZERO] * n
        path = [[i] for i in range(n)]
        for j in topological(self.le):
            for i in range(n):
                if i == j or not self.le[i] >> j & 1:
                    continue
                candidate = best[i] + self.edge(i, j)
                if candidate > best[j]:
                    best[j], path[j] = candidate, path[i] + [j]
        j = max(range(n), key=lambda k: best[k] + self.terminal(k))
        return best[j] + self.terminal(j), path[j]

    def height_peeling(self) -> tuple[Ordinal, list[dict[str, Any]]]:
        """Independent leading-exponent recurrence, not a call to height_dp."""
        def recurse(states: list[int]) -> tuple[Ordinal, list[dict[str, Any]]]:
            if not states:
                return ZERO, []
            labels = set(q for i in states for q in bits(self.active[i]))
            if not labels:
                d = {i: 1 for i in states}
                for j in topological(self.le):
                    if j in d:
                        d[j] = max([1] + [d[i] + 1 for i in states
                                          if i != j and self.le[i] >> j & 1])
                h = max(d.values())
                return Ordinal.nat(h), [{'finite_height': h, 'states': states}]
            lam = max(self.capacities[q] for q in labels)
            high = sum(1 << q for q in labels if self.capacities[q] == lam)
            d = {i: 0 for i in states}
            for j in topological(self.le):
                if j in d:
                    d[j] = max([0] + [d[i] + bool(self.active[i] & ~self.active[j] & high)
                                      for i in states if i != j and self.le[i] >> j & 1])
            c = max(d[i] + bool(self.active[i] & high) for i in states)
            tail = [i for i in states if d[i] == c]
            rest, certificate = recurse(tail)
            record = {'capacity': str(lam), 'coefficient': c, 'states': states,
                      'departure_counts': d, 'tail_states': tail}
            return lam.right_times(c) + rest, [record] + certificate
        return recurse(list(range(len(self.le))))

    def path_score(self, path: list[int]) -> Ordinal:
        if not path:
            return ZERO
        result = ZERO
        for i, j in zip(path, path[1:]):
            if i == j or not self.le[i] >> j & 1:
                raise ValueError('Certificate is not a strict state chain')
            result = result + self.edge(i, j)
        return result + self.terminal(path[-1])

    def height_exhaustive(self) -> Ordinal:
        """Independent enumeration of every nonempty strict state chain."""
        best = ZERO
        def visit(i: int, prefix: Ordinal) -> None:
            nonlocal best
            best = max(best, prefix + self.terminal(i))
            for j in bits(self.le[i] & ~(1 << i)):
                visit(j, prefix + self.edge(i, j))
        for i in range(len(self.le)):
            visit(i, ZERO)
        return best


def pure_frontier_system(le: list[int], capacities: list[Ordinal]) -> tuple[System, list[int]]:
    if not le:
        raise ValueError('Use the general construction for the empty skeleton')
    if len(capacities) != len(le):
        raise ValueError('Wrong number of capacities')
    fronts = antichains(le, maximal=True)
    return System(hoare_states(le, fronts), fronts, dict(enumerate(capacities))), fronts


def general_ordinal_system(le: list[int], fibers: list[Ordinal],
                           max_blocks: int = 18) -> tuple[System, list[int], list[dict[str, Any]]]:
    """CNF expansion, then ALL antichains (including the empty one).

    The default expansion guard avoids accidentally enumerating an enormous
    antichain space. Raise it explicitly only after considering 2^block_count.
    """
    if len(le) != len(fibers):
        raise ValueError('One ordinal per skeleton vertex is required')
    block_count = sum(c for a in fibers for _, c in a.terms)
    if block_count > max_blocks:
        raise ValueError(f'{block_count} expanded blocks exceed guard {max_blocks}')
    blocks = []
    for q, a in enumerate(fibers):
        for exponent, coefficient in a.terms:
            for _ in range(coefficient):
                blocks.append({'owner': q, 'exponent': exponent})
    n = len(blocks)
    edges = []
    for i, b in enumerate(blocks):
        for j, c in enumerate(blocks):
            if (b['owner'] == c['owner'] and i < j or
                b['owner'] != c['owner'] and le[b['owner']] >> c['owner'] & 1):
                edges.append((i, j))
    expanded_le = closure(n, edges)
    fronts = antichains(expanded_le)
    caps = {i: Ordinal.power(b['exponent']) for i, b in enumerate(blocks) if b['exponent']}
    infinite_mask = sum(1 << i for i in caps)
    system = System(hoare_states(expanded_le, fronts), [f & infinite_mask for f in fronts], caps)
    return system, fronts, blocks


def refine_capacities(system: System, max_states: int = 4096) -> tuple[System, list[dict[str, Any]]]:
    """Exact CNF-phase refinement of arbitrary nonzero coordinate capacities.

    A refined state remembers a CNF block for every currently active original
    label. Positive-exponent blocks become pure-coordinate labels; singleton
    blocks require no coordinate. This construction is an order isomorphism,
    unlike the height-only maximal-frontier compression of pure lex sums.
    """
    system.validate(pure=False)
    used = set(q for mask in system.active for q in bits(mask))
    phase_counts = {q: sum(c for _,c in system.capacities[q].terms) for q in used}
    count = sum(math.prod(phase_counts[q] for q in bits(mask)) for mask in system.active)
    if count > max_states:
        raise ValueError(f'{count} refined states exceed guard {max_states}')
    phases = {q: [e for e,c in system.capacities[q].terms for _ in range(c)] for q in used}
    metadata = []
    for i, mask in enumerate(system.active):
        labels = list(bits(mask))
        for choices in itertools.product(*(range(len(phases[q])) for q in labels)):
            metadata.append({'state': i, 'phase': dict(zip(labels, choices))})
    pure_id = {}
    caps = {}
    for q in sorted(used):
        for p, e in enumerate(phases[q]):
            if e:
                k = len(pure_id)
                pure_id[q,p] = k
                caps[k] = Ordinal.power(e)
    active = [sum(1 << pure_id[q,p] for q,p in a['phase'].items() if (q,p) in pure_id)
              for a in metadata]
    le = []
    for a in metadata:
        row = 0
        for j,b in enumerate(metadata):
            if (system.le[a['state']] >> b['state'] & 1 and
                all(p <= b['phase'][q] for q,p in a['phase'].items() if q in b['phase'])):
                row |= 1 << j
        le.append(row)
    refined = System(le, active, caps)
    # The theorem proves no-resurrection for the refinement. Public callers
    # can invoke refined.validate() for a complete, more expensive check.
    return refined, metadata


def exact_point_rank(system: System, state: int, coordinates: dict[int, Ordinal],
                     max_states: int = 4096) -> Ordinal:
    """Compute the exact rank of a point of an exact persistent model.

    Restrict to its inclusive principal ideal, cap shared coordinates at x+1,
    refine CNF phases, compute the (necessarily successor) height and remove
    the final 1. Do not apply a height-only compressed model to point ranks.
    """
    system.validate(pure=False)
    if not 0 <= state < len(system.le):
        raise ValueError('Unknown state')
    if set(coordinates) != set(bits(system.active[state])):
        raise ValueError('Supply precisely the active coordinates of this state')
    if any(not isinstance(x, Ordinal) or not x < system.capacities[q]
           for q,x in coordinates.items()):
        raise ValueError('Point coordinate is outside its capacity')
    states = [i for i in range(len(system.le)) if system.le[i] >> state & 1]
    le = [sum(1 << j for j,k in enumerate(states) if system.le[i] >> k & 1) for i in states]
    caps = dict(system.capacities)
    for q,x in coordinates.items():
        caps[q] = x + ONE
    ideal = System(le, [system.active[i] for i in states], caps)
    refined,_ = refine_capacities(ideal, max_states)
    height,_ = refined.height_dp(validate=False)
    if not height.terms or height.terms[-1][0] != ZERO:
        raise AssertionError('A principal ideal must have successor height')
    coefficient = height.terms[-1][1]
    terms = list(height.terms[:-1])
    if coefficient > 1:
        terms.append((ZERO,coefficient-1))
    return Ordinal(tuple(terms))


def solve(data: dict[str, Any]) -> dict[str, Any]:
    n = data['n']
    le = closure(n, [tuple(e) for e in data.get('edges', [])])
    fibers = [Ordinal.parse(a) for a in data['fibers']]
    mode = data.get('mode', 'general')
    if mode == 'pure':
        system, fronts = pure_frontier_system(le, fibers)
        blocks = []
    elif mode == 'general':
        system, fronts, blocks = general_ordinal_system(le, fibers, data.get('max_blocks', 18))
    else:
        raise ValueError('mode must be pure or general')
    height, path = system.height_dp()
    independent, peeling = system.height_peeling()
    if height != independent or system.path_score(path) != height:
        raise AssertionError('The two algorithms or the witness disagree')
    return {'height': str(height), 'height_cnf': height.json(),
            'state_count': len(fronts), 'expanded_blocks': len(blocks) if mode == 'general' else None,
            'witness_state_ids': path, 'witness_frontiers': [list(bits(fronts[i])) for i in path],
            'witness_weights': [str(system.edge(i,j)) for i,j in zip(path,path[1:])] +
                               ([str(system.terminal(path[-1]))] if path else []),
            'peeling_certificate': peeling}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        result = solve(json.loads(args.input.read_text(encoding='utf-8')))
    except (ValueError, TypeError, KeyError, OSError) as error:
        parser.error(str(error))
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    else:
        print(text, end='')

if __name__ == '__main__':
    main()
