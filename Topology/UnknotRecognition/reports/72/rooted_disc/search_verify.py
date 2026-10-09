"""Independent complete finite-language replay, including negative answers.

Rebuilds every local option product using a BFS component graph rather than the
producer transition or search. The input remains an abstract patch language;
this is NOT completeness or source authentication for a knot diagram.
"""
from __future__ import annotations
from .kernel import State, Candidate
from .assembly import Grammar, Patch
from .verify import verify_reduction


def reference_transition(s: State, p: Patch) -> State:
    if s.r != p.incoming + 1 or s.q != p.q:
        raise ValueError('interface mismatch')
    offset = len(s.good)
    n = offset + len(p.good)
    adjacency = [[] for _ in range(n)]
    for i in range(p.incoming):
        a, b = s.partition[i + 1], offset + p.partition[i]
        adjacency[a].append(b); adjacency[b].append(a)
    component_of = [-1] * n
    attributes = []
    flags, charges = s.good + p.good, s.charges + p.charges
    for seed in range(n):
        if component_of[seed] >= 0:
            continue
        identifier = len(attributes)
        component = {seed}; pending = [seed]
        while pending:
            for v in adjacency[pending.pop()]:
                if v not in component:
                    component.add(v); pending.append(v)
        good = all(flags[v] for v in component) and sum(len(adjacency[v]) for v in component) == 2 * (len(component) - 1)
        charge = 0
        if good:
            for v in component:
                charge ^= charges[v]
        attributes.append((good, charge))
        for v in component:
            component_of[v] = identifier
    output = [component_of[s.partition[0]]] + [component_of[offset + p.partition[p.incoming + i]] for i in range(p.outgoing)]
    remap, partition, good, charges = {}, [], [], []
    for identifier in output:
        if identifier not in remap:
            remap[identifier] = len(remap)
            g, h = attributes[identifier]
            good.append(g); charges.append(h)
        partition.append(remap[identifier])
    return State(tuple(partition), tuple(good), tuple(charges), s.q)


def _dominant(candidates: list[Candidate]) -> dict[State, Candidate]:
    table = {}
    for c in candidates:
        if not c.state.good[0]:
            continue
        previous = table.get(c.state)
        if previous is None or (c.cost, c.witness) < (previous.cost, previous.witness):
            table[c.state] = c
    return table


def verify_search(grammar: Grammar, answer: dict, *, max_dimension: int = 2_000_000) -> bool:
    """Check complete option generation, every reduction, and the final verdict.

The checker accepts basis-search answers with all reduction records. It also
checks work/table counts, but not machine timing or optional mesh-report fields.
ResourceLimit from row replay deliberately propagates instead of returning False.
"""
    try:
        digest = grammar.digest()
        if answer['source_sha256'] != digest or len(answer['reductions']) != len(grammar.layers) + 1:
            return False
        family = [Candidate(c.state, c.cost, (i,)) for i, c in enumerate(grammar.initial)]
        work = peak_exact = peak_basis = 0
        for stage, record in enumerate(answer['reductions']):
            if stage:
                layer = grammar.layers[stage - 1]
                work += len(family) * len(layer)
                family = [Candidate(reference_transition(c.state, p), c.cost + p.cost, c.witness + (i,))
                          for c in family for i, p in enumerate(layer)]
            expected = _dominant(family)
            supplied = [Candidate(State.from_dict(x['state']), int(x['cost'], 16), tuple(x['witness']))
                        for x in record['candidates']]
            if len(supplied) != len(expected) or len({c.state for c in supplied}) != len(supplied):
                return False
            if any(expected.get(c.state) != c for c in supplied):
                return False
            key = f'{digest}:{grammar.geometry_key}:stage={stage}'
            cert = record['certificate']
            if not verify_reduction(supplied, cert, geometry_key=key, max_dimension=max_dimension):
                return False
            family = [supplied[i] for i in cert['kept']]
            peak_exact = max(peak_exact, len(supplied)); peak_basis = max(peak_basis, len(family))
        feasible = [c for c in family if c.state.good[0] and ((c.state.charges[0] != 0) if grammar.target is None else c.state.charges[0] == grammar.target)]
        best = min(feasible, key=lambda c: (c.cost, c.witness)) if feasible else None
        if best is None:
            valid = answer['status'] == 'NO_ROOTED_DISC_IN_LANGUAGE' and answer['cost'] is None and answer['witness'] is None
        else:
            valid = (answer['status'] == 'FOUND_ABSTRACT_ROOTED_DISC' and int(answer['cost'], 16) == best.cost
                     and answer['witness'] is not None and all(type(i) is int for i in answer['witness'])
                     and tuple(answer['witness']) == best.witness)
        return valid and answer['transitions'] == work and answer['peak_exact_table'] == peak_exact and answer['peak_retained'] == peak_basis
    except (ValueError, TypeError, KeyError, IndexError, AttributeError):
        return False
