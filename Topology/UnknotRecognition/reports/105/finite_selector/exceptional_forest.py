"""Exact bounded-interface forest selection; no manifold authenticity claims.

The new reduction enumerates partial partitions of exceptional-row targets.
The polynomial rainbow-forest backend is copied without behavioral changes
from ProveIt_Dual_Forest_Normalization_2026-10-12/code/forest_search/
dual_forest_search.py. Its original comments and attribution are retained in
degree_two_backend.py. See PROOF.md for the new theorem and precise scope.
"""

from collections import deque

import degree_two_backend as backend


def _reach(adjacency, seeds):
    seen = set(seeds)
    queue = deque(seen)
    while queue:
        for target in adjacency[queue.popleft()]:
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return seen


def _interface(data, work):
    """Build the ordinary implication graph and exceptional Horn rules."""
    rows = data[3]
    owners = {}
    for r, row in enumerate(rows):
        for c, a in row:
            owners.setdefault(c, []).append((r, a))
            work.tick("interface_incidence_visits")
    exceptional = {
        c: occupants for c, occupants in owners.items()
        if len(occupants) > 2 and any(a == 1 for _, a in occupants)
    }
    interface = sorted({r for col in exceptional.values() for r, _ in col})
    index = {r: i for i, r in enumerate(interface)}
    adjacency = [set() for _ in rows]
    seeds = set()
    for c, occupants in owners.items():
        if c in exceptional or not any(a == 1 for _, a in occupants):
            continue
        if len(occupants) == 1:
            seeds.add(occupants[0][0])
        else:
            for target, a in occupants:
                if a == 1:
                    source = (occupants[1][0] if target == occupants[0][0]
                              else occupants[0][0])
                    adjacency[source].add(target)
    baseline_rows = tuple(tuple((c, a) for c, a in row if c not in exceptional)
                          for row in rows)
    baseline = data[:3] + (baseline_rows,)
    source_groups = backend._degree_two_groups(baseline, work)
    if source_groups is None:
        raise AssertionError("exceptional-column removal left a large active column")
    universe = set(interface)
    mandatory = [group for group in source_groups if universe.isdisjoint(group)]
    mandatory_rows = {r for group in mandatory for r in group}
    base_reached = _reach(adjacency, seeds | mandatory_rows)
    base_mask = sum(1 << index[r] for r in universe & base_reached)

    # Reverse reachability from each interface vertex computes all signatures
    # in O(u*(m+I)) graph work instead of traversing from every row.
    reverse = [set() for _ in rows]
    for r, targets in enumerate(adjacency):
        for target in targets:
            reverse[target].add(r)
    signature = [0] * len(rows)
    for target in interface:
        bit = 1 << index[target]
        for source in _reach(reverse, {target}):
            signature[source] |= bit
            work.tick("signature_memberships")
    reach_rules = [signature[r] for r in interface]
    horn = []
    for occupants in exceptional.values():
        support_mask = sum(1 << index[r] for r, _ in occupants)
        for r, a in occupants:
            if a == 1:
                target = 1 << index[r]
                horn.append((support_mask ^ target, target))
    return dict(interface=interface, exceptional_columns=sorted(exceptional),
                mandatory=mandatory, mandatory_rows=mandatory_rows,
                base_mask=base_mask, signature=signature,
                reach_rules=reach_rules, horn=horn)


def _closure(model, initial, work):
    active = initial
    while True:
        previous = active
        for i, targets in enumerate(model["reach_rules"]):
            work.tick("interface_reach_rule_tests")
            if active & (1 << i):
                active |= targets
        for premise, target in model["horn"]:
            work.tick("interface_horn_rule_tests")
            if active & premise == premise:
                active |= target
        if active == previous:
            return active


def _partial_partitions(bits):
    """Each object is generated once; omitted bits form a distinguished block."""
    blocks = []

    def visit(index):
        if index == len(bits):
            yield tuple(blocks)
            return
        bit = bits[index]
        yield from visit(index + 1)  # This bit is omitted from the seed subset.
        for block in range(len(blocks)):
            blocks[block] |= bit
            yield from visit(index + 1)
            blocks[block] ^= bit
        blocks.append(bit)
        yield from visit(index + 1)
        blocks.pop()

    yield from visit(0)


def _independent_representatives(data, groups, work):
    """Cloning converts overlapping Rado groups to disjoint color classes."""
    copies, original, clone_groups = [], [], []
    for group in groups:
        clone_group = []
        for r in group:
            edge = data[2][r]
            if edge is None or edge[0] == edge[1]:
                continue
            clone_group.append(len(copies))
            copies.append(edge)
            original.append(r)
            work.tick("candidate_clones")
        if not clone_group:
            work.tick("empty_candidate_groups")
            return None
        clone_groups.append(clone_group)
    clone_data = (data[0], 0, tuple(copies), tuple(() for _ in copies))
    chosen, failure = backend._rainbow_forest(clone_data, clone_groups, work)
    if failure is not None:
        return None
    selected = [original[e] for e in chosen]
    if len(selected) != len(set(selected)):
        raise AssertionError("parallel edge copies escaped graphic independence")
    return selected


def solve_exceptional(problem, *, max_work=None, max_partitions=None):
    """Return SUCCESS, NO_FOREST for this finite class, or INCONCLUSIVE on budget.

    A positive certificate uses the same tree/peeling schema as the prior
    degree-two selector. NO_FOREST from exhaustive partition enumeration is
    a solver result, not a succinct independently certified knot obstruction.
    """
    data = backend.normalize(problem)
    work = backend.Work(max_work, max_partitions)
    metadata = {}
    try:
        failure = backend._source_connectivity(data, work)
        if failure:
            return dict(status="NO_FOREST", reason="unrooted_graph",
                        certificate=failure, method="exceptional_partition",
                        stats=work.export())
        model = _interface(data, work)
        u = len(model["interface"])
        full = (1 << u) - 1
        base = _closure(model, model["base_mask"], work)
        dormant = [1 << i for i in range(u) if not base & (1 << i)]
        metadata = dict(exceptional_columns=len(model["exceptional_columns"]),
                        interface_rows=u, dormant_interface_rows=len(dormant),
                        mandatory_components=len(model["mandatory"]))
        eligible = [r for r, edge in enumerate(data[2])
                    if r not in model["mandatory_rows"] and edge is not None
                    and edge[0] != edge[1]]
        group_cache = {}
        closure_cache = {}
        for blocks in _partial_partitions(dormant):
            work.tick("search_nodes")
            work.tick("partial_partitions")
            initial = 0
            for block in blocks:
                initial |= block
            if initial not in closure_cache:
                closure_cache[initial] = _closure(model, base | initial, work) == full
            if not closure_cache[initial]:
                work.tick("closure_rejections")
                continue
            if len(model["mandatory"]) + len(blocks) > data[0] - 1:
                work.tick("rank_size_rejections")
                continue
            groups = list(model["mandatory"])
            for block in blocks:
                if block not in group_cache:
                    group_cache[block] = [r for r in eligible
                                         if model["signature"][r] & block == block]
                    work.tick("signature_subset_tests", len(eligible))
                groups.append(group_cache[block])
            work.tick("representative_calls")
            selected = _independent_representatives(data, groups, work)
            if selected is None:
                continue
            proof = backend._positive(data, selected, work)
            return dict(status="SUCCESS", certificate=proof,
                        method="exceptional_partition", parameters=metadata,
                        stats=work.export())
        return dict(status="NO_FOREST", reason="exhaustive_partial_partitions",
                    method="exceptional_partition", parameters=metadata,
                    stats=work.export())
    except (backend.BudgetExhausted, RecursionError) as error:
        return dict(status="INCONCLUSIVE", reason=str(error),
                    method="exceptional_partition", parameters=metadata,
                    stats=work.export())


def main():
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--max-work", type=int)
    parser.add_argument("--max-partitions", type=int)
    args = parser.parse_args()
    with open(args.input, encoding="utf-8") as stream:
        result = solve_exceptional(json.load(stream), max_work=args.max_work,
                                   max_partitions=args.max_partitions)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
