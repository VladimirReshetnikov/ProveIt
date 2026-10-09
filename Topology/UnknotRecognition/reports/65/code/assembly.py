"""Complete weighted search in a supplied finite boundary-arc assembly grammar.

The baseline and reduced solver have exactly the same transition generator.
Only the reduced solver prunes a family to disk-completion representatives.
The grammar is abstract unless ambient embedding/collar evidence is supplied
and checked separately. Neither solver returns KNOTTED or UNKNOT.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence
from disk_kernel import Candidate, Partition, canonical, reduce_family, disk_compatible, validate_partition


@dataclass(frozen=True)
class Layer:
    input_width: int
    output_width: int
    options: tuple[Candidate, ...]  # partitions on inputs followed by outputs


def extend(old: Partition, layer: Partition, output_width: int) -> Partition | None:
    r = len(old)
    if len(layer) != r + output_width or output_width < 1:
        raise ValueError("bad layer width")
    cp, cq = max(old) + 1, max(layer) + 1
    parent = list(range(cp + cq))
    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a
    for i in range(r):
        a, b = find(old[i]), find(cp + layer[i])
        if a == b:
            return None  # a new cycle creates positive topological defect
        parent[a] = b
    roots = {find(i) for i in range(cp + cq)}
    output = [find(cp + layer[r + i]) for i in range(output_width)]
    if set(output) != roots:
        return None  # a component has lost every future attachment arc
    return canonical(output)


def exact_deduplicate(items: Sequence[Candidate]) -> tuple[Candidate, ...]:
    table = {}
    for item in items:
        old = table.get(item.partition)
        if old is None or (item.cost, item.witness) < (old.cost, old.witness):
            table[item.partition] = item
    return tuple(table.values())


def solve(initial: Sequence[Candidate], layers: Sequence[Layer], caps: Sequence[Candidate],
          *, compressed: bool = True, collect_certificates: bool = False) -> dict:
    if not initial:
        raise ValueError("a nonempty initial family is required")
    r = len(initial[0].partition)
    for item in initial:
        validate_partition(item.partition)
        if len(item.partition) != r or type(item.cost) is not int:
            raise ValueError("bad initial state")
    for layer in layers:
        if type(layer.input_width) is not int or type(layer.output_width) is not int:
            raise ValueError("integer layer widths required")
        if layer.input_width != r or layer.output_width < 1:
            raise ValueError("incompatible layer dimensions")
        for item in layer.options:
            validate_partition(item.partition)
            if len(item.partition) != r + layer.output_width or type(item.cost) is not int:
                raise ValueError("invalid option")
        r = layer.output_width
    for item in caps:
        validate_partition(item.partition)
        if len(item.partition) != r or type(item.cost) is not int:
            raise ValueError("invalid cap")
    stats = {"transition_attempts": 0, "terminal_attempts": 0,
             "exact_stage_sizes": [], "stored_stage_sizes": []}
    evidence = []
    def prune(family):
        family = exact_deduplicate(family)
        stats["exact_stage_sizes"].append(len(family))
        if compressed:
            result = reduce_family(family)
            if collect_certificates:
                evidence.append({"partitions": [list(x.partition) for x in family],
                                 "costs": [x.cost for x in family],
                                 "certificate": result.certificate})
            family = result.retained
        stats["stored_stage_sizes"].append(len(family))
        return family
    states = prune([Candidate(x.partition, x.cost, (i,)) for i, x in enumerate(initial)])
    for layer in layers:
        generated = []
        for state in states:
            for j, option in enumerate(layer.options):
                stats["transition_attempts"] += 1
                out = extend(state.partition, option.partition, layer.output_width)
                if out is not None:
                    generated.append(Candidate(out, state.cost + option.cost, state.witness + (j,)))
        states = prune(generated)
    best = None
    for state in states:
        for j, cap in enumerate(caps):
            stats["terminal_attempts"] += 1
            if disk_compatible(state.partition, cap.partition):
                item = Candidate(state.partition, state.cost + cap.cost, state.witness + (j,))
                if best is None or (item.cost, item.witness) < (best.cost, best.witness):
                    best = item
    return {"status": "FOUND_ABSTRACT_DISK" if best is not None else "NO_DISK_IN_GRAMMAR",
            "cost": None if best is None else best.cost,
            "witness": None if best is None else list(best.witness),
            "stats": stats, "certificates": evidence}


def replay_surface(initial, layers, caps, witness):
    """Literal triangulated-surface witness replay, without frontier transitions."""
    from surface_model import assemble_patches
    if len(witness) != len(layers) + 2:
        raise ValueError("incorrect witness length")
    lengths = [len(initial)] + [len(L.options) for L in layers] + [len(caps)]
    if any(type(i) is not int or not 0 <= i < n for i, n in zip(witness, lengths)):
        raise ValueError("invalid witness index")
    selected = [initial[witness[0]]] + [L.options[i] for L, i in zip(layers, witness[1:-1])] + [caps[witness[-1]]]
    parts = [x.partition for x in selected]
    pairings = []
    previous_output_start = 0
    previous_width = len(parts[0])
    for k, layer in enumerate(layers, start=1):
        for i in range(previous_width):
            pairings.append(((k - 1, previous_output_start + i), (k, i)))
        previous_output_start = layer.input_width
        previous_width = layer.output_width
    for i in range(previous_width):
        pairings.append(((len(parts) - 2, previous_output_start + i), (len(parts) - 1, i)))
    result = assemble_patches(parts, pairings)
    result["cost"] = sum(x.cost for x in selected)
    return result
