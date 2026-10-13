"""Exhaust marked equivalence against literal equivariant fibre bijections."""
import argparse
from itertools import permutations, product
import json
from pathlib import Path
import sys

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))
from fastunknot.surface_cover import CoverIndex


def components(n, maps):
    """Explicit orbits, without gcds, classification or signature formulas."""
    remaining = set(range(n))
    answer = []
    while remaining:
        todo = [min(remaining)]
        found = set(todo)
        while todo:
            x = todo.pop()
            for p in maps:
                y = p[x]
                if y not in found:
                    found.add(y)
                    todo.append(y)
        remaining.difference_update(found)
        answer.append(tuple(sorted(found)))
    return answer


def bijections(source, target, maps):
    if len(source) != len(target):
        return []
    answer = []
    for image in permutations(target):
        f = dict(zip(source, image))
        if all(f[p[x]] == p[f[x]] for p in maps for x in source):
            answer.append(f)
    return answer


def audit(max_sheets=6):
    totals = dict(presentations=0, marked_comparisons=0, transported_sheets=0,
                  unmarked_comparisons=0, rooted_comparisons=0, max_sheets=max_sheets)
    for n in range(1, max_sheets + 1):
        atoms = tuple(product((-1, 1), range(n)))
        for monodromy in product(atoms, repeat=2):
            raw = dict(surface=dict(orientable=True, genus=0, boundary_components=3),
                       sheets=n, monodromy=[dict(sign=s, shift=a) for s, a in monodromy])
            index = CoverIndex(raw)
            maps = [tuple((s*x+a) % n for x in range(n)) for s, a in monodromy]
            orbits = components(n, maps)
            signatures = {}
            for orbit in orbits:
                for size in (0, 1, 2):
                    for marks in product(orbit, repeat=size):
                        signatures[orbit, marks] = index.marked_signature(orbit[0], marks)
            for source in orbits:
                for target in orbits:
                    witnesses = bijections(source, target, maps)
                    assert ((signatures[source, ()] == signatures[target, ()]) == bool(witnesses))
                    totals['unmarked_comparisons'] += 1
                    for x in source:
                        for y in target:
                            rooted = [f for f in witnesses if f[x] == y]
                            assert len(rooted) <= 1
                            for z in source:
                                observed = index.transport_sheet(x, y, z)
                                expected = rooted[0][z] if rooted else None
                                assert observed == expected, (raw, x, y, z)
                                totals['transported_sheets'] += 1
                            totals['rooted_comparisons'] += 1
                    for size in (1, 2):
                        for left in product(source, repeat=size):
                            allowed = {tuple(f[x] for x in left) for f in witnesses}
                            for right in product(target, repeat=size):
                                equal = signatures[source, left] == signatures[target, right]
                                assert equal == (right in allowed), (raw, left, right)
                                totals['marked_comparisons'] += 1
            totals['presentations'] += 1
    return totals


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = audit()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, sort_keys=True))
