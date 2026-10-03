"""Independent bounded audit of arithmetic discovery for the NEW candidate rule.

The all-index oracle is intentionally small-source, test-only. Production must
not use it. This audit leaves prior packets unchanged.
"""
from bisect import bisect_left, bisect_right
import argparse
from pathlib import Path
import importlib.util
import json
import random
import sys

from sparse_parallel import SparseParallelCompiler

HERE = Path(__file__).resolve().parent
OLD = HERE / 'frozen_lazy_source.py'
spec = importlib.util.spec_from_file_location('_candidate_audit_lazy', OLD)
lazy = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = lazy
spec.loader.exec_module(lazy)


def check(value, detail):
    if not value:
        raise RuntimeError(detail)


def source(side=1, delta=1, J=0):
    guard = {'op': 'true'} if delta >= 0 else {
        'op': 'gt', 'counter': (side+1)//2, 'value': 0}
    return dict(schema='reversible-two-counter-v1', controls=['q', 'h'],
                start='q', halt='h', class_cut=J, branches=[
                    dict(name='edge', source='q', target='h', side=side,
                         delta=delta, guard=guard)])


def scan(c, x, indices, sparse):
    ordered = sorted(x)
    out = {}
    for i in indices:
        g = c.gate_at(i)
        for label, shape in enumerate(g.shapes):
            for z in x:
                u = z - min(shape)
                if not all(u+d in x for d in shape):
                    continue
                count = (bisect_right(ordered, u+g.L)
                         - bisect_left(ordered, u-g.L)) if sparse else sum(
                             abs(v-u) <= g.L for v in x)
                if count != len(shape):
                    continue
                if g.guard is not None and not (
                        lazy._guard_sparse(g.guard, ordered, u) if sparse
                        else g.guard.allows(x, u)):
                    continue
                check((i, u) not in out or out[i, u] == label,
                      ('ambiguous orientation', i, u))
                out[i, u] = label
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=HERE)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(202610031222)
    sources = [source(side, delta, J) for side in (-1, 1)
               for delta in (-1, 0, 1) for J in (0, 2)]
    empty = source()
    empty['branches'] = []
    sources.append(empty)
    fan = source()
    fan['controls'] = ['q', 'zero', 'pos', 'h']
    fan['class_cut'] = 1
    fan['branches'] = [
        dict(name='zero', source='q', target='zero', side=1, delta=0,
             guard=dict(op='eq', counter=1, value=0)),
        dict(name='pos', source='q', target='pos', side=1, delta=0,
             guard=dict(op='gt', counter=1, value=0)),
        dict(name='inczero', source='zero', target='h', side=1, delta=1,
             guard=dict(op='eq', counter=1, value=0)),
        dict(name='incpos', source='pos', target='h', side=1, delta=1,
             guard=dict(op='gt', counter=1, value=0))]
    sources.append(fan)
    endpoints = comparisons = guard_checks = 0
    for data in sources:
        c = lazy.compile_lazy_source(data)
        actual = SparseParallelCompiler(data)
        for i in range(c.factors):
            g = c.gate_at(i)
            for shape in g.shapes:
                for shift in (0, -13, -(1 << 130), (1 << 130)+31):
                    x = frozenset(shift+d for d in shape)
                    check(i in c._candidate_indices(x),
                          ('missed exact endpoint', i, shift))
                    noise = x | {shift + rng.randrange(-3*c.Z, 3*c.Z)
                                 for _ in range(6)}
                    check(i in c._candidate_indices(noise),
                          ('missed contained endpoint with noise', i, shift))
                    endpoints += 2
        # Sparse raw rules versus an independent literal all-type scan, with
        # full label/key equality, both family boundaries, and negative anchors.
        for trial in range(80):
            if trial < 60:
                g = c.gate_at(rng.randrange(c.factors))
                x = set(rng.choice(g.shapes))
                x.update(rng.randrange(-2*c.Z, 2*c.Z) for _ in range(trial % 7))
                if trial % 3 == 0:
                    x.update((-c.Z-rng.randrange(c.J+2), c.Z+rng.randrange(c.J+2)))
            else:
                x = {rng.randrange(-3*c.Z, 3*c.Z) for _ in range(trial % 13)}
            shift = -(1 << 130) if trial % 4 == 0 else -17
            x = frozenset(z+shift for z in x)
            found = scan(c, x, c._candidate_indices(x), True)
            oracle = scan(c, x, range(c.factors), False)
            check(found == oracle, ('candidate mismatch', data, trial, found, oracle))
            for phase in ('E', 'P'):
                select = lambda key: (key[0] < c.E_count) == (phase == 'E')
                family = {k: v for k, v in oracle.items() if select(k)}
                check({k: v for k, v in found.items() if select(k)} == family,
                      ('family key mismatch', phase))
                block = getattr(actual, phase)
                check(dict(block.candidates(x)) == family,
                      ('actual raw mismatch', phase, trial))
                selected = {}
                for key, label in family.items():
                    i, u = key
                    if any(k != key and abs(k[1]-u) <= block.H for k in family):
                        continue
                    g = c.gate_at(i)
                    y = frozenset((x - {u+d for d in g.shapes[label]}) |
                                  {u+d for d in g.shapes[1-label]})
                    after = scan(c, y, range(c.factors), False)
                    before_keys = {k for k in family if abs(k[1]-u) <= block.b+block.r}
                    after_keys = {k for k in after if select(k) and abs(k[1]-u) <= block.b+block.r}
                    if before_keys == after_keys:
                        selected[key] = label
                check(dict(block.eligible(x)) == selected,
                      ('actual selection mismatch', phase, trial))
                want = set(x)
                for (i, u), label in selected.items():
                    g = c.gate_at(i)
                    want.difference_update(u+d for d in g.shapes[label])
                    want.update(u+d for d in g.shapes[1-label])
                check(block.apply(x, verify=trial % 10 == 0) == frozenset(want),
                      ('actual block mismatch', phase, trial))
            comparisons += 1
        for branch in c.branches:
            for table in (branch.domain_table, branch.image_table):
                guard = lazy.ref._record(lazy.ref._ClassGuard, J=c.J, Z=c.Z, table=table)
                for trial in range(80):
                    u = -(1 << 130) + trial
                    x = {u+side*(c.Z+k) for side in (-1, 1)
                         for k in range(c.J+2) if rng.randrange(3) == 0}
                    check(lazy._guard_sparse(guard, sorted(x), u) == guard.allows(x, u),
                          ('sparse guard mismatch', data, trial))
                    guard_checks += 1
    receipt = dict(status='passed', source_cases=len(sources),
                   endpoint_containment_checks=endpoints,
                   full_candidate_map_comparisons=comparisons,
                   actual_block_candidate_selection_output_comparisons=2*comparisons,
                   sparse_guard_comparisons=guard_checks,
                   optimized=bool(sys.flags.optimize),
                   scope='Small-source finite tests supplement the symbolic proof; no universal enumeration.')
    name = 'audit-candidate-receipt-optimized.json' if sys.flags.optimize else 'audit-candidate-receipt.json'
    (args.output_dir/name).write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
