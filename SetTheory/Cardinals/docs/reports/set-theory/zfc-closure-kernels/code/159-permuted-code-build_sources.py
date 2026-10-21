#!/usr/bin/env python3
"""Rebuild all source artifacts from pinned historical K219 and K217 JSON files.
No search, third-party packages, or binary transition-table allocator is used.
"""
import argparse
import hashlib
import json
from pathlib import Path
import audit_command_permutation as audit

PIN217 = '9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655'

def compact(tree):
    return (json.dumps(audit.sites(tree), separators=(',', ':'))+'\n').encode()

def splice_closed(tree, edits):
    used = {}
    def walk(t, lo=0):
        hi = lo + audit.width(t)
        affected = [(rg, replacement) for rg, replacement in edits.items()
                    if not (hi <= rg[0] or rg[1] <= lo)]
        if not affected: return t
        for (start, end), replacement in affected:
            if start <= lo and hi <= end:
                assert audit.boundary(t) == (0, 0)
                if lo == start:
                    used[start, end] = used.get((start, end), 0)+1
                    return replacement
                return None
        assert not audit.leaf(t)
        left = walk(t[0], lo)
        right = walk(t[1], lo+audit.width(t[0]))
        if left is None:
            if right is not None: assert audit.boundary(right) == (0, 0)
            return right
        if right is None:
            assert audit.boundary(left) == (0, 0)
            return left
        return left, right
    answer = walk(tree)
    assert used == {rg: 1 for rg in edits}
    return answer

def build(args):
    b219 = Path(args.baseline219).read_bytes()
    b217 = Path(args.baseline217).read_bytes()
    assert hashlib.sha256(b219).hexdigest() == audit.PINS['baseline219']
    assert hashlib.sha256(b217).hexdigest() == PIN217
    t219 = audit.parse(json.loads(b219))
    t217 = audit.parse(json.loads(b217))
    reference = audit.noncommon_reference(t219)
    read_d = audit.extract(t219, 23, 37)
    load_d = audit.extract(t219, 40, 66)
    assert audit.width(read_d) == 14 and audit.width(load_d) == 26
    # One closed associativity rotation of (read_d, load_d):
    # ((walk11, transfer3), load_d) -> (walk11, (transfer3, load_d)).
    walk11, transfer3 = read_d
    assert [audit.width(walk11), audit.width(transfer3)] == [11, 3]
    assert all(audit.boundary(t) == (0, 0) for t in (walk11, transfer3, load_d))
    read_then_load = walk11, (transfer3, load_d)
    source202 = splice_closed(t217, {
        (23, 37): None,       # Delete common counter-input read.
        (187, 201): None,     # Move AX counter read after its first implication.
        (228, 254): read_then_load,
        (4659, 4685): read_then_load,  # Local counter input on MP.
    })
    assert hashlib.sha256(compact(source202)).hexdigest() == audit.PINS['frozen202']
    assert audit.structured_graph(source202) == audit.structured_graph(reference)
    assert audit.counter_graph(audit.sites(source202)) == audit.structured_graph(reference)
    products = {'sites205_reference.json': reference, 'sites202.json': source202}
    for permutation in ('210', '120'):
        tree = audit.permute(source202, tuple(map(int, permutation)))
        assert hashlib.sha256(compact(tree)).hexdigest() == audit.PINS[permutation]
        assert audit.structured_graph(tree) == audit.counter_graph(audit.sites(tree))
        products[f'sites{permutation}.json'] = tree
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    records = {}
    for name, tree in products.items():
        raw = compact(tree)
        (out/name).write_bytes(raw)
        records[name] = {'sha256': hashlib.sha256(raw).hexdigest(), **audit.metrics(tree)}
    receipt = {'status': 'PASS_DETERMINISTIC_SOURCE_REBUILD',
               'inputs': {'baseline219_sha256': audit.PINS['baseline219'],
                          'baseline217_sha256': PIN217},
               'construction': 'Four closed interval splices in K217, with one closed right association of read_D followed by load_D; then a permutation of three closed command bodies.',
               'edits_in_K217_ordinals': [[23, 37], [187, 201], [228, 254], [4659, 4685]],
               'products': records,
               'scope': 'Source reconstruction and exact finite control-flow checks; no binary machine allocation or simulation.'}
    (out/'source_build.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline219', required=True)
    ap.add_argument('--baseline217', required=True)
    ap.add_argument('--output', required=True)
    build(ap.parse_args())
