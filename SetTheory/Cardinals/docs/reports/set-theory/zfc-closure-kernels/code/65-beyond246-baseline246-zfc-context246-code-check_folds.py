#!/usr/bin/env python3
"""Independently check the contextual quotient and exact source identities.

The finite commutation check becomes an unbounded simulation only with the
forced-symbol invariants proved in the report. This script does not infer
unreachability from a sampled execution.
"""
from hashlib import sha256
from pathlib import Path
import json
import independent_rebuild as independent
from rebuild_machines import ROOT, build, encode, read_table, CANONICAL_SHA256


def main():
    if not __debug__:
        raise SystemExit('Assertions are required; run without -O.')
    raw = (ROOT/'sources/prefix250_old.tm').read_bytes()
    prior, candidate, canonical, mapping = independent.generate(raw)
    assert candidate == build()
    assert encode(candidate, 95) == (ROOT/'machine/zfc_prefix246_old.tm').read_text()
    assert sha256(encode(canonical, 0).encode()).hexdigest() == CANONICAL_SHA256
    assert encode(canonical, 0) == (ROOT/'machine/zfc_prefix246.tm').read_text()
    excluded = {(0,0),(1,0),(1,1),(3,0),(3,1),(97,0)}
    def quotient(q):
        return {0:20, 97:255}.get(q, q)
    checked = 0
    for (q, b), (w, d, t) in prior.items():
        if (q,b) not in excluded:
            assert candidate[quotient(q),b] == (w,d,quotient(t))
            checked += 1
    assert checked == 494
    incoming = lambda target: sorted([list(k) for k, v in prior.items() if v[2] == target])
    assert incoming(0) == [[60,0]]
    assert incoming(1) == [[0,0],[1,1],[3,1]]
    assert incoming(3) == [[1,0]]
    assert incoming(97) == [[255,0]]
    assert incoming(255) == [[75,0]]
    assert prior[0,1] == candidate[20,1] == (0,'L',2)
    assert prior[97,1] == candidate[255,1] == (1,'L',131)
    assert candidate[75,0] == (1,'R',255)
    # These are the complete finite control premises of the two proofs.
    # Marking supplies a compulsory one; the pulse writes its own one.
    reachable, queue = set(), [95]
    while queue:
        q=queue.pop()
        if q == 254 or q in reachable:
            continue
        reachable.add(q)
        queue += [candidate[q,b][2] for b in (0,1)]
    assert reachable == {q for q,b in candidate}
    # All preserved source references are byte pinned, without claiming a build.
    manifest=json.loads((ROOT/'sources/lean-snapshot-manifest.json').read_text())
    for item in manifest['files']:
        assert sha256((ROOT/item['packaged_path']).read_bytes()).hexdigest() == item['sha256']
    result=dict(status='PASS', contextual_quotient_pairs=checked,
        excluded_pairs=[list(p) for p in sorted(excluded)],
        incoming_edges={str(q):incoming(q) for q in (0,1,3,97,255)},
        graph_reachable_working_states=len(reachable),
        independent_construction_matches=True,
        exact_lean_source_snapshots=len(manifest['files']),
        proof_scope='494 exact commuting rows; the universal domain restrictions '
            'are proved from register shape and the preceding write, not sampled.',
        new_proof_assistant_endpoint=False)
    (ROOT/'results/contextual-folds.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
