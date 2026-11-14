#!/usr/bin/env python3
"""Check shipped file integrity and bind the release facts to literal artifacts."""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without Python -O or PYTHONOPTIMIZE.')
    checked = 0
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT / name
        assert path.is_file(), name
        assert sha(path) == expected, 'File digest mismatch: ' + name
        checked += 1
    dense = ROOT / 'machine/pa194C.tm'
    native = ROOT / 'machine/pa194C.native.tm'
    assert sha(dense) == 'd759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b'
    assert sha(native) == 'b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c'
    assert dense.read_bytes() == (ROOT / 'construction/rebuilt_194C/pa194C.tm').read_bytes()
    assert native.read_bytes() == (ROOT / 'construction/rebuilt_194C/pa194C.native.tm').read_bytes()
    rows = [line.split() for line in dense.read_text().splitlines()]
    assert len(rows) == 388
    assert {(int(q), int(b)) for q, b, w, d, t in rows} == {
        (q, b) for q in range(194) for b in (0, 1)}
    assert all(w in ('0', '1') and d in ('L', 'R') and 0 <= int(t) <= 194
               for q, b, w, d, t in rows)
    receipt = json.loads((ROOT / 'verification/independent/recorded_C/PA194C/receipt.json').read_text())
    assert receipt['status'] == 'PASS'
    assert receipt['source_sites'] == 3649 and receipt['source_contracts'] == 4749
    assert receipt['startup_steps'] == 57922 and receipt['whole_blank_tape_equal']
    assert receipt['symbolic_steps'] == 1096302 and not receipt['arithmetic_box_oracles']
    assert receipt['root_free_graph_sha256'] == 'b79f4d344740679b87dace02fe3f211565c2cd4513f346812570d90caa3d9a3f'
    novelty = json.loads((ROOT / 'comparison/all194_novelty.json').read_text())
    assert novelty['prior194_graph_classes'] == 4
    assert novelty['new194C_absent_even_after_control_relabeling_root_change_and_reflection']
    print(json.dumps({'status': 'PASS', 'files_verified': checked,
                      'states': 194, 'rows': 388, 'independent_source_outcomes': 4749,
                      'scope': 'Release integrity and evidence binding; run both checkers to regenerate certificates.'}, indent=2))


if __name__ == '__main__':
    main()
