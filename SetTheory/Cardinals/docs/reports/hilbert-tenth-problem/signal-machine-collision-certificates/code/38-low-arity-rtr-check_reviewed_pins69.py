#!/usr/bin/env python3
"""Independent byte-pin and original/copied metadata checks, no imports from inputs."""
import hashlib
import json
from pathlib import Path

C = Path('/workspace/shared/report69-tool-review-candidate-v5')
O = Path('/workspace/shared/report69-independent-release-tool-review-20261004')
PINS = {
    'README.md': '975cae6eca069477fb5164d506b68ff8b7351bab7209a916ddb72e9a06d7036a',
    'tools/release69.py': 'cf70098ca75442d0e7868bf63fe03a15f80694895aa2ffe660d16f67c4ed3807',
    'tools/build_report69.py': '16074885d6203a09cbcc448478d4d4cbfb4ac91c36c018963da793d08194e2cb',
    'tools/selftest69.py': 'c3beaf2f18090c851ead535239e6ef91964a3241bce11ea8004f980f9cd326f4',
    'Report69.pdf': 'fc0db742d499ee0e515700134460f78b44d3c7301f14c63c77cfa6fb9a6686ce',
    'Report69.tex': '9f0508066f9354b6c7d74b4d6b8a10498e632e5e31b149ff8312ffb75f82cfd0',
    'manuscript/MANUSCRIPT_PINS.json': '38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c',
    'tools/BUILD_DEPENDENCIES_LOCK.json': '62d196ba3a660790910afa4ac4eb83f1410b8b64e6a401ad52d1388ee812f3f5',
    'INPUT_PINS.json': '5b1563a78935432a6d96f6665335f78c7c996f25d65e7b9e6e2532d909a9649d',
}

def main():
    baseline = json.loads((O / 'PRESERVATION_BEFORE.json').read_bytes())
    after = json.loads((O / 'PRESERVATION_AFTER.json').read_bytes())
    assert baseline == after
    rows = {}
    for name, expected in PINS.items():
        raw = (C / name).read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        assert actual == expected
        rows[name] = {'bytes': len(raw), 'sha256': actual}
    source_map = json.loads((C / 'INPUT_PINS.json').read_bytes())
    compared = 0
    for scope, original in source_map['source_roots'].items():
        for path, row in baseline[original].items():
            suffix = Path(path).relative_to(original)
            copied = str(C / scope / suffix)
            assert baseline[str(C)][copied] == row, (path, copied)
            compared += 1
    record = json.loads((C / 'qa/ORIGINAL_INPUT_METADATA.json').read_bytes())
    flattened = {path: row for root in baseline.values() for path, row in root.items()}
    for path, row in record.items():
        assert {k: flattened[path][k] for k in row} == row, path
    receipt = {'status': 'PASS', 'candidate': str(C), 'reviewed_pins': rows,
               'source_copy_entries_compared': compared, 'original_baseline_record_entries': len(record),
               'preserved_root_count': len(baseline), 'preserved_entry_count': sum(len(v) for v in baseline.values()),
               'all_source_bytes_modes_mtimes_and_root_metadata_preserved': True,
               'scope': 'Byte and metadata identity only; no scientific code import/execution'}
    (O / 'REVIEWED_PINS.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps(receipt, sort_keys=True, indent=2))

if __name__ == '__main__':
    main()
