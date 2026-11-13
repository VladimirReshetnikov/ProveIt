#!/usr/bin/env python3
"""Point-in-time source/object provenance survey; no semantic formula check."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parent.parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins = {
    D / 'research/nine-sharing-norm38-ipra-endpoint-check/attempt01/state.json': 'd55d3235bbd3636c7a1f7650b306a9786c2e2f3902bbec176599c8565b396ee5',
    D / 'research/nine-sharing-norm38-ipra-endpoint-check/src/DiophantineConsistency/Norm38IPRAEndpoint.lean': 'fe84dc25c6d4bb7c7ebfa06d1ff28d622f607c58dc1a4338214e0a40314a7f0c',
    D / 'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/SharingSeed38Syntax.lean': '9bde9c1eeaeda37dd59c097bcec2eb90df76ba07aa5a7e349ebe3eeae4b2e445',
    D / 'research/nine-current-lightweight-jones-probe/attempt01/state.json': '5003d43d0deb8c7339766d9ea62bb3866a66fba9d4d277fcca5f4afcf0db33d4',
    P / 'Norm38NamedFormula.lean': 'a5a8db6833252881c37016f3b28e006168db45a8119074b04572c8341d2593e6',
    P / 'FORMULA.md': '2ae78c33cf6f5f9a6096918aee8475c72adc205abbd6a954c69e7e06b457081c',
}
for p, expected in pins.items():
    if sha(p) != expected:
        raise RuntimeError(('pin mismatch', str(p)))

endpoint_root = Path('/tmp/nine-sharing-norm38-ipra-endpoint-check-20261106/lib/DiophantineConsistency')
probe_root = Path('/tmp/nine-light-jones-probe-20261105/lib/DiophantineConsistency')
probe = json.loads((D / 'research/nine-current-lightweight-jones-probe/attempt01/state.json').read_text())
if probe['status'] != 'PASS':
    raise RuntimeError('Jones probe not PASS')
expected = {
    'JonesSyntaxCore': ('f79661e08bf9bc1a15a88f6c6e433542e9f7808c4dc88066b7fdac424b211384', '62207d1acfeb39ee8b68a5c0a25dd0672f6e10bb7a39adc87e630f8c71061dca'),
    'ExecutableJonesCore': ('89832bbdcfcde58747c535a12a37d9ad76d3ca3298a30c00c9b9cfe7eaff1ec4', 'c1b97559f58ba03cf6bdbb79d5f8cd57bae05a850bc1d080c5de7fe8af470694'),
    'ModelJonesSyntax': ('6237531aa559af356ce3b4bf6159c62a207037ac79fb83de937d8f89c8f1fabd', 'ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171'),
}
for name, (source_hash, object_hash) in expected.items():
    rows = [r for r in probe['rows'] if r['module'] == name]
    if len(rows) != 1:
        raise RuntimeError(('producer row', name))
    row = rows[0]
    source = D / 'research/nine-current-lightweight-jones-probe/src/DiophantineConsistency' / (name + '.lean')
    out = probe_root / (name + '.olean')
    link = endpoint_root / (name + '.olean')
    if (row['source_sha256'] != source_hash or row['object_sha256'] != object_hash or
        row['deps']['exit'] != 0 or row['compile']['exit'] != 0 or
        sha(source) != source_hash or sha(out) != object_hash or
        not link.is_file() or link.resolve() != out.resolve() or sha(link) != object_hash):
        raise RuntimeError(('producer or overlay mismatch', name))
endpoint = endpoint_root / 'Norm38IPRAEndpoint.olean'
if sha(endpoint) != '570952bced71ff043c7fa9f0f84af3e99b8a6fea2f373651f12c01e7e6c72125':
    raise RuntimeError('endpoint object')
print(json.dumps({'status': 'PASS_POINT_IN_TIME_SOURCE_OBJECT_SURVEY',
                  'scope': 'Pinned source bytes, three recorded Jones producer rows and current overlay routes; no formula transcription, Lean replay or complete transitive/dynamic trace.',
                  'jones_producers': {k: {'source_sha256': a, 'object_sha256': b} for k, (a, b) in expected.items()},
                  'endpoint_object_sha256': sha(endpoint)}, indent=2, sort_keys=True))
