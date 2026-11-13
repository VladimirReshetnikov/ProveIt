#!/usr/bin/env python3
"""Inspect the retained ranked-main run and its direct providers, without Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')

root = Path(__file__).resolve().parents[2]
packet = root / 'research/p64-qcube72-ranked-main-draft'
retained = packet / 'observations/attempt03'
out = Path('/tmp/p64-qcube72-ranked-main-priority-check03')
expected = {
    packet / 'FreeMainRankedMain.lean': '633f9b3d64fee060a845e18c1d1a437137c08d06ac55232c3ebb232651d65a3f',
    packet / 'check03.py': 'b78fc2608dbbc03cecbfc5a0eb44c342add76c9ef324ae1e49deae76ddc6cc55',
    packet / 'missing_child.py': 'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
    retained / 'result.json': '476ea25cd88141f0a8ab0832af5740636423fa93df8eee00ffdb0b9c41dd0eaa',
    retained / 'compile.log': '4b8b64378605248fe8e1bfa678be0d7ca39ff6e7f9bba88cbc6111bc3c8c0a98',
    out / 'FreeMainRankedMain.olean': 'be2865b509d0f2f854430a3ce10dd2f6e6474b0e9801988661349236a60c40e8',
}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

for p, h in expected.items():
    if not p.is_file() or p.is_symlink() or sha(p) != h:
        raise RuntimeError('artifact mismatch: ' + str(p))
if (out/'result.json').read_bytes() != (retained/'result.json').read_bytes():
    raise RuntimeError('terminal receipt differs from retained copy')
if (out/'compile.log').read_bytes() != (retained/'compile.log').read_bytes():
    raise RuntimeError('terminal log differs from retained copy')

r = json.loads((retained/'result.json').read_text())
if (r['status'], r['exit'], r['stop_reason'], r['guards_stable']) != ('PASS', 0, None, True):
    raise RuntimeError('not a passing terminal receipt')
if r['guards_before'] != r['guards_after'] or r['group_rss_samples'] <= 0:
    raise RuntimeError('guards or samples invalid')
if r['object_sha256'] != expected[out/'FreeMainRankedMain.olean'] or r['log_sha256'] != expected[retained/'compile.log']:
    raise RuntimeError('output receipt mismatch')
if r['runner_sha256'] != expected[packet/'check03.py'] or r['missing_child_helper_sha256'] != expected[packet/'missing_child.py']:
    raise RuntimeError('runner receipt mismatch')
log = (retained/'compile.log').read_text()
if log.strip() != "'FreeMainRankedMain.main_at_rank' depends on axioms: [propext, Classical.choice, Quot.sound]":
    raise RuntimeError('unexpected compiler output')

# Reinspect the saved before/after guards, including checked direct shadows.
for raw, item in r['guards_after'].items():
    p = Path(raw)
    if item is None:
        if p.exists() or p.is_symlink():
            raise RuntimeError('previously absent guard now exists: ' + raw)
    elif not p.is_file() or str(p.resolve()) != item['realpath'] or sha(p) != item['sha256']:
        raise RuntimeError('guard does not match: ' + raw)

providers = [
    (root/'research/p64-qcube72-conditional-rank-draft/observations/attempt01/result.json',
     '/tmp/p64-qcube72-conditional-rank-priority-check01/FreeMainConditionalRank.olean',
     '5aaee0759cb98c0e1cafcc2c3a3d42c016b9f65c9827d8e584c46192c0226d34'),
    (root/'research/p64-qcube72-natural-norms-draft/observations/aux04/result.json',
     '/tmp/p64-qcube72-aux-norm-priority-check04/FreeMainAuxNorm.olean',
     '42c353eec1f0e4150ec9787dc82e5bcc34bff1419df3d5e8c8ef6ce4359b2bd8'),
]
for receipt, obj, h in providers:
    p = json.loads(receipt.read_text())
    if (p['status'], p['exit'], p['guards_stable'], p['object_sha256']) != ('PASS', 0, True, h):
        raise RuntimeError('provider receipt mismatch: ' + str(receipt))
    if r['guards_after'][obj]['sha256'] != h:
        raise RuntimeError('provider is not the guarded input: ' + obj)
    if Path(obj).parent.as_posix() not in r['lean_path'].split(':'):
        raise RuntimeError('provider absent from search path: ' + obj)

source = (packet/'FreeMainRankedMain.lean').read_text()
for required in ('(hq : 33≤qval p v)', '(hR : 0<FreeMainAuxNorm.rank p v)',
                 '(hhalf : 2*FreeMainAuxNorm.rank p v<cval p v)',
                 'FreeMainStrongNorm.strong p v hv hz', 'FreeMainAuxNorm.auxiliary p v hv hz',
                 'FreeMainConditionalRank.main_index_eq_rank p v (FreeMainAuxNorm.rank p v)'):
    if required not in source:
        raise RuntimeError('source theorem or composition changed: ' + required)
print(json.dumps({'status':'PASS', 'source':'ranked-main attempt03', 'lean_replayed':False,
                  'direct_providers':2, 'guard_entries_checked':len(r['guards_after']),
                  'scope':'Retained terminal artifact and direct-provider audit; transitive/dynamic ancestry inherited.'}, sort_keys=True))
