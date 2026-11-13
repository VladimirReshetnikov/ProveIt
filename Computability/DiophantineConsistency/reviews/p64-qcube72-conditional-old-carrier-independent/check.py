#!/usr/bin/env python3
"""Audit conditional old-carrier index client without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-conditional-old-carrier-draft'
obs=packet/'observations/attempt02'
out=Path('/tmp/p64-qcube72-conditional-old-carrier-priority-check02')
pins={packet/'FreeMainConditionalOldCarrier.lean':'a9cd0475ef4eab492a974fd37fc93c8752b1571be59ac7c50bf0aeabdf995cf6',
 packet/'check02.py':'e7ad76681a0069160123d8ce7b4b7e5e0f36d0af9cf6b717e5e8951985998bd5',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'f7b48d86639955508309172d48fdd7ed3f45948868be0b6a15e263ff425c7aca',
 obs/'result.json':'e6349811f43aa395de6058b1771a1e5a6f4fdd12b41a18fd9927e003901f7183',
 out/'FreeMainConditionalOldCarrier.olean':'cf77a2a51742d9dc22e20d2e766df715d4318557848602bb2790466feb82fa2e'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check02.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainConditionalOldCarrier.olean']):raise RuntimeError('receipt hash mismatch')
names=('index_eq_of_witness','fixed_of_witness')
want='\n'.join(f"'FreeMainConditionalOldCarrier.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
if (obs/'compile.log').read_text().strip()!=want:raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers={
 '/tmp/p64-qcube72-fixed-compact-carrier-cancel-priority-check01/FreeMainFixedCompactCarrierCancel.olean':'3dbbbc7253c3c0976f39adf9450d35e8b3280e098641c330268d7a9573b69434',
 '/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/P72Exact.olean':'6371d9c4a0b3374c0d4ac066607e689441fcdcece28b6fb397389b4061d61f2a'}
for path,h in providers.items():
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('provider mismatch '+path)
producer=json.loads((root/'research/p64-qcube72-fixed-compact-carrier-cancel-draft/observations/attempt01/result.json').read_text())
if (producer['status'],producer['exit'],producer['object_sha256'])!=('PASS',0,providers[next(iter(providers))]):raise RuntimeError('fixed data producer mismatch')
s=(packet/'FreeMainConditionalOldCarrier.lean').read_text()
for x in ('(hn : n<R) (hRmu : R+1<mu) (hmu : 0<mu)',
          '(hU : U=e*mu) (hdiv : mu∣h) (hks : k=2*n+4*(X*U)*s)',
          '(hold : h+k=U*gamma+(R+1)) : 2*n=R+1',
          'theorem fixed_of_witness (K : ℕ) (v : Fin 14 → V) (gamma : V)',
          'v 13+(v 10+v 11)=(Y*Y)*gamma+(FreeMainAuxNorm.rank p v+1)',
          'FreeMainFixedCompactCarrierCancel.fixed_data K v hv hz',
          'index_eq_of_witness (Y*Y) X R n k (v 13) gamma e mu s',
          'exact ⟨n,s,hn,hn2,hnx,hny,hks,heq⟩'):
    if x not in s:raise RuntimeError('hypothesis or same-index flow changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'scope':'explicit supplied old-carrier gamma equation; same index; captured ancestry'},sort_keys=True))
