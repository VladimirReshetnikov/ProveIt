#!/usr/bin/env python3
"""Audit actual-zero compact free-carrier data without invoking Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-fixed-compact-carrier-cancel-draft'
obs=packet/'observations/attempt01'
out=Path('/tmp/p64-qcube72-fixed-compact-carrier-cancel-priority-check01')
pins={packet/'FreeMainFixedCompactCarrierCancel.lean':'902ab9d30f07dcc7cdcca28c6103862aecaf3ce5bed34c979576a8c133d0d70d',
 packet/'check01.py':'7e11bfdbbb151a42701d683d260570e35b6c75391f4f10eb516a524dd7e38289',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'e0ae0e4572ac6c5e8d24945dd2a587d287432731c8c548070f1eafb47446e5b0',
 obs/'result.json':'e24fcbe237a4d47bb162855ab80b45eaddddae235614416ec39450efc8bc3d81',
 out/'FreeMainFixedCompactCarrierCancel.olean':'3dbbbc7253c3c0976f39adf9450d35e8b3280e098641c330268d7a9573b69434'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check01.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainFixedCompactCarrierCancel.olean']):raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainFixedCompactCarrierCancel.fixed_data' depends on axioms: [propext, Classical.choice, Quot.sound]":raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers=[
 ('/tmp/p64-qcube72-same-first-index-residue-priority-check01/FreeMainSameFirstIndexResidue.olean',
  'research/p64-qcube72-same-first-index-residue-draft/observations/attempt01/result.json',
  '35e42a6ac21791795d2a7cb2c5aa6857203d721168f5f60d6852146b4df871a1'),
 ('/tmp/p64-qcube72-free-carrier-cancel-priority-check01/FreeMainCarrierCancel.olean',
  'research/p64-qcube72-free-carrier-cancel-draft/observations/attempt01/result.json',
  'e43083918e775c396704e341db1268495c369a7d7b9b7f01fc207adb90775ef1')]
for path,receipt,h in providers:
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('provider mismatch '+path)
    p=json.loads((root/receipt).read_text())
    if (p['status'],p['exit'],p['object_sha256'])!=('PASS',0,h):raise RuntimeError('producer mismatch '+receipt)
s=(packet/'FreeMainFixedCompactCarrierCancel.lean').read_text()
for x in ('∃ n s e mu : V, n<R ∧ R<2*n ∧',
          'xcoord n (2*(P-1)+1)=v 9 ∧ 2*ycoord n (2*(P-1)+1)=k ∧',
          'k=2*n+4*P*s ∧ 0<e ∧ Y*Y=e*mu ∧ e∣9 ∧ 0<mu ∧',
          'q*(q*(q*q))≤mu ∧ mu∣v 13',
          'FreeMainGraphMainRoot.main_root p v hv hz',
          'FreeMainCarrierCancel.cancel q X Y (v 7) g c (v 13)',
          'FreeMainSameFirstIndexResidue.fixed_window_residue K v hv hz',
          'exact ⟨n,s,e,mu,hn1,hn2,hnx,hny,hks,he,hU,he9,hmu,hbound,hdiv⟩'):
    if x not in s:raise RuntimeError('source witness flow or conclusion changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'direct_producer_receipts':2,'scope':'same actual zero and index, model cancellation witnesses; inherited ancestry'},sort_keys=True))
