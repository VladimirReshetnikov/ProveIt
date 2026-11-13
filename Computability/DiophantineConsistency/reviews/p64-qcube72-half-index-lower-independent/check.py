#!/usr/bin/env python3
"""Audit generic Pell half-index bound artifacts without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-half-index-lower-draft'
obs=packet/'observations/attempt04'
out=Path('/tmp/p64-qcube72-half-index-lower-priority-check04')
pins={packet/'FreeMainHalfIndexLower.lean':'de70b6754ba9e28615f565d545b9eed0031f40e38fd12e0c4724bf8356298874',
 packet/'check04.py':'2c4c5b794b3d32ac5637b7657796c882f24d7c1e77c03bff885a0c677341cb5e',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'04f147e9114c924bdeff1cc074ba52d341f85f98a48b5feac09861aba112093b',
 obs/'result.json':'7700a73f610d45a221ff8fa135b14af2fa5b6328fe0f19755ffb6b028a976c38',
 out/'FreeMainHalfIndexLower.olean':'efd15c9bbd3394fbf085518e4f7374a0e0d75013a771872d6700a542c8ad5839'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check04.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainHalfIndexLower.olean']):raise RuntimeError('receipt hash mismatch')
if (obs/'compile.log').read_text().strip()!="'FreeMainHalfIndexLower.main_lt_twice_first' depends on axioms: [propext, Classical.choice, Quot.sound]":raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
providers={
 '/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticAdaptiveIndexComparison2011.olean':'68a74e1f4701b20224dc573e00e00f7a989d8a1687c7b4cff447e10abfe2b27c',
 '/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticPellCommonUnit.olean':'3644d7766d04f809f69abbebcdd72f426cd4ae01d691c99dc698f8db48635209'}
for path,h in providers.items():
    if r['guards_after'][path]['sha256']!=h:raise RuntimeError('captured provider mismatch '+path)
s=(packet/'FreeMainHalfIndexLower.lean').read_text()
for x in ('(hZeta : 0<zeta)',
          '(hfirst : 2*ycoord n (2*((X*Y)*Y-1)+1)=eta+zeta)',
          '(hmain : ycoord m (X*Y+Y)=(eta+zeta)*Y+eta) : m<2*n',
          '(composition A2 a 2 hx2 n).2', 'rwa [hy2] at hh',
          '(base_mono B A2 hAB n).2', '(y_strictMono a).monotone hm'):
    if x not in s:raise RuntimeError('theorem or composition changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'scope':'generic first/main coordinate hypotheses; two captured providers and inherited ancestry'},sort_keys=True))
