#!/usr/bin/env python3
"""Audit generic first-index comparison artifacts without Lean replay."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-first-index-comparison-draft'
obs=packet/'observations/attempt02'
out=Path('/tmp/p64-qcube72-first-index-comparison-priority-check02')
pins={packet/'FreeMainFirstIndexComparison.lean':'05a40cc42e40d229e3b18cc57b8585268488858ec8fa1e10465c4e1b25d64788',
 packet/'check02.py':'24ca5c3887d0f45073db05c4626d65743721933724e44d34da17178ef928664e',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'4e423a199a364400cd913793d46b7a78a10220f4b920d603dc247fdc29a1a61f',
 obs/'result.json':'4b2a609261cd30840ec9490e5b37f1155864f480105af706d247448dd05f6322',
 out/'FreeMainFirstIndexComparison.olean':'b047e0649391b7f65d2b2ec83d4f8fda46566adcc22abf8bd38f4bd566a3f6d6'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h: raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes(): raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True): raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']: raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check02.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainFirstIndexComparison.olean']):
    raise RuntimeError('receipt hashes disagree')
if (obs/'compile.log').read_text().strip()!="'FreeMainFirstIndexComparison.first_lt_main' depends on axioms: [propext, Classical.choice, Quot.sound]":
    raise RuntimeError('unexpected compiler log')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink(): raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
provider='/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/ArithmeticAdaptiveIndexComparison2011.olean'
if r['guards_after'][provider]['sha256']!='68a74e1f4701b20224dc573e00e00f7a989d8a1687c7b4cff447e10abfe2b27c':
    raise RuntimeError('captured provider mismatch')
s=(packet/'FreeMainFirstIndexComparison.lean').read_text()
for x in ('(hX : 0<X) (hY : 2≤Y) (heta : 0<eta)',
          '(hfirst : 2*ycoord n (2*((X*Y)*Y-1)+1)=k)',
          '(hmain : ycoord m (X*Y+Y)=k*Y+eta) : n<m',
          '(y_strictMono a).monotone hm', '(base_mono a B hab n).2'):
    if x not in s: raise RuntimeError('theorem scope changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
                 'scope':'generic coordinate hypotheses; captured comparison provider; inherited ancestry'},sort_keys=True))
