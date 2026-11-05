#!/usr/bin/env python3
"""Audit the same-index residue client without invoking Lean."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
packet=root/'research/p64-qcube72-same-first-index-residue-draft'
obs=packet/'observations/attempt01'
out=Path('/tmp/p64-qcube72-same-first-index-residue-priority-check01')
pins={packet/'FreeMainSameFirstIndexResidue.lean':'cfe7d173bca44c10d25bc39fb1175bc560d8f7e3c098cb2f488f823b8560c745',
 packet/'check01.py':'4837efdeb6daa67fb71e6ea3bd8e1ae2117a65c038c50740483bbd010df213ed',
 packet/'missing_child.py':'c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1',
 obs/'compile.log':'a9892d173505ef20be0090a9803dbaac0c4b5de292bc26ceea1e9fb48b854e77',
 obs/'result.json':'d70e9ec84c6f808ae05498f909b160282ff9c1a356564650633e52bbee0c5e58',
 out/'FreeMainSameFirstIndexResidue.olean':'35e42a6ac21791795d2a7cb2c5aa6857203d721168f5f60d6852146b4df871a1'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in pins.items():
    if not p.is_file() or p.is_symlink() or sha(p)!=h:raise RuntimeError('artifact mismatch '+str(p))
for n in ('compile.log','result.json'):
    if (out/n).read_bytes()!=(obs/n).read_bytes():raise RuntimeError('terminal copy mismatch '+n)
r=json.loads((obs/'result.json').read_text())
if (r['status'],r['exit'],r['stop_reason'],r['guards_stable'])!=('PASS',0,None,True):raise RuntimeError('failed receipt')
if r['guards_before']!=r['guards_after'] or not r['group_rss_samples']:raise RuntimeError('guard/sample mismatch')
if (r['runner_sha256'],r['missing_child_helper_sha256'],r['log_sha256'],r['object_sha256'])!=(
 pins[packet/'check01.py'],pins[packet/'missing_child.py'],pins[obs/'compile.log'],pins[out/'FreeMainSameFirstIndexResidue.olean']):raise RuntimeError('receipt hash mismatch')
names=('first_residue','fixed_window_residue')
want='\n'.join(f"'FreeMainSameFirstIndexResidue.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
if (obs/'compile.log').read_text().strip()!=want:raise RuntimeError('compiler log mismatch')
for name,item in r['guards_after'].items():
    p=Path(name)
    if item is None:
        if p.exists() or p.is_symlink():raise RuntimeError('guarded shadow present '+name)
    elif not p.is_file() or str(p.resolve())!=item['realpath'] or sha(p)!=item['sha256']:
        raise RuntimeError('guard mismatch '+name)
provider='/tmp/p64-qcube72-fixed-compact-index-window-priority-check01/FreeMainFixedCompactIndexWindow.olean'
h='7202be120448b67b446f6af2dcc1bb90de67e9fa7cfc527da35cc73165252d44'
producer=json.loads((root/'research/p64-qcube72-fixed-compact-index-window-draft/observations/attempt01/result.json').read_text())
if r['guards_after'][provider]['sha256']!=h or (producer['status'],producer['exit'],producer['object_sha256'])!=('PASS',0,h):
    raise RuntimeError('index-window producer mismatch')
s=(packet/'FreeMainSameFirstIndexResidue.lean').read_text()
for x in ('(hP : 0<P)', '(hny : 2*ycoord n (2*(P-1)+1)=k)',
          'residue_quotients n (2*(P-1)+1) (2*P) hB',
          '∃ n s : V, n<R ∧ R<2*n', 'k=2*n+4*P*s',
          'obtain ⟨n,hn1,hn2,hnx,hny⟩ := FreeMainFixedCompactIndexWindow.first_index_window K v hv hz',
          'obtain ⟨s,hs⟩ := first_residue P k n hP hny', 'exact ⟨n,s,hn1,hn2,hnx,hny,hs⟩'):
    if x not in s:raise RuntimeError('source witness flow or hypothesis changed '+x)
print(json.dumps({'status':'PASS','lean_replayed':False,'guards_checked':len(r['guards_after']),
 'scope':'same model n for fixed-port window, coordinates and residue; inherited captured ancestry'},sort_keys=True))
