#!/usr/bin/env python3
"""Audit generic low-mask theorem and rejected fixed clients without Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ten-positive-80-bfs-low-generic';S=P/'BFSDisplayedLowGeneric.lean';O=P/'observations/attempt01';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='f5bb4d5395aaee39808b297edf64ef83e1e231682968576719a32c5c42e78d16' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='4481f5c5e76c0cebd8ee4cb783c2dc77b2b3d64eb65dd32740536c8e6c9955e0' and sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='4b6de4c0f87b6185110c37cd846f119949835718e663b1bc6096a2a804e73618'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and (O/'stdout').read_text()=="'BFSDisplayedLowGeneric.low_recipe' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stderr').read_text()
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['DiophantineConsistency.CompactConcreteMask'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert '(hB : 4 ≤ B) (hS : S ⊆ range len) (hs : special ∈ S)' in s and 'Nat.ofDigits B (digits B len special S)' in s and 'B^len - 1 - (∑ j ∈ S, B^j) - 2*B^special' in s
provider=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib/DiophantineConsistency/CompactConcreteMask.olean');assert sha(provider)==t['pins'][str(provider)]['sha256']=='741c13117025cac74b3f94eb229f88f764aa101bf3cd9e4af3d4c0c43176cd0b'
Q=R/'ten-positive-80-bfs-displayed-low'
for i in (1,2):
 q=Q/f'observations/attempt{i:02}';z=json.loads((q/'terminal.json').read_text());assert z['status']=='FAILED' and z['exit']!=0 and sha(q/'stdout')==z['stdout_sha256'] and sha(q/'stderr')==z['stderr_sha256']
 log=(q/'stdout').read_text()+(q/'stderr').read_text();assert '(kernel) excessive memory consumption' in log and 'low_eq' in log
 print('rejected',i,'exit',z['exit'],'source',z['source_sha256'],'runner',z['runner_sha256'])
print('PASS generic variable-radix low recipe and direct pin; fixed low-mask specializations remain rejected, no Lean replay')
