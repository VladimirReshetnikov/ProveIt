#!/usr/bin/env python3
"""Audit arbitrary-radix high interval-sum theorem and its providers; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ten-positive-80-bfs-high-flat';S=P/'BFSHighFlat.lean';O=P/'observations/attempt01';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='35cf26f4ce4fb1c94606a5c29258a8f62107cc3b27aa4b50bb367874e1c87fa2' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='888308a57a6c5dd2c018f680f8c36d14577d97448c82d764dca46e0389c80f81' and sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='7bd984120f153d8487ea147c7cfc48e7cebad2a410be8fd2170c9f99864c368d'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and (O/'stdout').read_text()=="'BFSHighFlat.expansion' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stderr').read_text()
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSHighRunsV2'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert 'theorem expansion (B a b c : ℕ)' in s and 'Nat.ofDigits B (runs a b c)' in s and 'runs CompactHighPopulation.mu CompactHighPopulation.padding' in s and 'CompactHighPopulation.lastPadding = CompactHighPopulation.highDigits := rfl' in s
for term in ['Ico 1013 1023','Ico 1065 1074','Ico 8792 8805','B^2195 + B^3296','a*(B^4393+B^5495)','c*B^8805']:assert term in s
runs=(R/'ten-positive-80-bfs-high-runs/BFSHighRunsV2.lean').read_text().split('def runs (a b c : ℕ) : List ℕ :=',1)[1].split('theorem expansion',1)[0]
high=(R/'ordinary12-ipra-bridge/compact44-high-population-prototype/CompactHighPopulation.lean').read_text().split('def highDigits : List ℕ :=',1)[1].split('theorem digits_length',1)[0]
for old,new in (('[a]','[mu]'),('13 b','13 padding'),('[c,0]','[lastPadding,0]')):runs=runs.replace(old,new)
assert ''.join(runs.split())==''.join(high.split())
provider=Path('/tmp/bfs-high-runs-95e4auty/BFSHighRunsV2.olean');assert sha(provider)==t['pins'][str(provider)]['sha256']=='9864ee2d0d90c6b6cc5db02b9cbf205f712e1e6b3e80855b68a8a96a3ffc7d3f'
print('PASS arbitrary-radix interval sums and exact highDigits run source identity; selected provider pinned; no Lean replay')
print('No fixed highNat/iPRA/PDF-file binding theorem.')
