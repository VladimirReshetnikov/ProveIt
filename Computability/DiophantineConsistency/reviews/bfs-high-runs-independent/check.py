#!/usr/bin/env python3
"""Audit generic high digit run offsets and Lean receipt; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-bfs-high-runs';S=P/'BFSHighRunsV2.lean';O=P/'observations/attempt02';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert t['status']=='PASS' and t['exit']==0 and t['reason'] is None and sha(S)==t['source_sha256']=='47880b6dfd52870835bf05a935be89f5148469e296d2445fca14545700f32319' and sha(P/'run-v2.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='9864ee2d0d90c6b6cc5db02b9cbf205f712e1e6b3e80855b68a8a96a3ffc7d3f'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256'] and (O/'stdout').read_text()=="'BFSHighRuns.expansion' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (O/'stderr').read_text()
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSHighGeneric'] and not re.search(r'\b(?:sorry|admit)\b',s)
assert 'theorem expansion (B a b c : ℕ)' in s and 'Nat.ofDigits B (runs a b c)' in s
runtext=s.split('def runs (a b c : ℕ) : List ℕ :=',1)[1].split('theorem expansion',1)[0];expected_run='[4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++ List.replicate 42 0 ++ List.replicate 9 1 ++ List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++ List.replicate 1096 0 ++ [a] ++ List.replicate 1101 0 ++ [a] ++ List.replicate 3296 0 ++ List.replicate 13 b ++ [c,0]';assert ''.join(runtext.split())==''.join(expected_run.split())
runs=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+['a']+[0]*1101+['a']+[0]*3296+['b']*13+['c',0]
assert len(runs)==8807
assert [i for i,x in enumerate(runs) if x==1]==list(range(1013,1023))+list(range(1065,1074))+[2195,3296]
assert [i for i,x in enumerate(runs) if x=='a']==[4393,5495] and [i for i,x in enumerate(runs) if x=='b']==list(range(8792,8805)) and [i for i,x in enumerate(runs) if x=='c']==[8805] and runs[0]==4 and runs[-1]==0
for frag in ['B^1013 * (∑ j ∈ range 10, B^j)','B^1065 * (∑ j ∈ range 9, B^j)','B^2195 + B^3296 + B^4393*a + B^5495*a','B^8792 * (b * (∑ j ∈ range 13, B^j)) + B^8805*c']:assert frag in s
provider=Path('/tmp/bfs-high-generic-nsp2g8fz/BFSHighGeneric.olean');assert sha(provider)==t['pins'][str(provider)]['sha256']=='cdb9593b8e095fbe92ecc3d89fef9e7c77c4a98a3b1688b4988d6d48bc7cc1ff'
bad=P/'observations/attempt01';z=json.loads((bad/'terminal.json').read_text());log=(bad/'stdout').read_text()+(bad/'stderr').read_text();assert z['status']=='FAILED' and z['exit']!=0 and 'unsolved goals' in log
print('PASS arbitrary-radix 8807-digit run expansion, exact positions, direct provider and rejected first attempt; no Lean replay')
print('No fixed highNat or PDF coefficient theorem.')
