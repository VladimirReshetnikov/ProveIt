#!/usr/bin/env python3
"""Verify five retained low specialization failures; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json
D=Path(__file__).resolve().parents[2];R=D/'research'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for root,count in [('ten-positive-80-bfs-low-radix',2),('ten-positive-80-bfs-displayed-low',3)]:
 P=R/root
 for i in range(1,count+1):
  O=P/f'observations/attempt{i:02}';t=json.loads((O/'terminal.json').read_text());assert t['status']=='FAILED' and t['exit']!=0 and '-M3000' in t['command']
  source=Path(t['command'][-3]);assert sha(source)==t['source_sha256'] and sha(O/'stdout')==t['stdout_sha256'] and sha(O/'stderr')==t['stderr_sha256']
  for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
  log=(O/'stdout').read_text()+(O/'stderr').read_text();assert 'excessive memory consumption' in log
  if root.endswith('low-radix'):
   assert 'formula_to_digits' in log
   if i==2:assert 'maximum recursion depth' in log
  else:assert 'low_eq' in log
  print(root,O.name,'FAILED exit',t['exit'],'source',t['source_sha256'],'terminal',sha(O/'terminal.json'))
print('PASS five rejected 3-GiB-cap attempts; no accepted fixed low-mask theorem/client; no Lean replay')
