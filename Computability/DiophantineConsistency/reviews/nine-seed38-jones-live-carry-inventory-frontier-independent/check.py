#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-live-carry-inventory';r=json.loads((p/'result.json').read_text())
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'check.py')=='d59ff89ef6db686cf105245b60507f97d7708a6bc815114daf34f4b7aab11289' and sha(p/'result.json')=='9797545e8193025d84f169984879161a26b09cc686b6e4fd0e4d24c2d11b9ba5'
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,check=True,timeout=300);assert not x.stderr and x.stdout==(p/'result.json').read_bytes()
prefix=d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean';assert sha(prefix)=='c2d995fcf0287325efcfbd060bed17eefd33a1b481a2b67a20978234614b00fa'
lines=prefix.read_text().splitlines();cons=[set() for _ in range(45)];found=set()
for line in lines:
 m=re.match(r'def d(\d+) : Dag (\d+) := \.snoc d(\d+) ',line)
 if not m:continue
 j,n,prior=map(int,m.groups());assert j==n==prior+1 and 1<=j<=45 and j not in found;found.add(j)
 for i in set(map(int,re.findall(r'\.ref ⟨(\d+), by decide⟩',line))):assert 0<=i<j-1;cons[i].add(j)
assert found==set(range(1,46)) and len(r['rows'])==45
for i,row in enumerate(r['rows']):
 assert row['entry_index']==i and row['birth_prefix']==i+1 and row['consumer_prefixes']==sorted(cons[i]);end=max(cons[i],default=i+1);assert row['last_consumer_prefix']==end and row['one_snoc_steps_to_last_predecessor']==max(0,end-i-2)
assert sum(len(c) for c in cons)==r['distinct_reference_edges']==89 and sum(max(0,max(c,default=i+1)-i-2) for i,c in enumerate(cons))==r['one_snoc_steps_if_built_fresh_shared_per_entry']==403
assert r['rows'][30]['consumer_prefixes']==[32] and r['rows'][30]['one_snoc_steps_to_last_predecessor']==0 and r['rows'][44]['consumer_prefixes']==[]
print(json.dumps({'status':'PASS','scope':'external source-pinned reference/liveness inventory; regex scan is not a verified parser or Lean proof','named_nodes':45,'distinct_consumer_edges':89,'fresh_per_entry_snoc_steps':403},indent=2,sort_keys=True))
