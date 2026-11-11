#!/usr/bin/env python3
import gzip, hashlib, itertools, json, subprocess, sys
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2]
p=base/'research/current2011-carrier65-na-shear-obstruction'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for f,h in {'README.md':'016a39a236b479c798f85ead03e4e4afda635bf27a6cdd6b64027adbb85070e1','check.py':'f370b47a543f9c630c3a0d5e8b1ef4bd0095440633e882d368db692f7ec14aed','result.json':'f0074a52774e1977424adf116e7f76d519cb6e4d5f1a9d87a4e9f802247bfcdd'}.items():assert sha(p/f)==h
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=base,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
incoming=base/'research/carrier65-independent/INCOMING_CARRIER65.json'; maintained=base/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'; proof=base/'research/carrier65-independent/PROOF.md'
assert sha(incoming)=='bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7'
assert sha(maintained)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
assert sha(proof)=='53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749'
g=json.loads(incoming.read_text());m=json.loads(maintained.read_text());rows=g['source'];assert rows==m['source'] and len(rows)==65
assert Counter(x[1] for x in rows)=={'+':16,'-':12,'*':37}
ports=m['coefficient_binding']['ports'];assert set(ports)=={'beta','K0','MC','MF'}
for v in ports.values():
 path=maintained.parent/'coefficients'/v['file'];b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==v['gzip_sha256'];raw=gzip.decompress(b);assert hashlib.sha256(raw).hexdigest()==v['raw_sha256'] and len(raw)==v['raw_bytes'] and int.from_bytes(raw,'big')>0
leaves=set(g['witnesses'])|set(ports)
def validate(rr):
 available=set(leaves)
 for n,op,a,b in rr:
  assert n not in available and op in '+-*' and all(isinstance(x,int) or x in available for x in (a,b));available.add(n)
 needed={'polynomial'}
 for n,op,a,b in reversed(rr):
  if n in needed:needed.update([a,b])
 assert all(n in needed for n,_,_,_ in rr)
validate(rows)
rmap={r[0]:r for r in rows}
assert rmap['scaled_Ns']==['scaled_Ns','-','scaled_f2','normalized_S2'] and rmap['scaled_f2']==['scaled_f2','*','Delta','f2'] and rmap['normalized_S']==['normalized_S','*','i','Dc2']
# Directly synthesize and verify a topological, live h=1 schedule.
new=[]
for row in rows:
 if row[0] in ('zqm','Nt'):continue
 new.append(row)
 if row[0]=='Na':new.extend([['na_minus_one','-','Na',1],['z_prime','+','z','na_minus_one'],['zqm','*','z_prime','qm'],rmap['Nt']])
assert len(new)==67;validate(new)
# Dependencies are derived from topology, not author-provided lists.
def deps(symbol):
 d={symbol}
 for n,_,a,b in rows:
  if a in d or b in d:d.add(n)
 return [n for n,_,_,_ in rows[:60] if n in d]
assert deps('y')==['y2','V2minusY2','aux_product','Na'] and deps('z')==['zqm','Nt']
assert all(x not in deps('y') for x in ('normalized_S','V2','Delta','Dc2'))
assert all(x not in deps('i') for x in ('Delta','Dc2','V2'))
# Exhaustive residue cases provide controls on the two parity arguments.
for s,v,y in itertools.product(range(4),repeat=3):
 n=(y*y+s*s*(v*v-y*y))%4; assert n in (0,1) and n==(y*y if s%2==0 else v*v)%4
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'original_live_gates':65,'h_one_live_gates':67,'mod4_cases':64,'scope':'Source-only exact zero-preserving shear and direct-alias obstruction; no smaller circuit, Lean or PDF binding.'},indent=2))
