#!/usr/bin/env python3
"""Check both uncompiled forward witness constructors against frozen seed ASTs."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];ports={'beta':0,'K0':1,'MC':2,'MF':3}
def term(t,seen,limit):
 k=t[0]
 if k=='num':return f'({t[1]} : S)'
 if k=='port':return f'(ports {ports[t[1]]})'
 if k=='var':
  i=t[1];assert 1<=i<=limit
  if i<=14:return f'(u {i-1})'
  assert i in seen;return f'w{i}'
 assert k in ('add','mul');return f'({term(t[1],seen,limit)} '+('+' if k=='add' else '*')+f' {term(t[2],seen,limit)})'
results={}
for limit,pin in [(54,'d3bc360e995a3cd617e43b905875de9db2d4b1a1e4257b4bbc6460e95330fcbc'),(52,'db5fc39eb7c8075ff7417b084a0c9a4755b497b1be388fe9d0aa1e65bad356ff')]:
 source=D/f'research/nine-sharing-quartic65-{limit}-candidate/seed.json';raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()==pin;d=json.loads(raw);src=(P/f'ForwardWitness{limit}.lean').read_text();assert 'UNCOMPILED DRAFT' in src;seen=set();expected=[]
 for x in d['residuals']:
  if x['kind']=='output':continue
  t=x['expr'];assert t[0]=='sub' and t[1][0]=='var';i=t[1][1];assert i not in seen;expected.append(f'  let w{i} : S := '+term(t[2],seen,limit));seen.add(i)
 actual=[x for x in src.splitlines() if re.match(r'^  let w\d+ : S := ',x)];assert actual==expected and seen==set(range(15,limit+1));vals=[f'u {i}' for i in range(14)]+[f'w{i}' for i in range(15,limit+1)];assert '  !['+', '.join(vals)+']' in src
 results[str(limit)]={'coordinates':limit,'cut_assignments':len(seen),'source_sha256':hashlib.sha256(src.encode()).hexdigest()}
print(json.dumps({'status':'PASS_FORWARD_WITNESS_TRANSCRIPTION_ONLY','constructors':results,'scope':'Both forward constructor texts follow frozen residual ASTs; generic Lean algebra and reverse model bridge remain uncompiled.'},indent=2,sort_keys=True))
