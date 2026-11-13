#!/usr/bin/env python3
"""Check uncompiled 38-seed constructor text against its frozen residual AST."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];source=D/'research/nine-sharing-quartic65-norm38-candidate/seed.json';raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23';d=json.loads(raw);src=(P/'ForwardWitness38.lean').read_text();assert 'UNCOMPILED DRAFT' in src;ports={'beta':0,'K0':1,'MC':2,'MF':3}
def term(t,seen):
 k=t[0]
 if k=='num':return f'({t[1]} : S)'
 if k=='port':return f'(ports {ports[t[1]]})'
 if k=='var':
  i=t[1];assert 1<=i<=38
  if i<=14:return f'(u {i-1})'
  assert i in seen;return f'w{i}'
 assert k in ('add','mul');return f'({term(t[1],seen)} '+('+' if k=='add' else '*')+f' {term(t[2],seen)})'
seen=set();expected=[]
for x in d['residuals']:
 if x['kind']=='norm':continue
 t=x['expr'];assert t[0]=='sub' and t[1][0]=='var';i=t[1][1];assert i not in seen;expected.append(f'  let w{i} : S := '+term(t[2],seen));seen.add(i)
actual=[x for x in src.splitlines() if re.match(r'^  let w\d+ : S := ',x)];assert actual==expected and seen==set(range(15,39));vals=[f'u {i}' for i in range(14)]+[f'w{i}' for i in range(15,39)];assert '  !['+', '.join(vals)+']' in src
print(json.dumps({'status':'PASS_FORWARD_WITNESS_TRANSCRIPTION_ONLY','coordinates':38,'cut_assignments':len(seen),'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'scope':'Generated semiring constructor matches materialized norm38 gate AST only; five norm residuals and Lean model bridge unproved.'},indent=2,sort_keys=True))
