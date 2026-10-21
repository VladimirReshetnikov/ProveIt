"""Replay the fixed 97-row H/K/Peirce-to-S data; no downloaded code execution."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent.parent
path=R/'research217_three_variable_axioms/H_K_P_to_S_certificate.json'
data=json.loads(path.read_text())
def parse(s):
 def at(k):
  if s[k]!='C':return s[k],k+1
  a,k=at(k+1);b,k=at(k);return (a,b),k
 t,k=at(0);assert k==len(s);return t
def put(t,m):return m[t] if isinstance(t,str) else (put(t[0],m),put(t[1],m))
axioms={k:parse(v) for k,v in {'ax-1':'CpCqp','imim1':'CCpqCCqrCpr','peirce':'CCCpqpp'}.items()}
past={};counts={}
for row in data['rows']:
 i=row['id'];t=parse(row['polish']);rule=row['rule'];counts[rule]=counts.get(rule,0)+1
 if rule=='ax-mp':
  j,k=row['parents_minor_major'];assert j<i and k<i
  assert isinstance(past[k],tuple) and past[k][0]==past[j] and past[k][1]==t
 else:
  assert rule in axioms
  inst={k:parse(v) for k,v in row['substitution'].items()}
  assert put(axioms[rule],inst)==t
 past[i]=t
assert len(past)==97 and past[97]==parse('CCpCqrCCpqCpr')
out={'status':'PASS_97_EXPLICIT_ROWS_NATIVE_TRANSPORT','rows':97,'counts':counts,'last':'CCpCqrCCpqCpr',
 'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'received_code_executed':False,'formula_search':False,
 'native_transport':'Universal numeric substitution into I=4P commutes with all displayed schematic instances and exact MP. No general theorem-renaming or object-language substitution rule is used.'}
(R/'research217_native_basis_review/H_K_P_S_NATIVE_REPLAY.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],counts)
