#!/usr/bin/env python3
"""Generate an uncompiled natural witness constructor for the frozen 54 seed."""
import json,hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];source=D/'research/nine-sharing-quartic65-54-candidate/seed.json';raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()=='d3bc360e995a3cd617e43b905875de9db2d4b1a1e4257b4bbc6460e95330fcbc';d=json.loads(raw);ports={'beta':0,'K0':1,'MC':2,'MF':3}
def term(t,known):
 k=t[0]
 if k=='num':return f'({t[1]} : S)'
 if k=='port':return f'(ports {ports[t[1]]})'
 if k=='var':
  i=t[1];assert 1<=i<=54
  if i<=14:return f'(u {i-1})'
  assert i in known;return f'w{i}'
 assert k in ('add','mul');return f'({term(t[1],known)} '+('+' if k=='add' else '*')+f' {term(t[2],known)})'
known=set();lines=[]
for residual in d['residuals']:
 if residual['kind']=='output':continue
 t=residual['expr'];assert t[0]=='sub' and t[1][0]=='var';i=t[1][1];assert i>=15 and i not in known;rhs=term(t[2],known);lines.append(f'  let w{i} : S := {rhs}');known.add(i)
assert known==set(range(15,55)) and len(lines)==40
vals=[f'u {i}' for i in range(14)]+[f'w{i}' for i in range(15,55)]
text='''import DiophantineConsistency.SharingGateModel

/-! UNCOMPILED DRAFT. A forward witness constructor generated from the exact
54-witness candidate. Its residual-correctness theorem and the all-model
reverse bridge have not yet been proved or checked. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingForward54

/-- Every cut witness is a semiring expression in earlier witnesses and inputs. -/
def witnessCoordinates {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (u : Fin 14 → S) : Fin 54 → S :=
'''+ '\n'.join(lines)+'\n  !['+', '.join(vals)+''']

end DiophantineConsistency.SharingForward54
'''
out=P/'ForwardWitness54.lean';assert not out.exists();out.write_text(text);print('seed_sha256',hashlib.sha256(raw).hexdigest(),'source_sha256',hashlib.sha256(text.encode()).hexdigest(),'cut_coordinates',len(lines))
