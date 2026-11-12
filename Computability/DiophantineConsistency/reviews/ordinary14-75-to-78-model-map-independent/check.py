#!/usr/bin/env python3
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-75-to-78-model-map-draft'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'2fa5c7e8889afd537dac500effd1fb1f3b39b08b65ec8f43a140289ba39872fd',A/'Model75To78.lean':'c4315f65bed66e551c791ac11f706d3156d23b21b8256aa4b8c52384ed13ace8',A/'check_source.py':'5ddae3ec6ae96025690568ee3192fb7cc4f1915c735c90873e492e688b16fbae',A/'observation.json':'18a6005ad0fced78eb09b5f8877cbf606be57b0e85a496da487aecad29291ccf'}
tail=b"\nIndependent source review: [75 to 78 model map](../../reviews/ordinary14-75-to-78-model-map-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='592022806a9080818c6da9ac2abf83cf6f94f3655a063450fe28defc338325e3'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
s=(A/'Model75To78.lean').read_text()
for t in ('Positive75To74Draft.forward v','Positive75To74Draft.forward_positive v hv','Ring75To74Draft.output_eval p','Positive75To74Draft.cast_forward v','restricted_residues p w','factor_units_of_zero p beta w hbeta hb','hwzero hmain haux hstrong','unit_iff_one','Ring75To74Draft.restricted_eval p','Ring75To74Draft.guard_eval p','Ring78To75Draft.factor_evals p z','fiveSquares_eq_zero_iff'):
 assert t in s,t
checks=0;ones=0
for A0,A1,aux,gap,guard in product(range(-2,3),repeat=5):
 factors=(1+A0,1+A1,aux,1+gap,1+guard)
 if all(x==1 for x in factors):
  assert A0*A0+A1*A1+(aux-1)**2+gap*gap+guard*guard==0;ones+=1
 checks+=1
assert ones==1
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source interface and finite factors only; no Lean or endpoint','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'factor_controls':checks,'all_units_cases':ones,'author_receipt_replayed':True},sort_keys=True,indent=2))
