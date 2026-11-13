#!/usr/bin/env python3
"""Independent same-zero and ring-unit source audit; no Lean."""
from pathlib import Path
from itertools import product
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-74-ownzero-units-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'5de8805dc3b4190b202837c144445ffe371ea995fbe815a4255f3cc3f8bedd38','OwnZeroUnits74.lean':'668fb089dad1ced2867530cb7f95919eb584d49f4aa953903a7e2b6d526de43c','check_source.py':'4186080d8b0075c0f51c7d554121f02f4eea4dc70f10a365cf465af9b771b73d','observation.json':'a76dd35dff82116ccbe7c1590e6a5849a554fd90fb7389cf5208202750463e72'}
tail=b"\nIndependent source review: [74 own-zero guard unit](../../reviews/ordinary14-74-ownzero-units-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='4246382da00716e3e1be5905eb9b0220d8f895d9239a20363d42b7a42f38124c'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
s=(A/'OwnZeroUnits74.lean').read_text(); prod=D/'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean';res=D/'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean';ref=D/'Lean/DiophantineConsistency/Compact44/FreeJ13.lean'
for p,h in [(prod,'26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db'),(res,'368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60'),(ref,'cf8beb3993b1cd716266d7adf06ab9ee4eda5d5a7e4b921072eecc5b31389d01')]:assert sha(p)==h
# Check the same zero/port inputs and the guard position in the reviewed tuple.
for token in ['restricted_residues p v','factor_units_of_zero p beta v hbeta hb hJ hw hs hz hmain haux hstrong','exact h.2.2.2.1','(unit_iff_one _ v).mp (guard_pair_unit p beta v hbeta hb hJ hw hs hz)']:
 assert token in s,token
pt=prod.read_text();before=pt.split('theorem factor_units_of_zero',1)[1].split(':= by',1)[0]
pos=[before.index(x) for x in ['v 8*v 8=','(P74PositiveGuard.graph p).main v).1=','(P74PositiveGuard.graph p).aux v).1=','(P74PositiveGuard.graph p).guardFactor v).1=','(P74PositiveGuard.graph p).strong v).1=']]
assert pos==sorted(pos) and len(set(pos))==5
# Conversion proof is exactly the established generic source proof, modulo spacing.
def unitblock(t):
 x=t.split('theorem unit_iff_one',1)[1].split('\n\n',1)[0]
 return ''.join(x.split())
assert unitblock(s)==unitblock(ref.read_text())
controls=0
for a,b in product(range(41),repeat=2):
 assert (a==b+1)==(a-b==1);controls+=1
units=0
for x in product(range(-2,3),repeat=5):
 a,b,c,d,e=x
 if a*b*c*d*e==1 and a!=-1 and b!=-1 and c!=-1 and e!=-1:
  assert x==(1,1,1,1,1);units+=1
assert units>0
review=D/'reviews/ordinary14-74-factor-residues-independent'
assert sha(review/'check.py')=='d0329b690b1199d8fb07eb2d062fc3563ce2be0c2529991f1a7b0dfba3a18a6f'
assert sha(review/'observation.json')=='ef65ebc3b0116e205dce748ec1a77729e17ba1f2cb7f5c93761e96c72b0a643b'
assert subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],cwd=D,check=True,capture_output=True).stdout==(review/'observation.json').read_bytes()
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source interface and finite signed-unit controls only; no Lean, provider or endpoint','author_pins':pins,'unit_ring_controls':controls,'positive_five_factor_controls':units,'prior_residue_review_replayed':True,'author_receipt_reproduced':True},sort_keys=True,indent=2))
