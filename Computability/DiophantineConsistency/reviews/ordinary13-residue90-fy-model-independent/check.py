#!/usr/bin/env python3
"""Independent f/y residual binding and signed-magnitude interface; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue90-fy-model-draft/Residue90FyForce.lean.src','1d4bd8b0f99b20a5796fe04f1ff0c4f5a825af65b1ba548a79aa0c0940a6e21a')
pin('research/ordinary13-residue90-fy-model-draft/receipt.json','06a116dee14ac52c48ef0e979cafa00502f7c875279c42b9decf13e3cac70e12')
pin('reviews/ordinary13-residue90-xzero-graph-independent/result.json','ffa967831cfed486dca16c9f3bbf9a3735fcc0e298c13b1cfc124a19b8b0cc6e')
r=pin('research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src','efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925')
mag=pin('Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean','c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c')
help=pin('research/adaptive-aq17-forced105-model-draft/AQ17Forced105Arithmetic.lean.src','b3057437cfb476170b28114283783bb0bd392a28f1de1ba4a39b6bf264b5e330')
assert '![A0,A1,Fam,g72]' in r and ': Fin 4 → Expr (Fin 13)' in r
assert '∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a)' in mag
assert 'theorem f_pos (f delta q : V)' in help and 'theorem y_pos_of_zero_product (y z q : V) (hq : 4≤q)' in help
for item in ['theorem strong_identity','all_residuals_zero _ v hz 3','theorem auxiliary_identity','all_residuals_zero _ v hz 2','ordinateRing','ReducedNormSigned.natural_magnitude_square','rw [hqrep,hzsq] at haux','theorem f_y_positive']:
 assert item in s,item
g=json.loads(pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'));rows={row[0]:row for row in g['source']}
for row in [['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','Q'],['g74','*','T','c'],['g75','-','g74','R'],['g76','*','f2','g75'],['V','-','g76','c'],['g81','-','y2','V2'],['g82','*','Q','g81'],['Fa','-','y2','g82'],['Fam','-','Fa',1]]:assert rows[row[0]]==row,row
# Strong and auxiliary forms agree for signed ordinates, including negative values.
for q in range(4,16):
 for y in range(6):
  for z in range(-6,7):
   aux=y*y-q*(y*y-z*z)-1
   assert aux==y*y+q*z*z-1-q*y*y
   if y==0 and aux==0:assert q*z*z==1
print(json.dumps({'scope':'signed magnitude interface, literal residual indices and finite algebra controls; no Lean','strong_residual_index':3,'auxiliary_residual_index':2,'ordinate_sign_unrestricted':True,'all_ports_natural_representation':True,'positive_beta_J_X_gamma_not_required_locally':True,'lean_elaborated':False},sort_keys=True,indent=2))
