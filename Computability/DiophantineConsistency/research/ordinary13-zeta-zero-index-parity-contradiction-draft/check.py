from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-zeta-zero-index-parity-contradiction-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
orig=Path('research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src').read_text(); s=(D/'ZetaZeroIndexParity.lean.src').read_text()
for n in ['theorem zeta_zero_contradiction','(hc : c = k + Y * k)','m k hq3 hX hy0 hYq hc hi\' hf ha','⟨(1 + Y) * ycoord','PellOrdinateParityModelDraft.ordinate_mod_two']:
 assert n in s,n
idx=Path('research/ordinary13-eta-zero-p72-index-draft/P72ExactEtaNatural.lean.src').read_text()
assert '(hc : c = η + Y * k)' in idx and 'm = R ∧ 2 * n = R + 1' in idx
# At exact-index parity, k is twice a model natural and c=(1+Y)k is even,
# whereas the main ordinate at odd R is odd. Finite controls illustrate it.
cases=0
for a in range(25):
 D0=(a+1)**2-1;x,y=1,0
 for R in range(1,60):
  x,y=(a+1)*x+D0*y,x+(a+1)*y
  assert y%2==R%2
  if R%2:
   for Y in range(12):
    n=(R+1)//2
    for j in range(12):
     k=2*j;c=(1+Y)*k
     assert c%2==0 and c!=y
     cases+=1
print(json.dumps({'finite_odd_pell_even_c_controls':cases,'general_eta_exact_index_signature_checked':True,'actual_graph_binding_proved':False,'lean_executed':False},sort_keys=True,indent=2))
