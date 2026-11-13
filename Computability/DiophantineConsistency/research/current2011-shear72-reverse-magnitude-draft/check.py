from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-reverse-magnitude-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/current2011-sheared72-46-candidate/polynomial.json').read_text())
assert g['witnesses']==['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
r={v[0]:v for v in g['source']}
expected=[['c2','*','c','c'],['f2','*','f','f'],['f2m1','-','f2',1],['Aaux','*','Delta','f2m1'],['I','*','i','c2'],['I2','*','I','I'],['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux'],['strong_residual','-','I2','Aaux'],['P2','*','N0','N0'],['Na2','*','Na','Na'],['QW','*','N1','Nt'],['rQW','-','QW',1],['rQW2','*','rQW','rQW'],['strong2','*','strong_residual','strong_residual'],['sum1','+','P2','Na2'],['sum2','+','sum1','rQW2'],['sum3','+','sum2','strong2'],['polynomial','-','sum3',2]]
assert all(r[row[0]]==row for row in expected)
s=(D/'Shear72ReverseMagnitude.lean.src').read_text()
for t in ['theorem shifted_ne_zero','theorem natural_bounds','(hd : 1 ≤ d) (hf : 1 ≤ f) (hi : 1 ≤ i) (hc : 2 ≤ c)', 'theorem positive_magnitude','abs_eq_ι z','theorem positive_old_ordinate','0 < yOld ∧ (ι yOld : DiffRing V)^2 = (Vr+ι y)^2','theorem auxiliary_of_same_square']:
    assert t in s,t
count=0
for d in range(1,5):
 for f in range(1,5):
  for i in range(1,4):
   for c in range(2,5):
    for y in range(1,4):
     A=d*(f*f-1);I=i*c*c;V=-y;assert A==0 or A>=2
     for P in range(-3,4):
      for QW in range(-3,4):
       out=P*P+(A*V*V)**2+(QW-1)**2+(I*I-A)**2-2
       assert out>0
       count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'exact_candidate_rows_checked':len(expected),'finite_zero_ordinate_controls':count,'graph_to_model_zero_proved':False,'lean_executed':False},sort_keys=True,indent=2))
