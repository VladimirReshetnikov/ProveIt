"""Exact endpoint bracket for the product-envelope critical radius."""
from fractions import Fraction
from pathlib import Path
import contextlib,importlib.util,io,json,sys
p=Path(__file__).with_name('verify_green_half.py')
spec=importlib.util.spec_from_file_location('envelope_scalar_verifier',p)
v=importlib.util.module_from_spec(spec);sys.modules[spec.name]=v
with contextlib.redirect_stdout(io.StringIO()):spec.loader.exec_module(v)
v.K=64
left=Fraction(573537286334,10**12);right=Fraction(573537286335,10**12)
rows=[]
for r in [left,right]:
 v.r=r;z=v.hp(Fraction(1,2))
 rows.append({'radius':str(r),'ellprime_half_interval':[str(Fraction(z.lo,v.S)),str(Fraction(z.hi,v.S))]})
 if r==left:v.need(z.hi<0,'left endpoint negative')
 else:v.need(z.lo>0,'right endpoint positive')
out={'root_interval':[str(left),str(right)],'unique_root_proved_analytically':True,'exact_sign_evaluations':rows,'all_comparisons_exact':True}
Path(__file__).with_name('envelope_threshold_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
