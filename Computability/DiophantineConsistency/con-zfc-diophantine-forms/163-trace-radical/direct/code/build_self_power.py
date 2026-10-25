from pathlib import Path
import sys,json,copy
BASE=Path(__file__).resolve().parent.parent/'inherited/factorial_free/direct'
sys.path.insert(0,str(BASE/'parent/code'))
sys.path.insert(0,str(BASE))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T
import build_affine as A
OUT=Path(__file__).resolve().parent.parent/'lineage/self_power'
OUT.mkdir(parents=True,exist_ok=True)
old=json.loads((BASE/'factorial_free_affine/raw_source.json').read_text())
new=copy.deepcopy(old)
names={v['name']:i for i,v in enumerate(new['variables'])}
t,d=names['t0'],names['growth.power_base']
hits=[i for i,r in enumerate(new['residuals']) if r['label']=='growth.base_definition']
if len(hits)!=1:raise ValueError(hits)
ri=hits[0]
new['residuals'][ri]['terms']=E.as_terms({(d,):1,(t,):-1,():-16})
new['variant']='self_power_t_to_t'
fac,fc=F.transform(new)
pr,pc,m=E.optimize(fac,max_support=16)
E.verify(fac,pr,pc)
op=json.loads((BASE/'parent/data/projected.json').read_text())
ot=json.loads((BASE/'parent/equation/translation_certificate.json').read_text())
byname={op['variables'][i]['name']:s for i,s in ot['shifts']}
shifts={i:byname[v['name']] for i,v in enumerate(pr['variables']) if v['name'] in byname}
eq=T.translate(pr,shifts)
for name,obj in [('raw_source.json',new),('source_edit.json',{'row':ri,'old':old['residuals'][ri],'new':new['residuals'][ri]}),('factored_source.json',fac),('factorization_certificate.json',fc),('projected.json',pr),('projection_certificate.json',pc),('translation_certificate.json',{'convention':'old=new+shift','shifts':sorted(shifts.items())}),('equation.json',eq)]:
 (OUT/name).write_bytes(E.canonical_bytes(obj))
print('initial',len(eq['variables']),len(eq['residuals']))
for end in ['241','242']:
 cert=json.loads((BASE/f'factorial_free_affine{end}_balanced/certificate.json').read_text())
 oldeq=json.loads((BASE/'factorial_free_affine/equation.json').read_text())
 print('same names', [v['name'] for v in oldeq['variables']]==[v['name'] for v in eq['variables']])
 # The existing certificate remains valid if its exact projection rows were untouched.
 try:
  neq,p,met=A.construct(eq,cert)
 except Exception as error:
  print('certificate failed',end,error)
  continue
 pth=OUT/('affine'+end);pth.mkdir(exist_ok=True)
 for name,obj in [('equation.json',neq),('expanded_polynomial.json',p),('certificate.json',cert),('METRICS.json',met)]:
  (pth/name).write_bytes(E.canonical_bytes(obj))
 print(end,met)
