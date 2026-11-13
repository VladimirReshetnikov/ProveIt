from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-q2-scale60-divisibility-cut')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text());g=json.loads((D/'candidate.json').read_text())
assert g['witnesses']==p['witnesses'] and g['fixed_numerals']==p['fixed_numerals'] and g['domain']==p['domain']=='nonnegative integers'
expected=[(['Y','*','q2','s'] if r[0]=='Y' else r) for r in p['source'] if r[0]!='q3']
assert g['source']==expected and len(g['source'])==60 and len(p['source'])==61
leaves=set(g['fixed_numerals']+g['witnesses']); rows={}
for name,op,a,b in g['source']:
 assert name not in rows and name not in leaves and op in '+-*'
 assert all(isinstance(x,int) or x in leaves or x in rows for x in (a,b))
 rows[name]=(a,b)
live=set();used=set()
def walk(x):
 if isinstance(x,int):return
 if x not in rows:used.add(x);return
 if x in live:return
 live.add(x)
 for y in rows[x]:walk(y)
walk(g['output']);assert len(live)==60 and used==leaves

def ev(graph,ins):
 v=ins.copy()
 for name,op,a,b in graph['source']:
  a=a if isinstance(a,int) else v[a];b=b if isinstance(b,int) else v[b]
  v[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return v
# Sample evaluations support, but do not replace, the algebraic proof of the map.
for beta in range(4):
 for j in range(3):
  for s0 in range(3):
   i=dict(zip(p['fixed_numerals']+p['witnesses'],[beta,2,1,3,j,2,1,2,s0,2,3,1,2,1]));q=1+beta*j
   a=ev(p,i); ii=i|{'n_s':q*(s0+1)-1};b=ev(g,ii)
   assert all(a[r[0]]==b[r[0]] for r in g['source'] if r[0]!='s')
   assert (ii['n_s']+1)%q==0 and (ii['n_s']+1)//q-1==s0
# Partial zero with q not dividing s: first and carrier residuals alone cannot prove the cut.
i=dict(zip(g['fixed_numerals']+g['witnesses'],[2,1,0,0,1,0,0,2,0,3,973,0,1,0]));v=ev(g,i)
assert v['q']==3 and v['s']==1 and v['Y']==9 and v['Bres']==0 and v['firstres']==0
assert v['s']%v['q']!=0 and v['A1']!=0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'candidate_sha256':sha256((D/'candidate.json').read_bytes()).hexdigest(),
 'candidate_live_operations':len(live),'witnesses':len(g['witnesses']),
 'source_delta_exact':True,'partial_zero_has_nondivisible_s':True,
 'partial_zero_main_residual_nonzero':True,'unconditional_zero_equivalence_proved':False,'lean_executed':False},indent=2,sort_keys=True))
