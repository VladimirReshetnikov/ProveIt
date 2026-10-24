from fractions import Fraction
from itertools import product
from pathlib import Path
import json,random
from norm_dag import evaluate

def ringmul(a,b,radicands):
 out={}
 for i,x in a.items():
  for j,y in b.items():
   coefficient=x*y;overlap=i&j
   while overlap:
    flag=overlap&-overlap;coefficient*=radicands[flag.bit_length()-1];overlap^=flag
   k=i^j;out[k]=out.get(k,0)+coefficient
 return {k:v for k,v in out.items() if v}

def norm(z,radicands):
 a={0:Fraction(z),**{1<<i:Fraction(-1) for i in range(len(radicands))}}
 for i in range(len(radicands)):
  conjugate={k:(-v if k&(1<<i) else v) for k,v in a.items()}
  a=ringmul(a,conjugate,radicands)
  if any(k&(1<<i) for k in a):raise RuntimeError('norm did not eliminate root')
 if any(k for k in a):raise RuntimeError('nonconstant norm')
 return a.get(0,0)

def run():
 rng=random.Random(20261024);results=[]
 for rootcount in [4,5]:
  p=Path(__file__).resolve().parent/f'norm{rootcount}_cleared_dag.json';packet=json.loads(p.read_text());m=2**(rootcount-1)
  for _ in range(80):
   ins={x:rng.randint(-7,7) for x in packet['inputs']}
   if ins['delta']==0:ins['delta']=1
   rad=[Fraction(ins[x]) for x in ['A','B','D','G'][:rootcount-1]]+[Fraction(ins['Cnum'],ins['delta'])]
   expected=norm(ins['z'],rad)*ins['delta']**m
   actual=evaluate(packet,ins)
   if expected.denominator!=1 or expected!=actual:raise RuntimeError((rootcount,ins,expected,actual))
  for _ in range(40):
   roots=[rng.randint(-9,9) for _ in range(rootcount)];delta=rng.randint(1,7)
   ins=dict(zip(['A','B','D','G'][:rootcount-1],[x*x for x in roots[:-1]]))
   ins.update(Cnum=delta*roots[-1]**2,delta=delta,z=sum(roots))
   if evaluate(packet,ins)!=0:raise RuntimeError('explicit root tuple rejected')
  results.append({'roots':rootcount,'exact_fraction_ring_norm_comparisons':80,'explicit_zero_fixtures':40,'live_ops':packet['live_binary_operations']})
 print(json.dumps({'status':'PASS','results':results},indent=2))
 (Path(__file__).resolve().parent/'NORM_DAG_CHECKS.json').write_text(json.dumps({'status':'PASS','results':results},indent=2)+'\n')
if __name__=='__main__':run()
