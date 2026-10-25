import json,sys,pathlib
from fractions import Fraction as F
from math import lcm
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));import terminal_elimination as E
from factor_horn import add,V

def kernels(rows):
 piv={};K=[]
 for i,row in enumerate(rows):
  r={m:F(c) for m,c in row.items() if len(m)==2};v={i:F(1)}
  while r:
   m=min(r);c=r[m]
   if m not in piv:
    piv[m]=({n:a/c for n,a in r.items()},{j:a/c for j,a in v.items()});break
   rp,vp=piv[m]
   r={m:a for m,a in add(r,{m:-c*a for m,a in rp.items()}).items() if a}
   v={j:a for j,a in add(v,{j:-c*a for j,a in vp.items()}).items() if a}
  if not r:
   d=lcm(*(a.denominator for a in v.values()));K.append({j:int(a*d) for j,a in v.items()})
 return K
if __name__=='__main__':
 inp=json.loads(pathlib.Path(sys.argv[1]).read_text());rows=[E.normalize(r['terms']) for r in inp['residuals']]
 ks=kernels(rows);print('kernel',len(ks))
 for v in ks:
  print(v);print(add(*[{m:c*v[i] for m,c in r.items()} for i,r in enumerate(rows) if i in v]))
