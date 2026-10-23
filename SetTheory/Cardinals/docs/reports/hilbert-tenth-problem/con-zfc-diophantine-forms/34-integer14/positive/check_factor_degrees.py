"""New independent formal-Laurent diagnostic of the exact degree table."""
import json
from pathlib import Path
H=Path(__file__).resolve().parent
p=65521
LO=-60

def add(x,y):
 z=dict(x)
 for k,v in y.items():z[k]=(z.get(k,0)+v)%p
 return {k:v for k,v in z.items() if v}
def scale(x,c):return {k:v*c%p for k,v in x.items() if v*c%p}
def mul(x,y):
 z={}
 for i,a in x.items():
  for j,b in y.items():
   if i+j>=LO:z[i+j]=(z.get(i+j,0)+a*b)%p
 return {k:v for k,v in z.items() if v}
def sq(x):return mul(x,x)
def sub(x,y):return add(x,scale(y,-1))
def root(x,lead):
 d=max(x)//2;r=[lead%p];inv=pow(2*r[0],-1,p)
 for n in range(1,61):
  r.append((x.get(2*d-n,0)-sum(r[j]*r[n-j] for j in range(1,n)))*inv%p)
 out={d-n:v for n,v in enumerate(r) if v}
 # The first61 coefficients of the square recover those of x.
 check=sq(out)
 assert all(check.get(2*d-n,0)==x.get(2*d-n,0) for n in range(61))
 return out

def main():
 if not __debug__:raise SystemExit("Assertions must remain enabled.")
 result={}
 expected={'b':[130]*4+[128]*4,'ac':[130]*4+[128]*2+[124]*2,'ac2':[130]*4+[128]*2+[120]*2,'half':[130]*4+[128]*2+[119]*2,'half_aux':[130]*4+[128]*2+[119,118]}
 for kind in expected:
  packet=json.loads((H/f'positive12_shift_{kind}_product.json').read_text())
  # Independent diagonal affine specialization with small fixed coefficients.
  vals={n:{1:i+2,0:2*i+3} for i,n in enumerate(packet['witnesses'])}
  vals.update({n:{0:i+5} for i,n in enumerate(packet['fixed_numerals'])})
  def get(x):return vals[x] if isinstance(x,str) else {0:x%p}
  for n,o,a,b in packet['source']:
   vals[n]= {'+':add,'-':sub,'*':mul}[o](get(a),get(b))
   if n=='W':break
  # A and G have ell² as highestform; D has (aI)².
  lead=lambda n:vals[n][max(vals[n])]
  ra=root(vals['A'],lead('ell'));rg=root(vals['G'],lead('ell'));rf=root(vals['D'],lead('a')*lead('I'))
  B=scale(mul(mul(mul(vals['Q'],vals['c']),vals['T']),vals['b']),2)
  e=sub(add(vals['P'],vals['U']),{0:1});h2=sq(vals['H']);degrees=[]
  for sa in [-1,1]:
   for sg in [-1,1]:
    Z=sub(sub(vals['W'],scale(mul(vals['HM'],ra),sa)),scale(mul(vals['L'],rg),sg))
    for sf in [-1,1]:
     factor=add(sub(mul(vals['d'],sq(Z)),mul(h2,e)),scale(mul(mul(h2,B),rf),sf))
     degrees.append(max(factor))
  assert sorted(degrees)==sorted(expected[kind]),(kind,degrees)
  result[kind]={'eight_factor_degrees':degrees,'norm_degree':sum(degrees),'prime':p,'scope':'Exact finite-field formal-Laurent diagnostic; mathematical uniform proof is separate.'}
 (H/'FACTOR_DEGREES.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
