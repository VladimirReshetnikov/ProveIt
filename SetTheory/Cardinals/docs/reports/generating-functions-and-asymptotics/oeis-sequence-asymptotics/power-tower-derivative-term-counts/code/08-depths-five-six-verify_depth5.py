"""Finite rectangle for A290268 depth five, exact integers only."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json,hashlib,time
D,R,Q=5,410,839

def require(test,message):
 if not test:raise ArithmeticError(message)

def column(q,K,depth=5):
 r=2*depth+1+q
 a=[1]+[0]*depth
 for j in range(r):a=[(2*depth-j)*a[i]+(a[i-1] if i else 0) for i in range(depth+1)]
 yield a
 if K==0:return
 b=[(2*depth-q)*a[i]+(2*a[i-1] if i else 0) for i in range(depth+1)]
 yield b
 for k in range(1,K):
  c=[(2*depth-q)*b[i]+(2*b[i-1] if i else 0)+k*(k+r)*a[i] for i in range(depth+1)]
  yield c;a,b=b,c

start=time.time();zeroes=[];count=0;digest=hashlib.sha256();maxbits=0
for q in range(Q):
 for k,jet in enumerate(column(q,R-2)):
  H=jet[5];hole=q==10 and k%2==1
  require((H==0)==hole,f"incorrect zero at {k},{q}")
  count+=1;maxbits=max(maxbits,H.bit_length())
  if hole:zeroes.append([k,q])
  # digest sign and two nonvanishing diagnostics; nonzero is proved by H itself.
  digest.update(f'{k},{q},{(H>0)-(H<0)},{H%1000000007},{H%1000000009}\n'.encode())
center=list(column(10,R))[-1];require(center[1]>0 and center[3]>8*center[1],"central moment seed failed")
Hq=sum((F(1,j) for j in range(1,Q+1)),F(0));S=sum((F(1,j*j) for j in range(1,Q+1)),F(0));H10=sum((F(1,j) for j in range(1,11)),F(0));S10=sum((F(1,j*j) for j in range(1,11)),F(0))
tail=(Hq-H10)**2-S-S10;require(tail>16,"tail moment seed failed")
record={'depth':5,'R':R,'Q':Q,'rectangle_k':[0,R-2],'rectangle_q':[0,Q-1],'cells':count,'holes':len(zeroes),'max_derivative_order':2*(R-2)+11+(Q-1),'digest_sign_and_residues':digest.hexdigest(),'maximum_integer_bits':maxbits,'center_cubic_to_linear_ratio':str(F(center[3],center[1])),'center_ratio_minus_8_positive':True,'tail_rational_minus_16':str(tail-16),'elapsed_seconds':time.time()-start}
Path(__file__).with_name('depth5_certificate.json').write_text(json.dumps(record,indent=2));print(json.dumps({k:v for k,v in record.items() if not isinstance(v,str) or len(v)<200},indent=2))
