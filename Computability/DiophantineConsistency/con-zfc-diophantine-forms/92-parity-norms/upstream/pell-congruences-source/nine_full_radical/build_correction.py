"""Regenerate the compact correction from the explicit majorant table."""
from pathlib import Path
import json,math,collections
import laurent_symbolic as p
R=Path(__file__).resolve().parent
def main():
 A,C,i,t,D,e,F,L,G,H,DF,I=p.expr_setup();mul=p.mul;add=p.add;sc=p.scale;sq=lambda x:mul(x,x);one=p.const(1)
 Ns=add(sc(G,2),L);N1=add(sc(mul(mul(mul(sq(e),D),add(D,one,-1)),L),2),sc(C,3))
 N2=sc(mul(mul(sq(e),add(D,one,-1)),L),2);N3=sc(mul(sq(e),add(L,C,-1)),2);N4=sc(mul(sq(e),C),2)
 inside=mul(add(add(sc(sq(D),2048),sc(D,-1024)),p.const(-256)),Ns)
 for pol,k in [(N1,-128),(N2,-80),(N3,-56),(N4,-42)]:inside=add(inside,sc(pol,k))
 inside=add(inside,mul(sq(i),add(add(p.const(1568),sc(A,-448)),sc(C,288))))
 oldcore=mul(e,inside)
 raw=json.loads((R/'laurent_candidate.json').read_text());T0={tuple(m):int(c)for m,c in raw['majorant']}
 correction=add(sc(mul(oldcore,H),16,(0,7,0,0)),T0,-1)
 out=collections.defaultdict(int)
 # Replace A^2 by (D+C^2-1)/C^2; all required C exponents are nonnegative.
 for (a,c,i,t),v in correction.items():
  half=a//2
  if c<2*half:raise ValueError('unexpected denominator')
  for k in range(half+1):
   for ell in range(half-k+1):out[a%2,c-2*half+2*ell,i,t,k]+=v*math.comb(half,k)*math.comb(half-k,ell)*(-1)**(half-k-ell)
 final=collections.defaultdict(int)
 # Multiply the whole majorant by4; then A=(J+5)/4 has no denominators.
 for (a,c,i,t,d),v in out.items():
  if a==0:final[0,c,i,t,d]+=4*v
  else:final[1,c,i,t,d]+=v;final[0,c,i,t,d]+=5*v
 final={m:v for m,v in final.items()if v}
 (R/'laurent_correction_nopad_4JDbasis.json').write_text(json.dumps([[list(m),str(v)]for m,v in sorted(final.items())]))
 print('Correction records:',len(final))
if __name__=='__main__':main()
