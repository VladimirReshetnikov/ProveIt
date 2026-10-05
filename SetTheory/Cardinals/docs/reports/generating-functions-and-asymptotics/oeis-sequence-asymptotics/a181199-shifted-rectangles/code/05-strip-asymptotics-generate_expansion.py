"""Exact dominant-sector coefficients from the proved formal Gaussian recipe.
Use --order K; optionally --height m to specialize before Gaussian evaluation.
"""
from functools import lru_cache
from pathlib import Path
import argparse,json,sympy as s
ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=3);ap.add_argument('--height',type=int);args=ap.parse_args()
K=args.order
if K<0:raise RuntimeError('Nonnegative order required')
if args.height is not None and args.height<2:raise RuntimeError('Height at least2 required')
m=s.Integer(args.height) if args.height is not None else s.Symbol('m',positive=True)
S={0:m,1:s.Integer(0)}
for i in range(2,2*K+3):S[i]=s.Symbol('S'+str(i))
@lru_cache(None)
def moment(powers):
    if 1 in powers:return s.Integer(0)
    z=powers.count(0)
    if z:return s.factor(m**z*moment(tuple(x for x in powers if x)))
    if not powers:return s.Integer(1)
    ell=powers[-1];rest=list(powers[:-1]);v=0
    for a in range(ell-1):v+=moment(tuple(sorted(rest+[a,ell-2-a])))
    v-=(ell-1)*moment(tuple(sorted(rest+[ell-2])))/m
    for index,j in enumerate(rest):
        other=rest[:index]+rest[index+1:]
        v+=j*(moment(tuple(sorted(other+[ell+j-2])))-moment(tuple(sorted(other+[ell-1,j-1])))/m)
    return s.factor(v/4)

def expect(poly):
    syms=tuple(S[i] for i in range(2,2*K+3));out=0
    for ex,v in s.Poly(s.expand(poly),*syms).terms():
        powers=tuple(i for i,e in enumerate(ex,start=2) for _ in range(e))
        out+=v*moment(powers)
    return s.factor(out)
L={a:-s.Rational(2**(2*a+2),(2*a+2)*(2*a+1))*S[2*a+2]+s.Rational(2**(2*a-1),a)*S[2*a]+(sum(s.binomial(2*a,j)*S[j]*S[2*a-j] for j in range(2*a+1))-2**(2*a)*S[2*a])/(2*a) for a in range(1,K+1)}
for k in range(1,(K+1)//2+1):
    power=2*k-1;bk=s.bernoulli(2*k)/(2*k*(2*k-1))
    L[power]+=bk*2**(2*k)*(m**(1-2*k)-m)
    for j in range(1,K-power+1):L[power+j]-=bk*2**(2*k)*s.binomial(2*k+2*j-2,2*j)*4**j*S[2*j]
H={0:s.Integer(1)};coeff=[]
for n in range(1,K+1):
    H[n]=s.expand(sum(k*L[k]*H[n-k] for k in range(1,n+1))/n)
    c=expect(H[n]);coeff.append(str(c));print('c'+str(n)+' = '+str(c),flush=True)
if K>=1 and s.factor(s.sympify(coeff[0],locals={'m':m})-(m*m-1)**2/(12*m))!=0:raise RuntimeError('First coefficient')
if K>=2 and s.factor(s.sympify(coeff[1],locals={'m':m})-(m*m-1)*(m**6+3*m*m-1)/(288*m*m))!=0:raise RuntimeError('Second coefficient')
out={'height':args.height,'order':K,'coefficients':coeff,'method':'formal central-binomial/pair-denominator expansion and trace-zero Ward recurrence'}
target=Path(__file__).with_name('expansion_'+(str(args.height) if args.height is not None else 'symbolic')+'_'+str(K)+'.json');target.write_text(json.dumps(out,indent=2)+'\n')
