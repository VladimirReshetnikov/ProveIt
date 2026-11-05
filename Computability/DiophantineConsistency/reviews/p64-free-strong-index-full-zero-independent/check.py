#!/usr/bin/env python3
"""Independent direct-formula verification, without the author's graph interpreter."""
import hashlib,json,math,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here=Path(__file__).resolve().parent; parent=here.parents[1]/'research/p64-free-strong-index-full-zero'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if sha(parent/'check.py')!='788520d4bc47af5c380fb27409cddeb1af0b3d53de3f7fc9efb1048cdf1d7e55' or sha(parent/'result.json')!='a1de22b23a8c5dbf346eda76642c164b4505682244b82c40a54cf06a1d32f8a9':
    raise RuntimeError('author packet drift')
record=json.loads((parent/'result.json').read_text())
# Norm-one Pell powering by bitwise doubling and optional multiply.
# The author uses a general binary pair multiplication routine instead.
def pell_power(base_x,base_y,D,n):
    if base_x*base_x-D*base_y*base_y!=1: raise RuntimeError('not a Pell unit')
    x,y=1,0
    for bit in bin(n)[2:]:
        x,y=2*x*x-1,2*x*y
        if bit=='1':x,y=base_x*x+D*base_y*y,base_y*x+base_x*y
        if max(x.bit_length(),y.bit_length())>400000:raise RuntimeError('Pell operand bound')
    if x*x-D*y*y!=1:raise RuntimeError('Pell norm')
    return x,y
P,U,H,a,n,D=4374,729,759,189,191,36480
t,k=pell_power(8749,2,P*(P+1),11720)
g,c=pell_power(n,1,D,19259)
x,y=pell_power(D,1,D*D-1,561)
if not (x%D==0 and 27*k<c<28*k and c%(n*n)==n*n-1):raise RuntimeError('coordinate preconditions')
V=x//D
if (c+V)%(n*n):raise RuntimeError('L not integral')
L=(c+V)//(n*n)
if U*(g-6-a*c)%H:raise RuntimeError('A not integral')
A=U*(g-6-a*c)//H;B=k-1+A
# Extended Euclid, independently computing U^-1 modulo c.
def egcd(a,b):
    x0,x1=1,0
    while b:
        d,a,b=a//b,b,a%b
        x0,x1=x1,x0-d*x1
    return a,x0
G,inv=egcd(U,c)
if G!=1 or U*inv%c!=1:raise RuntimeError('inverse')
gamma=(B+L)*inv%c; R=B-U*gamma
if not (gamma>0 and R>=40 and (R+L)%c==0):raise RuntimeError('rank, port or T sign')
T=(R+L)//c
beta,J,F,alpha,z,f,I,s,w,eta,zeta,K0,MC,MF=2,1,1,1,2,n,D,1,2,c-27*k,28*k-c,3,R-40,0
if min(J,F,alpha,z,f,I,T,s,w,t,eta,zeta,y,gamma)<=0 or min(beta,K0,MC,MF)<0:
    raise RuntimeError('signs')
# Evaluate the modified graph's formulas directly, with no row interpreter.
q=beta*J+1;Y=q*q*q*s; X=w*q; kk=eta+zeta
cc=kk*Y+eta; aa=Y*(X+1); HH=4*aa+3; delta=aa*aa+HH; uu=Y*Y
rank=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
ell=X*Y*kk*Y; first=t*t-ell*(ell+kk)
carrier=uu*(X+aa*cc)+HH*(uu*gamma-(kk-rank-1))
main=carrier*carrier-uu*uu*(delta*cc*cc+1)
strong=I*I-delta*(f*f-1)
vv=f*f*(cc*T-rank)-cc
aux=delta*(f*f-1)*(vv*vv-y*y)+y*y
transport=(K0+w)*(q-F-alpha)-F-z*(q-1)
output=(first*aux-1)**2+main**2+strong**2+transport**2
if (q,Y,X,kk,cc,aa,HH,delta,uu,rank,vv)!=(3,27,6,k,c,a,H,D,U,R,V):raise RuntimeError('parameter formulas')
if (first,main,strong,aux,transport,output)!=(1,0,0,1,0,0):raise RuntimeError('full residual mismatch')
if not 0<I<c*c:raise RuntimeError('free I unexpectedly divisible')
# Independently check the pinned graph rows against the direct formulas.
graphpath=here.parents[1]/'research/p64-qcube76-independent-y-candidate/graph.json'
if sha(graphpath)!='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c':raise RuntimeError('graph hash')
graph=json.loads(graphpath.read_text()); env={'beta':beta,'K0':K0,'MC':MC,'MF':MF,'J':J,'F':F,'alpha':alpha,'z':z,'f':f,'I':I,'T':T,'s':s,'w':w,'t':t,'eta':eta,'zeta':zeta,'y':y,'gamma':gamma}
removed=0; counted=0
for name,op,left,right in graph['source']:
    if name=='I':
        if [name,op,left,right]!=['I','*','i','c2']:raise RuntimeError('changed I row')
        removed+=1;continue
    if name in env or op not in ('+','-','*'):raise RuntimeError('malformed row')
    left=env[left] if isinstance(left,str) else left
    right=env[right] if isinstance(right,str) else right
    if op=='+': env[name]=left+right
    elif op=='-': env[name]=left-right
    else: env[name]=left*right
    counted+=1
if removed!=1 or counted!=75 or any(env[n]!=v for n,v in [('A0',first),('M',main),('W',strong),('Na',aux),('Lt',transport),('polynomial',output)]):
    raise RuntimeError('pinned graph and direct formulas differ')
def digest(a):return hashlib.sha256(a.to_bytes(max(1,(a.bit_length()+7)//8),'big')).hexdigest()
for name,value in [('c',c),('k',k),('R',R),('gamma',gamma),('T',T)]:
    if digest(value)!=record['key_sha256_unsigned_big_endian'][name]:raise RuntimeError('author hash mismatch: '+name)
if digest(MC)!=record['ports']['MC_sha256_unsigned_big_endian'] or MC.bit_length()!=record['ports']['MC_bits']:
    raise RuntimeError('port hash mismatch')
result={'status':'PASS_DIRECT_FORMULAS','script_sha256':sha(Path(__file__)),
        'author_script_sha256':sha(parent/'check.py'),'author_result_sha256':sha(parent/'result.json'),
        'graph_sha256':sha(graphpath),'checked_graph_rows':counted,'A1':first,'M':main,'W':strong,'Na':aux,'Lt':transport,'output':output,
        'c_bits':c.bit_length(),'I':I,'c_squared_exceeds_I':True,'MC_bits':MC.bit_length(),
        'scope':'Exact modified-graph formula verification at specified ports; no original-graph nonexistence, fixed compact44 equivalence or Lean proof.'}
out=here/'result.json';payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as f:f.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
