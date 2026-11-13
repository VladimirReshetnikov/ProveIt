#!/usr/bin/env python3
"""Partial counterexample to a direct gamma-coordinate inverse; no graph zero."""
import hashlib,json,math,sys
from pathlib import Path
from collections import Counter
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
# Construct only the structural free-main experiment from the pinned parent.
here=Path(__file__).resolve().parent
graph_path=here.parent/'p64-qcube76-independent-y-candidate/graph.json'
raw=graph_path.read_bytes()
if hashlib.sha256(raw).hexdigest()!='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c':
    raise RuntimeError('parent graph drift')
graph=json.loads(raw); removed={'r_plus_one','r','U_gamma','main_gap'}; rows=[]
for row in graph['source']:
    if row[0] in removed: continue
    if row[0]=='H_main_gap':
        if row!=['H_main_gap','*','H','main_gap']: raise RuntimeError('unexpected main gap')
        row=['H_main_gap','*','H','h']
    rows.append(row)
witnesses=list(graph['witnesses'])
if witnesses[13]!='gamma': raise RuntimeError('unexpected witness')
witnesses[13]='h'; known=set(witnesses+graph['fixed_numerals']); deps={}
for name,op,a,b in rows:
    if name in known or any(not isinstance(x,int) and x not in known for x in (a,b)): raise RuntimeError('invalid graph row')
    known.add(name);deps[name]=[x for x in (a,b) if isinstance(x,str)]
seen=set(); todo=[graph['output']]
while todo:
    name=todo.pop()
    if name in seen: continue
    seen.add(name);todo.extend(deps.get(name,[]))
if len(rows)!=72 or len(seen.intersection(deps))!=72 or not set(witnesses+graph['fixed_numerals'])<=seen:
    raise RuntimeError('unexpected free-main graph structure')

# Positive witness and natural port values, with h independent of gamma.
beta,J,F,alpha,z,w,s,eta,zeta=1,3,1,1,1,1,1,4,6
K0,MC,MF=1,0,0
q=beta*J+1; qm=q-1; Y=q**3*s; U=Y*Y; X=w*q
k=eta+zeta; c=k*Y+eta; a=Y*(X+1); H=4*a+3; D=a*a+H
C=q-F-alpha; R=((qm*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J)
transport=(K0+w)*C-F-z*qm
h=U; r=k-R-1; g=2*(a+2)**2-1
if (q,Y,U,X,k,c,a,H,D,C,R,r,h,g)!=(4,64,4096,4,10,644,320,1283,103683,2,150,-141,4096,207367):
    raise RuntimeError('unexpected base parameters')
if min(beta,J,F,alpha,z,w,s,eta,zeta,h)<=0 or min(K0,MC,MF)<0 or transport!=0:
    raise RuntimeError('input signs or transport failed')
if g*g!=1+D*c*c:
    raise RuntimeError('scalar Pell norm failed')
b0=X+a*c; Dstar=U*b0+H*h
if Dstar!=U*g or Dstar*Dstar-U*U*(D*c*c+1)!=0:
    raise RuntimeError('free-main residual failed')
# Take the 644th power of g+c*sqrt(D). Its radical coefficient is
# divisible by c², giving a positive i for the strong norm.
f,cn=1,0
for _ in range(c):
    f,cn=f*g+D*cn*c, f*c+cn*g
    if max(f.bit_length(),cn.bit_length())>20000:
        raise RuntimeError('Pell resource bound exceeded')
if cn%(c*c): raise RuntimeError('strong-witness divisibility failed')
i=D*cn//(c*c)
if min(f,i)<=0 or (i*c*c)**2-D*(f*f-1)!=0:
    raise RuntimeError('strong residual failed')
# Evaluate the actual free-main 72-row DAG at a complete positive tuple;
# t=1 and y=1 are arbitrary here, so the graph is not claimed to vanish.
env={'beta':beta,'K0':K0,'MC':MC,'MF':MF,'J':J,'F':F,'alpha':alpha,'z':z,
     'f':f,'i':i,'T':1,'s':s,'w':w,'t':1,'eta':eta,'zeta':zeta,'y':1,'h':h}
def get(x): return x if isinstance(x,int) else env[x]
for name,op,x,y in rows:
    left,right=get(x),get(y)
    env[name]={'+':lambda:left+right,'-':lambda:left-right,'*':lambda:left*right}[op]()
    if abs(env[name]).bit_length()>200000:
        raise RuntimeError('graph evaluation resource bound exceeded')
if any(env[n]!=0 for n in ('M','W','Lt')) or env['R']!=R:
    raise RuntimeError('graph residual mismatch')
if env['polynomial']==0: raise RuntimeError('unexpected full zero')
if h+r != 3955 or not (0<h+r<U) or (h+r)%U==0:
    raise RuntimeError('gamma inverse obstruction failed')
# First residual A1=1 would require an integer square here.
P=X*Y*Y; first_target=1+P*(P+1)*k*k; floor=math.isqrt(first_target)
if floor*floor>=first_target or first_target>=(floor+1)*(floor+1):
    raise RuntimeError('first target unexpectedly square')
result={'status':'PASS_PARTIAL_OBSTRUCTION_ONLY','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'free_graph_operations':len(rows),'free_graph_operation_counts':dict(Counter(row[1] for row in rows)),
        'parent_graph_sha256':hashlib.sha256(raw).hexdigest(),
        'q':q,'Y':Y,'U':U,'X':X,'k':k,'c':c,'R':R,'h':h,'r':r,'gamma_numerator':h+r,
        'gamma_numerator_mod_U':(h+r)%U,'evaluated_graph_zero':False,'pell_iterations':c,'f_bits':f.bit_length(),'i_bits':i.bit_length(),
        'first_target':first_target,'first_floor_sqrt':floor,'first_gap':first_target-floor*floor,
        'scope':'Positive natural partial data satisfying transport, free-main and strong residuals; no first norm, unit residual, full zero or existence-equivalence counterexample.'}
out=Path(__file__).with_name('result.json');payload=json.dumps(result,indent=2,sort_keys=True)+'\n'
if sys.argv[1:]==['--write']:
    with out.open('x') as out_file:out_file.write(payload)
elif sys.argv[1:]:raise SystemExit('usage: python3 -I -S -B check.py [--write]')
elif out.read_text()!=payload:raise SystemExit('result differs')
print(json.dumps(result,sort_keys=True))
