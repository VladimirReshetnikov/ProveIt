"""Independent centered-polynomial identities and full native circuit replay.
No builder or circuit helper is imported. Finite checks are not consistency proofs.
"""
from pathlib import Path
import json,gzip,hashlib,random,math
import sympy as sy
from independent_formula_short_guard import evaluate
R=Path(__file__).resolve().parent
manifest=json.loads((R/'FIXED_COEFFICIENTS.json').read_text());fixed={}
for name,info in manifest.items():
 packed=(R/info['file']).read_bytes();raw=gzip.decompress(packed)
 if hashlib.sha256(packed).hexdigest()!=info['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=info['raw_sha256']:raise RuntimeError('fixed hash')
 fixed[name]=(-1 if raw[0] else 1)*int.from_bytes(raw[1:],'little')
ports=[int.from_bytes(gzip.decompress((R/'data'/f'{name}.bin.gz').read_bytes()),'little')for name in ['beta','K','MC','MF_source']]
code=json.loads((R/'data/code.json').read_text());kernel=json.loads((R/'data/kernels.json').read_text())
# Exact rational-polynomial identities are proved by full coefficient cancellation.
a,c,x,b,y=sy.symbols('a c x b y');d=(a*a-4)*c*c+4;f=4*(a*a-4)*c**4*d*x*x+1;g=(a/2-1)*(f-1)-1;h=c+f*(b-c+16*c*c*d*x*y);gh=sy.Poly(sy.expand(g*h),a)
L=1+16*c**4*x*x*(3*c*c-4)
q=sy.cancel((g*h-gh.nth(0))/(4*c*c*x*a))
half=sy.symbols('half');qpoly=sy.Poly(q.subs(a,2*half),half,c,x,b,y)
if not all(v.q==1 for v in qpoly.coeffs()):raise RuntimeError('correction is not integral polynomial in halfA')
r0=2*a*c*c*x*(d-2*c*c);j=d+16*c**4*x*x*((3*c*c-4)*d-4*c*c*(c*c-1));j0=-4*(c*c-1)-256*c**4*x*x*(c*c-1)**2
if sy.expand(d*f-r0*r0-j)!=0:raise RuntimeError('first square completion')
r=r0*g*h+L*q
rem=j0*(g*h)**2+c*c*L*a*g*h*(a*gh.nth(0)-4*x*(4-6*c*c)*q)-(L*q)**2-d*f*(h*h-1)
if sy.expand(d*f*((g*g-1)*h*h+1)-r*r-rem)!=0:raise RuntimeError('second square completion')
Z,S,u,v,P=sy.symbols('Z S u v P')
old=((Z+S*P)**2-S*S*(u+v))**2-4*S**4*u*v
new=(Z*Z+2*S*P*Z+S*S*(u-(v-P*P)))**2-4*S*S*u*(Z+S*P)**2
if sy.expand(old-new)!=0:raise RuntimeError('translated norm identity')
qterms=[(exps,int(co))for exps,co in qpoly.terms()]
def qfun(aa,cc,xx,bb,yy,p):
 values=[aa*pow(2,-1,p)%p,cc,xx,bb,yy]
 return sum(co*math.prod(pow(v,e,p)for v,e in zip(values,exps))for exps,co in qterms)%p
receipts=[];rng=random.Random(1202410)
for mode,ops,degree in [('polar',471,1245324),('center0',485,1179788),('center1',496,1114252),('center2',545,1080888)]:
 body=json.loads((R/('integer10_'+mode+'.json')).read_text());nodes=body['nodes'];names=body['named_nodes']
 for key,rows in body['fixed_recipes'].items():
  if fixed[key]!=sum(row['coefficient']*math.prod(v**e for v,e in zip(ports,row['powers']))for row in rows):raise RuntimeError('fixed binding')
 if fixed['radix']!=2**2134940 or fixed['threshold']!=2**34159017:raise RuntimeError('radix')
 def run(inputs,p):
  env=dict(zip(body['variables'],inputs));out=[]
  for i,n in enumerate(nodes):
   k=n['kind']
   if k=='variable':v=env[n['name']]
   elif k=='literal':v=n['value']
   elif k=='fixed':v=fixed[n['name']]
   else:
    if max(n['left'],n['right'])>=i:raise RuntimeError('forward edge')
    a0,b0=out[n['left']],out[n['right']];v=a0+b0 if k=='add' else a0-b0 if k=='sub' else a0*b0
   out.append(v%p)
  return out
 cases=0
 for p in [1000003,1000033,1000037]:
  for trial in range(120):
   inputs=[rng.randrange(-30,31)for _ in body['variables']];_,env=evaluate(inputs,p,[v%p for v in ports],code,kernel)
   aa,cc,xx,bb,yy=[env[n] for n in ['A','C','xi','B1']]+[inputs[7]%p]
   D,F,G,H=[env[n]for n in ['D','F','G','H']]
   root=0 if mode=='polar' else 2*aa*cc*cc*xx*(D if mode=='center0' else D-2*cc*cc)*G*H
   if mode=='center2':
    # Evaluate the separately expanded integer polynomial; no inversion or circuit register.
    root+=qfun(aa,cc,xx,bb,yy,p)*(1+16*cc**4*xx*xx*(3*cc*cc-4))
   shifted=inputs[:];shifted[-1]=(shifted[-1]+root)%p
   expected,_=evaluate(shifted,p,[v%p for v in ports],code,kernel);actual=run(inputs,p)
   if actual[body['output']]!=expected:raise RuntimeError(('full replay',mode,p,trial))
   cases+=1
 deg=[]
 for n in nodes:
  k=n['kind'];deg.append(1 if k=='variable' else 0 if k in ('literal','fixed') else deg[n['left']]+deg[n['right']] if k=='mul' else max(deg[n['left']],deg[n['right']]))
 leaders={}
 for p in [1000003,1000033,1000037]:
  lc=[]
  for i,n in enumerate(nodes):
   k=n['kind']
   if k=='variable':v=1
   elif k=='literal':v=n['value']
   elif k=='fixed':v=fixed[n['name']]
   elif k=='mul':v=lc[n['left']]*lc[n['right']]
   else:
    l,rr=n['left'],n['right'];v=(lc[l] if deg[l]==deg[i] else 0)+(1 if k=='add' else -1)*(lc[rr] if deg[rr]==deg[i] else 0)
   lc.append(v%p)
  if not lc[-1]:raise RuntimeError('degree unattained')
  leaders[str(p)]=lc[-1]
 seen=set();todo=[body['output']]
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k);n=nodes[k]
  if 'left'in n:todo.extend([n['left'],n['right']])
 if len(seen)!=len(nodes) or deg[-1]!=degree or sum('left'in n for n in nodes)!=ops:raise RuntimeError('literal metrics')
 receipts.append(dict(mode=mode,operations=ops,exact_degree=degree,leading_coefficients=leaders,complete_native_replays=cases,sha256=hashlib.sha256((R/('integer10_'+mode+'.json')).read_bytes()).hexdigest()))
result=dict(status='PASS',universal_polynomial_identities=3,correction_integral_polynomial=True,candidates=receipts)
(R/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
