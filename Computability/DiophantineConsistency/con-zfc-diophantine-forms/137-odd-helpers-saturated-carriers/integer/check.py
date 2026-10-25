#!/usr/bin/env python3
"""Independent local polynomial and exact-leading-form audit, standard library only."""
import ast,gzip,hashlib,json,itertools,importlib.util,copy,math
from pathlib import Path
from collections import Counter
from exact_polynomial import Ring
ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','s'];PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def need(ok,msg):
 if not ok:raise ValueError(msg)
def formulas(p):
 f=[('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),('W','12*w+4'),('X','q*W'),('Y','v' if p['free_y'] else 'q*v'),('E','X*Y'),('a','E+Y'),('H','4*a+3'),('Delta','a*a+H'),('A','a+2'),('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J'),('k','R+1+h*E'),('c2','c*c'),('Yk','Y*k'),('eta','c-Yk'),('Derr','(cone_A*F-q)**2+(cone_B*C-q)**2')]
 if p['free_y']:f += [('q3','q**3'),('Yeta','Y*eta'),('kq3','k*q3'),('Budget','Y*Y*(k*k*(q*q-Derr)-4*q*q*eta*eta)-k*k*q**8')]
 else:f += [('Budget','k*k*(q*q-Derr)-4*q*q*eta*eta')]
 f += [('L','E*Y*k'),('Dt','1+L*(L+k)'),('D4','12*Budget-16'),('Pg','Dt*s'),('P','Dt+4*(3*Budget-4)*Dt*Dt*s*s'),('Dm','1+Delta*c*c'),('BP','Dm*P'),('Ub','r*c*c'),('U','A*Ub'),('UBP','U*BP'),('strong','Delta*U*U*BP'),('Df','strong+1'),('Q','Delta*strong'),('delta','Q-1'),('b','c-R+4*UBP*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),('K','X*(3*c-2*X)+2'),('qscale','q**3' if p['free_y'] else 'q*q'),('M','2*qscale'),('Dcar','M*H'),('M2','M*M'),('M4','M**4'),('Dcar2','Dcar*Dcar'),('Dcar3','Dcar**3'),('S','s*r*H*M**5'),('S2','S*S'),('zc','Dcar*T+M*K+H*(v-qscale)'),('zc2','zc*zc'),('Ac','(zc**2+3*Dcar**2)*(zc**3-19*Dcar**3)')]
 if p['center']=='simple':f += [('lam','A*U*BP'),('shift','lam*V'),('Z','S*(n+lam*V)-Ac')]
 else:f += [('Z','S*n-Ac')]
 f += [('output','delta*Z*Z-S*S*BP*Df*Cy')]
 return f

def local_checks(p):
 nodes=p['nodes'];nm=dict(p['named_registers']);nm.update({r[1]:i for i,r in enumerate(nodes) if r[0] in ('variable','coefficient')});nm['output']=p['output'];covered=set();ledger=[]
 for name,expr in formulas(p):
  if name not in nm:continue
  tree=ast.parse(expr,mode='eval');refs=sorted({n.id for n in ast.walk(tree) if isinstance(n,ast.Name)});ring=Ring(refs);env={n:ring.var(n) for n in refs};memo={nm[n]:v for n,v in env.items()}
  def rec(i):
   covered.add(i)
   if i in memo:return memo[i]
   row=nodes[i]
   if row[0]=='integer':val=ring.scalar(row[1])
   else:
    need(row[0] in ('add','sub','mul'),'unbound local leaf '+str(row));a,b=rec(row[1]),rec(row[2]);val=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
   memo[i]=val;return val
  expected=eval(expr,{'__builtins__':{}},env);need(rec(nm[name]).terms==expected.terms,'free-ring register '+name);ledger.append({'register':name,'expression':expr})
 missing=[i for i,r in enumerate(nodes) if r[0] in ('add','sub','mul') and i not in covered];need(not missing,'all live arithmetic bound '+str(missing));return ledger

def universal():
 ring=Ring(['z','a','b']);z,a,b=[ring.var(n) for n in ring.names];acc={0:ring.scalar(1)}
 for signs in itertools.product([-1,1],repeat=2):
  fac={0:z,1:-signs[0]*ring.scalar(1),2:-signs[1]*ring.scalar(1)};out={}
  for i,x in acc.items():
   for j,y in fac.items():
    val=x*y
    for bit,rad in enumerate([a,b]):
     if (i&j)&(1<<bit):val=val*rad
    key=i^j;out[key]=out.get(key,ring.scalar(0))+val
  acc={i:v for i,v in out.items() if v.terms}
 need(set(acc)=={0} and acc[0].terms==((z*z+a-b)**2-4*a*z*z).terms,'four conjugate product')
 ring=Ring(['A','u','B','V','S','W','P']);A,u,B,V,S,W,P=[ring.var(n) for n in ring.names]
 D=A*A-1;U=A*u;F=1+D*U*U*B;Q=D*D*U*U*B;delta=Q-1;Cy=Q*V*V-1
 lam=A*U*B;diff=U*U*B*B-B
 need((lam*lam-B*F-diff).terms=={},'simple product center identity')
 Z=W+S*lam*V;output=delta*Z*Z-S*S*B*F*Cy
 cut=delta*W*W+2*delta*S*lam*V*W+S*S*((delta*diff-B*F)*V*V+B*F)
 need((output-cut).terms=={},'simple product exact cancellation cut')
 ring=Ring(['A','c','u','b']);A,c,u,b=[ring.var(n) for n in ring.names];D=A*A-1;B=1+D*c*c;U=A*u;F=1+D*U*U*B;Q=D*D*U*U*B;delta=Q-1;V=F*b-c;Cy=Q*V*V-1;Da=delta*Cy
 need((Q+D-D*F).terms=={},'Q remainder')
 L=Q*b*(V-c)+D*c*c
 need((Cy+B-F*L).terms=={},'Cy remainder')
 need((Da-A*A*B-F*(D*F*L-D*B-A*A*L)).terms=={},'Da remainder')
 need((Da-1-Q*((Q-1)*V*V-1)).terms=={},'Da=1 modulo Q')
 ring=Ring(['A','c','u','b','P']);A,c,u,b,P=[ring.var(n) for n in ring.names];D=A*A-1;B=1+D*c*c;BP=B*P;U=A*u;F=1+D*U*U*BP;Q=D*D*U*U*BP;delta=Q-1;V=F*b-c;Cy=Q*V*V-1;Da=delta*Cy;LL=Q*b*(V-c)+D*c*c
 need((Cy+B-F*LL).terms=={},'new product Cy remainder')
 need((Da-A*A*B-F*(D*F*LL-D*B-A*A*LL)).terms=={},'new product Da remainder')
 need((Da-1-Q*((Q-1)*V*V-1)).terms=={},'new product Da=1 modulo BP')
 ring=Ring(['U','d','T','c','R','F']);U,d,T,c,R,F=[ring.var(n) for n in ring.names]
 need((F*(c-R+4*U*d*d*T)-c-(F*(c-R+4*(U*d)*(d*T))-c)).terms=={},'auxiliary exact rescaling')
 ring=Ring(['Y','k','q','E','err']);Y,k,q,E,err=[ring.var(n) for n in ring.names]
 need((Y*Y*(k*k*(q*q-err)-4*q*q*E*E)-k*k*q**8-((Y*k)**2*(q*q-err)-q*q*(4*(Y*E)**2+(k*q**3)**2))).terms=={},'shared strengthened guard identity')
 finite_cases=0
 for A in list(range(-7,-1))+list(range(2,8)):
  for c in range(-4,5):
   for r in range(-3,4):
    for b in range(-3,4):
     D=A*A-1;B=1+D*c*c;U=A*r*c*c;F=1+D*U*U*B;Q=D*D*U*U*B;V=F*b-c;Da=(Q-1)*(Q*V*V-1)
     need(math.gcd(B,F)==math.gcd(B,Da)==math.gcd(F,Da)==1,'finite coprimality edge case')
     need(F%4==1 and Q%4==0,'finite parity edge case');finite_cases+=1
 return dict(four_conjugates=True,center_identities=True,cancellation_cuts=True,coprimality_remainders=True,auxiliary_rescaling=True,shared_guard_identity=True,finite_edge_cases=finite_cases)

def topology(p):
 ns=p['nodes'];live=set();todo=[p['output']];ds=[]
 for i,r in enumerate(ns):
  if r[0] in ('add','sub','mul'):
   need(len(r)==3 and all(type(j)==int and 0<=j<i for j in r[1:]),'acyclic binary gate');ds.append(ds[r[1]]+ds[r[2]] if r[0]=='mul' else max(ds[r[1]],ds[r[2]]))
  else:need(r[0] in ('variable','coefficient','integer'),'leaf kind');ds.append(int(r[0]=='variable'))
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if ns[i][0] in ('add','sub','mul'):todo.extend(ns[i][1:])
 need(live==set(range(len(ns))),'all nodes live');need([r[1] for r in ns if r[0]=='variable']==VARS,'all eleven variables');need([r[1] for r in ns if r[0]=='coefficient']==PORTS,'all six coefficients')
 cnt=Counter(r[0] for r in ns if r[0] in ('add','sub','mul'));need(dict(cnt)==p['operation_counts'] and sum(cnt.values())==p['operations'],'count');need(ds[p['output']]==p['syntactic_degree_bound'],'syntactic bound')
 return dict(live_nodes=len(ns),operations=sum(cnt.values()),counts=dict(cnt),syntactic_degree=ds[p['output']])

def leading(p):
 order=['T','j','w','v','h','s','r','c','C','z','n'];cr=Ring(PORTS);zero=(0,)*11;values=[];nm=p['named_registers'];cuts=[]
 def key(v):return(sum(v[0]),)+v[0]
 def times(a,b):return(tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
 def plus(a,b,minus=False):
  if key(a)>key(b):return a
  if key(a)<key(b):return(b[0],-b[1] if minus else b[1])
  return(a[0],a[1]-b[1] if minus else a[1]+b[1])
 def product(*args):
  out=(zero,cr.scalar(1))
  for a in args:out=times(out,values[nm[a]] if isinstance(a,str) else (zero,cr.scalar(a)))
  return out
 for i,row in enumerate(p['nodes']):
  if p['center']=='simple' and i==p['output']:
   val=product('S2','Q','BP','BP','U','U','V','V')
   weights={'S':sum(values[nm['S']][0]),'delta':sum(values[nm['delta']][0]),'lam':sum(values[nm['lam']][0]),'V':sum(values[nm['V']][0]),'W':max(sum(values[nm['S']][0])+1,sum(values[nm['Ac']][0])),'B':sum(values[nm['BP']][0]),'F':sum(values[nm['Df']][0]),'U':sum(values[nm['U']][0])}
   rr=Ring(list(weights));S,delta,lam,V,W,B,F,U=[rr.var(n) for n in rr.names]
   diff=B*B*U*U-B
   expanded=delta*W*W+2*delta*S*lam*V*W+S*S*((delta*diff-B*F)*V*V+B*F)
   leader=S*S*delta*B*B*U*U*V*V
   degree=sum(val[0]);ww=[weights[n] for n in rr.names]
   need(expanded.weighted_degree(ww)==degree and expanded.homogeneous(ww,degree)==leader.terms,'unique maximal cancellation-cut term')
   cuts.append({'node':i,'register':'output','proved_identity':'universal() exact product center expansion','unique_leader':'S2*Q*BP^2*U^2*V^2'})
  elif row[0]=='variable':
   ex=[0]*11;ex[order.index(row[1])]=1;val=(tuple(ex),cr.scalar(1))
  elif row[0]=='coefficient':val=(zero,cr.var(row[1]))
  elif row[0]=='integer':val=(zero,cr.scalar(row[1]))
  else:
   a,b=values[row[1]],values[row[2]];val=times(a,b) if row[0]=='mul' else plus(a,b,row[0]=='sub')
  need(bool(val[1].terms),'nonzero leader at gate '+str(i));values.append(val)
 out=values[p['output']];degree=sum(out[0]);need(degree==p['exact_degree'],'exact degree');need(len(out[1].terms)==1,'single coefficient monomial');m,c=next(iter(out[1].terms.items()));need(all(not m[i] for i in range(1,len(m))),'only beta in leading coefficient')
 rem=abs(c);powers={}
 for prime in [2,3]:
  k=0
  while rem%prime==0:rem//=prime;k+=1
  powers[str(prime)]=k
 need(rem==1,'coefficient powers');return dict(exact_degree=degree,monomial=dict(zip(order,out[0])),coefficient=dict(sign=1 if c>0 else -1,powers=powers,beta=m[0]),cancellation_cuts=cuts,all_actual_gate_leaders_checked=len(values))

def main():
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for path,pin in pins['dependencies'].items():
  raw=(ROOT/path).read_bytes();need(len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256'],'dependency '+path)
 binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());ports={}
 for n,pin in binding['payloads'].items():
  raw=gzip.decompress((ROOT/'coefficients'/pin['file']).read_bytes());need(hashlib.sha256(raw).hexdigest()==pin['raw_sha256'],'coefficient '+n);ports[n]=int.from_bytes(raw,'little');need(ports[n].bit_length()==pin['bits'],'coefficient bits '+n)
 need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'fixed coefficient recipes')
 spec=importlib.util.spec_from_file_location('recipe',ROOT/'coefficients/recipe/source34_builder.py');recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe);rebuilt,ra=recipe.construct()
 for a,b in [('beta','beta'),('K','K0'),('MC','MC'),('MF_source','MF')]:need(rebuilt[a]==ports[b],'complete finite recipe '+b)
 result=dict(status='PASS',universal=universal(),dependencies_authenticated=len(pins['dependencies']),all_six_coefficient_payloads_authenticated=True,full_coefficient_recipe_rebuilt=True,recipe_audit=ra,equations=[])
 for path in sorted(ROOT.glob('*_product11_*.json')):
  p=json.loads(path.read_text());result['equations'].append(dict(name=p['name'],topology=topology(p),free_ring_register_bindings=local_checks(p),leading_certificate=leading(p)))
 # Each arithmetic gate must be rejected by independent algebraic checks.
 controls=[]
 for path in sorted(ROOT.glob('*_product11_*.json')):
  sample=json.loads(path.read_text());rejected=0
  for index,row in enumerate(sample['nodes']):
   if row[0] not in ('add','sub','mul'):continue
   damaged=copy.deepcopy(sample);damaged['nodes'][index][0]={'add':'sub','sub':'add','mul':'add'}[row[0]]
   try:local_checks(damaged)
   except (ValueError,KeyError):rejected+=1
   else:raise ValueError('gate mutation not rejected '+str(index))
  controls.append({'name':sample['name'],'gate_mutations_rejected':rejected})
 for kind in ['integer_leaf','variable_leaf','degree','coefficient_leaf']:
  sample=json.loads((ROOT/'free_product11_simple.json').read_text());damaged=copy.deepcopy(sample)
  if kind=='integer_leaf':next(r for r in damaged['nodes'] if r[0]=='integer')[1]+=1
  elif kind=='variable_leaf':next(r for r in damaged['nodes'] if r[0]=='variable')[1]='unapproved_variable'
  elif kind=='coefficient_leaf':next(r for r in damaged['nodes'] if r[0]=='coefficient')[1]='unapproved_coefficient'
  else:damaged['exact_degree']+=1
  try:topology(damaged);local_checks(damaged);leading(damaged)
  except (ValueError,KeyError):controls.append(kind)
  else:raise ValueError('mutation not rejected '+kind)
 result['rejected_mutations']=controls
 (ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(status='PASS',metrics=[dict(name=r['name'],operations=r['topology']['operations'],degree=r['leading_certificate']['exact_degree']) for r in result['equations']]),indent=2))
if __name__=='__main__':main()
