#!/usr/bin/env python3
"""Independent portable finite audit. Standard library only; no removable asserts."""
import ast,gzip,hashlib,json,itertools,importlib.util
from pathlib import Path
from collections import Counter
from exact_polynomial import Ring
ROOT=Path(__file__).resolve().parent
NAMES=['guard_fused11_direct','guard_fused11_aux','fused11_integral','fused11_rational']
VARS=['j','C','z','h','r','v','w','T','c','n','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def need(ok,why):
 if not ok:raise ValueError(why)
def formulas(fused,rat,center):
 f=[('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('q2','q*q'),('q3','q*q*q'),('W','12*w+4'),('X','q*W'),('Y','(2*v+1)*q*q*q'),('E','X*Y'),('a','(X+1)*Y'),('H','4*a+3'),('Delta','a*a+H'),('F','(K0+W)*C-z*qm'),('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),('k','R+1+h*E'),('c2','c*c'),('eta','c-Y*k'),('U','cone_A*F'),('Vc','cone_B*C'),('Derr','(U-q)**2+(Vc-q)**2'),('Budget','k*k*(q*q-Derr)-4*q*q*eta*eta'),('ell','X*Y*Y'),('L','ell*k'),('Dt','1+ell*(ell+1)*k*k'),('D','3*Budget-4'),('s2','2*s'),('Dg','1+4*D*Dt*s*s')]
 if fused:f += [('Amain','a+2'),('Dm','1+Delta*c*c'),('I','2*s*r*c*c*Dt*Dg*Dm*Amain')]
 else:f += [('I','2*s*r*c*c')]
 f += [('I2','I*I'),('strong','Delta*I*I'),('Df','1+Delta*I*I'),('Q','Delta*Delta*I*I'),('delta','Q-1'),('b','c-R+4*I*T'),('V','Df*b-c'),('Cy','Q*V*V-1')]
 if not rat:f += [('Da','(Q-1)*(Q*V*V-1)')]
 f += [('K','X*(3*c-2*X)+2'),('H2','H*H'),('H3','H*H*H'),('H5','H**5'),('S','I*H**5'),('S2','S*S'),('zc','H*T+K'),('zc2','zc*zc'),('Ac','(zc*zc+3*H*H)*(zc*zc*zc-19*H*H*H)')]
 if fused:f += [('Z','S*n-Ac'),('product','Df*Dt*Dg'),('output',('delta*Z*Z-S*S*product*Cy' if rat else 'Z*Z-S*S*product*Da'))]
 else:
  if center!='direct':f += [('shift','(2*Q-1)*V'),('Z','S*(n+shift)-Ac')]
  else:f += [('Z','S*n-Ac')]
  f += [('P','Dt*Dg'),('ra','S*S*Df'),('rb','4*S*S*Da'),('rc','16*S*S*P'),('Z2','Z*Z'),('ab','ra+rb'),('arb','ra*rb'),('vnorm','Z*Z-ra-rb-rc'),('ynorm','vnorm*vnorm-4*(ra*rb+ra*rc+rb*rc)'),('output','ynorm*ynorm-64*ra*rb*rc*Z*Z')]
 return f

def local_checks(p):
 nodes=p['nodes'];nm=dict(p['named_registers']);nm.update({r[1]:i for i,r in enumerate(nodes) if r[0] in ('variable','coefficient')});nm['output']=p['output']
 covered=set();ledger=[]
 for name,expr in formulas(p['fused'],p['rational'],p['center']):
  if name not in nm:continue # algebraic abbreviation absent from live evaluator
  tree=ast.parse(expr,mode='eval');refs=sorted({n.id for n in ast.walk(tree) if isinstance(n,ast.Name)})
  ring=Ring(refs);env={n:ring.var(n) for n in refs};cut={nm[n]:v for n,v in env.items()};memo=dict(cut)
  def rec(i):
   covered.add(i)
   if i in memo:return memo[i]
   row=nodes[i]
   if row[0]=='integer':v=ring.scalar(row[1])
   else:
    need(row[0] in ('add','sub','mul'),'unbound local leaf '+str(row))
    a,b=rec(row[1]),rec(row[2]);v=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
   memo[i]=v;return v
  expected=eval(expr,{'__builtins__':{}},env)
  need(rec(nm[name]).terms==expected.terms,'entire free-ring register '+name)
  ledger.append({'register':name,'expression':expr,'free_inputs':refs})
 missing=[i for i,r in enumerate(nodes) if r[0] in ('add','sub','mul') and i not in covered]
 need(not missing,'all live arithmetic covered '+str(missing))
 return ledger

def universal():
 ring=Ring(['z','a','b','e']);z,a,b,e=[ring.var(n) for n in ring.names];rs=[a,b,e]
 # Independently multiply all8linear conjugates in free triquadratic algebra.
 acc={0:ring.scalar(1)}
 for signs in itertools.product([-1,1],repeat=3):
  factor={0:z,1:-signs[0]*ring.scalar(1),2:-signs[1]*ring.scalar(1),4:-signs[2]*ring.scalar(1)};out={}
  for i,x in acc.items():
   for j,y in factor.items():
    v=x*y
    for bit,r in enumerate(rs):
     if (i&j)&(1<<bit):v=v*r
    key=i^j;out[key]=out.get(key,ring.scalar(0))+v
  acc={i:v for i,v in out.items() if v.terms}
 expected=((z*z-a-b-e)**2-4*(a*b+a*e+b*e))**2-64*a*b*e*z*z
 need(set(acc)=={0} and acc[0].terms==expected.terms,'whole conjugate product identity')
 need(len(expected.terms)==35,'35coefficients')
 # Independently verify short congruence and centered auxiliary cuts.
 ring=Ring(['X','a','c','S','Q','V']);X,a,c,S,Q,V=[ring.var(n) for n in ring.names]
 need(((4*a+3)*X*c-2*(X*(X+2*a*c)-1)-(X*(3*c-2*X)+2)).terms=={},'short K identity')
 need((4*S*S*(Q-1)*(Q*V*V-1)-(S*(2*Q-1)*V)**2-S*S*(-V*V-4*Q+4)).terms=={},'auxiliary center cut')
 return {'norm_coefficients':35,'full_sign_product':True,'short_projector_identity':True,'center_identity':True}

def degree_cert(name):
 ring=Ring(['j','w','v','h','s','r','c','T','beta']);j,w,v,h,s,r,c,T,beta=[ring.var(n) for n in ring.names]
 q=6*beta*j;X=q*12*w;Y=2*v*q**3;a=X*Y;L=h*a*a*Y
 Dt=L*L;Budget=-4*q*q*Y*Y*h*h*a*a;Dg=12*Budget*Dt*s*s;P=Dt*Dg
 I=2*s*r*c*c
 if name.startswith('fused'):I=I*Dt*Dg*(a*a*c*c)*a
 S=I*(4*a)**5;Df=a*a*I*I;Q=a**4*I*I;V=4*a*a*I**3*T;Cy=Q*V*V;Da=Q*Cy
 if name=='guard_fused11_direct':top=(4*S*S*Da)**4;degree=728
 elif name=='guard_fused11_aux':top=16*(4*S*S*Da)**2*(16*S*S*P)**2;degree=688
 elif name=='fused11_integral':top=-S*S*Df*Dt*Dg*Da;degree=1892
 else:top=-S*S*Df*Dt*Dg*Cy;degree=1632
 need(len(top.terms)==1,'unique maximum T slice')
 mon,coef=next(iter(top.terms.items()));need(sum(mon[:-1])==degree,'attained total degree')
 sign=1 if coef>0 else -1;rem=abs(coef);powers={}
 for p in [2,3]:
  k=0
  while rem%p==0:k+=1;rem//=p
  powers[str(p)]=k
 need(rem==1,'coefficient consists of2and3powers')
 return {'exact_degree':degree,'monomial':dict(zip(ring.names[:-1],mon[:-1])),'coefficient':f'{sign} * 2^{powers["2"]} * 3^{powers["3"]} * beta^{mon[-1]}','coefficient_factors':{'sign':sign,'2':powers['2'],'3':powers['3'],'beta':mon[-1]},'nonzero_for_authentic_beta':True,'selection':'Maximum T exponent in top homogeneous form; all remaining factors are monomials.','proof':'PROOF.md Section6 supplies universal upper bound; literal leading dependencies checked below.'}

def actual_leading(p,certificate):
 order=['T','j','w','v','h','s','r','c','C','z','n'];cr=Ring(PORTS);zero=(0,)*11;values=[];nm=p['named_registers']
 def key(v):return(sum(v[0]),)+v[0]
 def times(a,b):return(tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
 def plus(a,b,minus=False):
  if key(a)>key(b):return a
  if key(a)<key(b):return(b[0],-b[1] if minus else b[1])
  return(a[0],a[1]-b[1] if minus else a[1]+b[1])
 override=None
 if p['name']=='guard_fused11_aux':
  row=p['nodes'][nm['vnorm']];need(row[0]=='sub' and row[2]==nm['rc'],'centered vnorm schedule');override=row[1]
 for i,row in enumerate(p['nodes']):
  if i==override:
   # This is (Z²-ra-rb)=omega-ra. The separately proved center cut has
   # degree126 leading 2*S*shift*(S*n-Ac); all competitors have degree<=118.
   lhs=p['nodes'][i];need(lhs==['sub',nm['Z2'],nm['ab']],'complete overridden node')
   c0=times(values[nm['S']],values[nm['shift']]);s0=plus(times(values[nm['S']],values[next(j for j,r in enumerate(p['nodes']) if r==['variable','n'])]),values[nm['Ac']],True)
   v=times((zero,cr.scalar(2)),times(c0,s0));need(sum(v[0])==126,'centered cancellation bound attained')
  elif row[0]=='variable':
   exp=[0]*11;exp[order.index(row[1])]=1;v=(tuple(exp),cr.scalar(1))
  elif row[0]=='coefficient':v=(zero,cr.var(row[1]))
  elif row[0]=='integer':v=(zero,cr.scalar(row[1]))
  else:
   a,b=values[row[1]],values[row[2]];v=times(a,b) if row[0]=='mul' else plus(a,b,row[0]=='sub')
  need(bool(v[1].terms),'nonzero exact leading coefficient at node'+str(i));values.append(v)
 v=values[p['output']];need(dict(zip(order,v[0]))=={n:certificate['monomial'].get(n,0) for n in order},'actual DAG top monomial')
 ex=certificate['coefficient_factors'];want=ex['sign']*(2**ex['2'])*(3**ex['3'])*cr.var('beta')**ex['beta']
 need(v[1].terms==want.terms,'actual DAG exact top coefficient')
 return {'all_nodes':len(values),'exact_center_cut_used':override is not None,'actual_output_matches_degree_certificate':True}

def topology(p):
 nodes=p['nodes'];live=set();todo=[p['output']];degs=[]
 for i,r in enumerate(nodes):
  if r[0] in ('add','sub','mul'):
   need(len(r)==3 and all(type(j)==int and 0<=j<i for j in r[1:]),'acyclic binary gate');degs.append(degs[r[1]]+degs[r[2]] if r[0]=='mul' else max(degs[r[1]],degs[r[2]]))
  else:need(r[0] in ('variable','coefficient','integer'),'leaf kind');degs.append(int(r[0]=='variable'))
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if nodes[i][0] in ('add','sub','mul'):todo.extend(nodes[i][1:])
 need(live==set(range(len(nodes))),'no dead nodes');need([r[1] for r in nodes if r[0]=='variable']==VARS,'all11variables');need([r[1] for r in nodes if r[0]=='coefficient']==PORTS,'all6fixedports')
 count=Counter(r[0] for r in nodes if r[0] in ('add','sub','mul'));need(dict(count)==p['operation_counts'] and sum(count.values())==p['operations'],'binary operation count')
 need(degs[p['output']]==p['syntactic_degree_bound'],'syntactic bound')
 wanted={'S':148 if p['fused'] else 34,'Df':248 if p['fused'] else 20,'Q':260 if p['fused'] else 32,'V':367 if p['fused'] else 25,'Cy':994 if p['fused'] else 82,'Dg':60,'Dt':34,'Ac':35}
 for n,d in wanted.items():need(degs[p['named_registers'][n]]==d,'literal prefix degree '+n)
 return {'live_nodes':len(nodes),'operations':sum(count.values()),'counts':dict(count),'syntactic_bound':degs[p['output']]}

def main():
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for name,pin in pins['dependencies'].items():
  raw=(ROOT/name).read_bytes();need(len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256'],'complete retained source '+name)
 binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());ports={}
 for n,pin in binding['payloads'].items():
  raw=gzip.decompress((ROOT/'coefficients'/pin['file']).read_bytes());need(hashlib.sha256(raw).hexdigest()==pin['raw_sha256'],'full coefficient payload '+n);ports[n]=int.from_bytes(raw,'little');need(ports[n].bit_length()==pin['bits'],'coefficient bits '+n)
 need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'fixed recipes')
 spec=importlib.util.spec_from_file_location('source34_recipe',ROOT/'coefficients/recipe/source34_builder.py');recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe)
 rebuilt,recipe_audit=recipe.construct()
 for old,new in [('beta','beta'),('K','K0'),('MC','MC'),('MF_source','MF')]:need(rebuilt[old]==ports[new],'full finite recipe equality '+new)
 result={'status':'PASS','universal':universal(),'coefficient_payloads':True,'coefficient_recipe_rebuilt':True,'recipe_audit':recipe_audit,'equations':[]}
 for name in NAMES:
  p=json.loads((ROOT/(name+'.json')).read_text());d=degree_cert(name);need(d['exact_degree']==p['exact_degree'],'declared exact degree')
  result['equations'].append({'name':name,'topology':topology(p),'all_register_ring_cuts':local_checks(p),'degree':d,'actual_dag_leading':actual_leading(p,d)})
 dest=ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json');dest.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','equations':[{k:r[k] for k in ['name','topology','degree']} for r in result['equations']]},indent=2))
if __name__=='__main__':main()
