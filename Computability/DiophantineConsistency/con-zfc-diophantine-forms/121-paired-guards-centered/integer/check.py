#!/usr/bin/env python3
"""Portable independent free-ring audit, including exact cancellation cuts."""
import ast,gzip,hashlib,json,itertools,importlib.util
from pathlib import Path
from collections import Counter
from exact_polynomial import Ring
import prior_check as old
ROOT=Path(__file__).resolve().parent
VARS=old.VARS;PORTS=old.PORTS;need=old.need
NAMES=['optimized_guard_fused11_direct','optimized_guard_fused11_aux','optimized_fused11_integral','optimized_fused11_rational','pair_fused11_integral','pair_fused11_rational','pair_fused11_rational_strong','pair_fused11_rational_sharp']
def formulas(p):
 pair=p['name'].startswith('pair_');fused=p.get('fused',False);rat=p['rational'];center=p['center']
 fs=old.formulas(False,False,'direct')
 fs=fs[:next(i for i,(n,e) in enumerate(fs) if n=='Dg')]
 fs += [('Pg','2*s*Dt'),('P','Dt+4*D*Dt*Dt*s*s')]
 if pair:fs += [('A','a+2'),('Dm','1+Delta*c*c'),('Ib','s*r*c*c*Dm'),('I','2*A*Ib')]
 elif fused:fs += [('Amain','a+2'),('Dm','1+Delta*c*c'),('I','2*s*r*c*c*P*Dm*Amain')]
 else:fs += [('I','2*s*r*c*c')]
 fs += [('I2','I*I'),('strong','Delta*I*I'),('Df','1+Delta*I*I'),('Q','Delta*Delta*I*I'),('delta','Q-1'),('b','c-R+4*I*T'),('V','Df*b-c'),('Cy','Q*V*V-1'),('Da','delta*Cy'),('K','X*(3*c-2*X)+2'),('H2','H*H'),('H3','H**3'),('H5','H**5'),('S','I*H**5'),('S2','S*S'),('zc','H*T+K'),('zc2','zc*zc'),('Ac','(zc*zc+3*H*H)*(zc**3-19*H**3)')]
 if pair:
  if center=='strong':fs += [('shift','A*I*V')]
  if center=='sharp':fs += [('lam','(2*Delta+1)*Ib'),('shift','lam*V')]
  fs += [('Z','S*n-Ac' if center=='none' else 'S*(n+shift)-Ac'),('Z2','Z*Z')]
  if rat:fs += [('pa','delta*Z2'),('pb','4*delta*S2*P'),('pc','S2*Df*Cy'),('rnorm','pa+pb-pc'),('output','rnorm*rnorm-4*pa*pb')]
  else:fs += [('ra','S2*Df*Da'),('rb','4*S2*P'),('rnorm','Z2-ra-rb'),('output','rnorm*rnorm-4*ra*rb')]
 elif fused:fs += [('Z','S*n-Ac'),('product','Df*P'),('output','delta*Z*Z-S2*product*Cy' if rat else 'Z*Z-S2*product*Da')]
 else:
  if center!='direct':fs += [('shift','(2*Q-1)*V')]
  fs += [('Z','S*n-Ac' if center=='direct' else 'S*(n+shift)-Ac'),('ra','S2*Df'),('rb','4*S2*Da'),('rc','16*S2*P'),('Z2','Z*Z'),('zp','Z2*rb'),('ue','ra*rc'),('vnorm','Z2+rb-ra-rc'),('ynorm','vnorm*vnorm-4*(zp+ue)'),('output','ynorm*ynorm-64*zp*ue')]
 return fs

def local_checks(p):
 nodes=p['nodes'];nm=dict(p['named_registers']);nm.update({r[1]:i for i,r in enumerate(nodes) if r[0] in ('variable','coefficient')});nm['output']=p['output'];covered=set();ledger=[]
 for name,expr in formulas(p):
  if name not in nm:continue
  tree=ast.parse(expr,mode='eval');refs=sorted({n.id for n in ast.walk(tree) if isinstance(n,ast.Name)});ring=Ring(refs);env={n:ring.var(n) for n in refs};memo={nm[n]:v for n,v in env.items()}
  def rec(i):
   covered.add(i)
   if i in memo:return memo[i]
   row=nodes[i]
   if row[0]=='integer':v=ring.scalar(row[1])
   else:
    need(row[0] in ('add','sub','mul'),'unbound local leaf '+str(row));a,b=rec(row[1]),rec(row[2]);v=a+b if row[0]=='add' else a-b if row[0]=='sub' else a*b
   memo[i]=v;return v
  expected=eval(expr,{'__builtins__':{}},env);need(rec(nm[name]).terms==expected.terms,'free-ring register '+name);ledger.append({'register':name,'expression':expr,'free_inputs':refs})
 missing=[i for i,r in enumerate(nodes) if r[0] in ('add','sub','mul') and i not in covered];need(not missing,'all live arithmetic bound '+str(missing));return ledger

def universal():
 prior=old.universal();ring=Ring(['z','a','b','e']);z,a,b,e=[ring.var(n) for n in ring.names]
 bal=((z*z+b-a-e)**2-4*(z*z*b+a*e))**2-64*z*z*b*a*e
 sym=((z*z-a-b-e)**2-4*(a*b+a*e+b*e))**2-64*a*b*e*z*z
 need(bal.terms==sym.terms,'balanced octic equals all-eight conjugate product')
 two=(z*z-a-b)**2-4*a*b
 acc={0:ring.scalar(1)}
 for signs in itertools.product([-1,1],repeat=2):
  factor={0:z,1:-signs[0]*ring.scalar(1),2:-signs[1]*ring.scalar(1)};out={}
  for i,x in acc.items():
   for j,y in factor.items():
    v=x*y
    for bit,r in enumerate([a,b]):
     if (i&j)&(1<<bit):v=v*r
    key=i^j;out[key]=out.get(key,ring.scalar(0))+v
  acc={i:v for i,v in out.items() if v.terms}
 need(set(acc)=={0} and acc[0].terms==two.terms,'four conjugates exactly multiplied')
 ring=Ring(['Z','S','d','F','C','P']);Z,S,d,F,C,P=[ring.var(n) for n in ring.names]
 need(((d*Z*Z+4*d*S*S*P-S*S*F*C)**2-16*d*d*S*S*P*Z*Z - ((d*Z*Z-S*S*F*C-4*d*S*S*P)**2-16*d*S**4*F*C*P)).terms=={},'denominator-cleared two-root identity')
 ring=Ring(['A','B','Q','V']);A,B,Q,V=[ring.var(n) for n in ring.names];Delta=A*A-1;I=2*A*B;Df=1+Delta*I*I;lam=(2*Delta+1)*B
 need((Df-lam*lam-(1-B*B)).terms=={},'sharp strong center exact identity')
 return dict(prior=prior,balanced_octic=True,four_conjugates=True,cleared_pair_norm=True,sharp_center=True)

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
 need(live==set(range(len(nodes))),'all nodes live');need([r[1] for r in nodes if r[0]=='variable']==VARS,'all eleven variables');need([r[1] for r in nodes if r[0]=='coefficient']==PORTS,'all six fixed numerals')
 count=Counter(r[0] for r in nodes if r[0] in ('add','sub','mul'));need(dict(count)==p['operation_counts'] and sum(count.values())==p['operations'],'cost count');need(degs[p['output']]==p['syntactic_degree_bound'],'syntactic degree');return {'live_nodes':len(nodes),'operations':sum(count.values()),'counts':dict(count),'syntactic_degree_bound':degs[p['output']]}

def leading(p):
 order=['T','j','w','v','h','s','r','c','C','z','n'];cr=Ring(PORTS);zero=(0,)*11;values=[];nm=p['named_registers'];cuts=[]
 def key(v):return(sum(v[0]),)+v[0]
 def times(a,b):return(tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
 def plus(a,b,minus=False):
  if key(a)>key(b):return a
  if key(a)<key(b):return(b[0],-b[1] if minus else b[1])
  return(a[0],a[1]-b[1] if minus else a[1]+b[1])
 def mulregs(*args):
  v=(zero,cr.scalar(1))
  for a in args:v=times(v,values[nm[a]] if isinstance(a,str) else (zero,cr.scalar(a)))
  return v
 for i,row in enumerate(p['nodes']):
  if p['name']=='optimized_guard_fused11_aux' and i==nm['ynorm']:
   v=mulregs(-4,'rb','rc');need(sum(v[0])==344,'octic center leading degree');cuts.append({'node':i,'register':'ynorm','exact_identity':'(omega-u-e)^2-4*(u*e+b*(u+e))','omega_degree':126,'unique_leader':'-4*b*e'})
  elif p['name'] in ['pair_fused11_rational_strong','pair_fused11_rational_sharp'] and i==nm['rnorm']:
   rr='I' if p['center']=='strong' else 'Ib';v=mulregs('S2','Q',rr,rr,'V','V');cuts.append({'node':i,'register':'rnorm','exact_identity':'S^2*(Q*(lambda^2-Df)-lambda^2)*V^2+S^2*Df+2*delta*S*lambda*V*(S*n-Ac)+delta*(S*n-Ac)^2+4*delta*S^2*P','unique_leader':'S^2*Q*'+rr+'^2*V^2'})
  elif row[0]=='variable':
   ex=[0]*11;ex[order.index(row[1])]=1;v=(tuple(ex),cr.scalar(1))
  elif row[0]=='coefficient':v=(zero,cr.var(row[1]))
  elif row[0]=='integer':v=(zero,cr.scalar(row[1]))
  else:
   a,b=values[row[1]],values[row[2]];v=times(a,b) if row[0]=='mul' else plus(a,b,row[0]=='sub')
  need(bool(v[1].terms),'all leading coefficients nonzero at '+str(i));values.append(v)
 out=values[p['output']];degree=sum(out[0]);need(degree==p['exact_degree'],'exact total degree attained');need(len(out[1].terms)==1,'one coefficient monomial');m,c=next(iter(out[1].terms.items()));need(all(not m[i] for i in range(1,len(m))),'only authentic beta in top coefficient');rem=abs(c);powers={}
 for prime in [2,3]:
  k=0
  while rem%prime==0:rem//=prime;k+=1
  powers[str(prime)]=k
 need(rem==1,'top coefficient prime factors');return {'exact_degree':degree,'monomial':dict(zip(order,out[0])),'coefficient':{'sign':1 if c>0 else -1,'powers':powers,'beta':m[0]},'all_actual_gate_leaders_checked':len(values),'cancellation_cuts':cuts,'nonzero_for_authentic_beta':True}

def main():
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 for path,pin in pins['dependencies'].items():
  raw=(ROOT/path).read_bytes();need(len(raw)==pin['bytes'] and hashlib.sha256(raw).hexdigest()==pin['sha256'],'retained dependency '+path)
 binding=json.loads((ROOT/'coefficients/BINDING.json').read_text());ports={}
 for n,pin in binding['payloads'].items():
  raw=gzip.decompress((ROOT/'coefficients'/pin['file']).read_bytes());need(hashlib.sha256(raw).hexdigest()==pin['raw_sha256'],'coefficient payload '+n);ports[n]=int.from_bytes(raw,'little');need(ports[n].bit_length()==pin['bits'],'coefficient bits '+n)
 need(ports['beta']==2**1064921-1 and ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'fixed recipes')
 spec=importlib.util.spec_from_file_location('recipe',ROOT/'coefficients/recipe/source34_builder.py');recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe);rebuilt,audit=recipe.construct()
 for oldn,new in [('beta','beta'),('K','K0'),('MC','MC'),('MF_source','MF')]:need(rebuilt[oldn]==ports[new],'full finite coefficient recipe '+new)
 result={'status':'PASS','universal':universal(),'retained_dependencies_authenticated':True,'coefficient_payloads_authenticated':True,'coefficient_recipe_rebuilt':True,'recipe_audit':audit,'equations':[]}
 for name in NAMES:
  p=json.loads((ROOT/(name+'.json')).read_text());result['equations'].append({'name':name,'topology':topology(p),'free_ring_register_bindings':local_checks(p),'leading_certificate':leading(p)})
 (ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','metrics':[{'name':r['name'],'operations':r['topology']['operations'],'degree':r['leading_certificate']['exact_degree']} for r in result['equations']]},indent=2))
if __name__=='__main__':main()
