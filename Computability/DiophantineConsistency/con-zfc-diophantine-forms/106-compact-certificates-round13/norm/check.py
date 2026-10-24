"""Independent exact local-ring audit; no producer or graph-helper imports.
The finite modular replays are transcription diagnostics, not a consistency proof.
"""
import json,gzip,hashlib,random,math,copy
from pathlib import Path
from collections import Counter
import sympy as sy
from independent_formula_short_guard import evaluate
R=Path(__file__).resolve().parent

def require(test,msg):
 if not test:raise RuntimeError(msg)
def read(p):return json.loads((R/p).read_text())
for name,info in read('SOURCE_PINS.json')['source_pins'].items():
 payload=(R/name).read_bytes()
 require(len(payload)==info['bytes'] and hashlib.sha256(payload).hexdigest()==info['sha256'],'source authentication '+name)
manifest=read('FIXED_COEFFICIENTS.json');fixed={}
for name,info in manifest.items():
 packed=(R/info['file']).read_bytes();raw=gzip.decompress(packed)
 require(hashlib.sha256(packed).hexdigest()==info['gzip_sha256'],'gzip hash '+name)
 require(hashlib.sha256(raw).hexdigest()==info['raw_sha256'],'raw hash '+name)
 fixed[name]=(-1 if raw[0] else 1)*int.from_bytes(raw[1:],'little')
ports=[int.from_bytes(gzip.decompress((R/'data'/f'{name}.bin.gz').read_bytes()),'little')for name in ['beta','K','MC','MF_source']]
code=read('data/code.json');kernel=read('data/kernels.json');base=read('source/integer10_polar.json')
for name,recipe in base['fixed_recipes'].items():
 require(fixed[name]==sum(t['coefficient']*math.prod(v**e for v,e in zip(ports,t['powers']))for t in recipe),'coefficient recipe '+name)
require(fixed['radix']==2**2134940 and fixed['threshold']==2**34159017,'fixed power leaves')

def names(body):
 ns=dict(body['named_nodes'])
 for a,b in [('Sigma','Sigma_new'),('Theta','Theta_new')]:
  if b in ns:ns[a]=ns[b]
 return ns

def expression(body,target,cuts):
 """Expand only a local cut, over free integral indeterminates."""
 ns=names(body);cutids={ns[n]:sy.Symbol(n)for n in cuts if n in ns};cache={};nodes=body['nodes']
 def visit(i):
  if i in cutids:return cutids[i]
  if i in cache:return cache[i]
  n=nodes[i];k=n['kind']
  if k=='literal':v=sy.Integer(n['value'])
  elif k in ('fixed','variable'):v=sy.Symbol(k+'_'+n['name'])
  else:
   a,b=visit(n['left']),visit(n['right']);v=a+b if k=='add' else a-b if k=='sub' else a*b
  cache[i]=v;return v
 return sy.expand(visit(target))

def exact_audit(body,parent,mode):
 bn,pn=names(body),names(parent)
 avoid={'center','inner','F10','shear','Sigma_new','Theta_new','shifted_center'}
 checked=[]
 for key in sorted(set(bn)&set(pn)-avoid,key=lambda x:pn[x]):
  cuts={n for n in set(bn)&set(pn)-avoid if pn[n]<pn[key] and bn[n]<bn[key]}
  # Explicitly expand dependent coordinates needed by these local identities.
  if key in ('X','K'):cuts-={'X','tc'}
  if key=='G':cuts-={'F'}
  aa=expression(body,bn[key],cuts);bb=expression(parent,pn[key],cuts)
  require(sy.expand(aa-bb)==0,'exact prefix identity '+key)
  checked.append(key)
 if mode!='polar':
  cuts={'halfA','B1','C','xi'} if mode=='sixterm' else {'A','E','E0','D','C','G','H'}
  require(sy.expand(expression(body,bn['shear'],cuts)-expression(parent,pn['shear'],cuts))==0,'exact shear identity')
 cuts={'Sigma','Theta','guard','lucas'}|({'shear'}if mode!='polar'else set())
 require(sy.expand(expression(body,body['output'],cuts)-expression(parent,parent['output'],cuts))==0,'exact complete norm identity')
 return checked

def run(body,inputs,p):
 env=dict(zip(body['variables'],inputs));out=[]
 for n in body['nodes']:
  k=n['kind']
  if k=='variable':v=env[n['name']]
  elif k=='fixed':v=fixed[n['name']]
  elif k=='literal':v=n['value']
  else:
   a,b=out[n['left']],out[n['right']];v=a+b if k=='add' else a-b if k=='sub' else a*b
  out.append(v%p)
 return out

def leading(body,p):
 ds=[];cs=[]
 for n in body['nodes']:
  k=n['kind']
  if k=='variable':d,c=1,1
  elif k in ('fixed','literal'):d,c=0,fixed[n['name']]if k=='fixed'else n['value']
  else:
   l,r=n['left'],n['right']
   if k=='mul':d,c=ds[l]+ds[r],cs[l]*cs[r]
   else:
    d=max(ds[l],ds[r]);c=(cs[l]if ds[l]==d else 0)+(1 if k=='add'else-1)*(cs[r]if ds[r]==d else 0)
  ds.append(d);cs.append(c%p)
 return {k:(ds[v],cs[v])for k,v in names(body).items()}

# Exact expanded radical defects with the six-term polynomial independently written.
h,b,c,x,y=sy.symbols('h b c x y');gens=[h,b,c,x,y];A=2*h;u=c*c;D=(A*A-4)*u+4;E0=u*x;E=E0*D
F=4*(A*A-4)*u*u*D*x*x+1;G=(h-1)*(F-1)-1;H=c+F*(b-c+16*E*y);a1=D*F*((G*G-1)*H*H+1)
r0=2*A*E*G*H;r1=2*A*E0*(D-2*u)*G*H
qa=u*(2*h*h-11)+6;qb=u*u*(8*h**4-52*h*h+143)+u*(32*h*h-176)+48
r6=32768*u**7*x**4*h**9*((h-1)*(x*(b-c)*qa+16*u*x*x*y*qb+3*y)-2*y)
roots={'polar':sy.Integer(0),'linear':sy.expand(r0),'cubic':sy.expand(r1),'sixterm':sy.expand(r6)}
weights=[16384,7942,1,2,1];defects={};weighted_degrees={}
for mode in ['linear','cubic','sixterm']:
 pp=sy.Poly(sy.expand(a1-roots[mode]**2),*gens);defects[mode]=pp
 weighted_degrees[mode]=max(sum(a*b for a,b in zip(exps,weights))for exps,coeff in pp.terms())
require(weighted_degrees=={'linear':426050,'cubic':393282,'sixterm':368449},'exact defect weighted degrees')

rootterms={k:sy.Poly(v,*gens).terms() for k,v in roots.items()}
# Structural ceiling: the negative square strictly dominates the short guard.
deg0=leading(base,1000003)
dg,dcap,dK,dL,dr=[deg0[n][0] for n in ['g','cap','K','L','r']]
require(dg+max(dcap,dg)+2*dK < 2*dcap+2*(dK+dL),'short-guard strict dominant square')
require(2*dcap+2*(dK+dL)+2*dr+2==deg0['guard'][0],'negative-square a0 degree')
require(weighted_degrees['linear']<deg0['lucas'][0],'positive-square a1 leading form')
require(4*deg0['Sigma'][0]+deg0['guard'][0]+deg0['lucas'][0]==1080888,'translation lower-bound degree')
sg,uu,vv=sy.symbols('sg uu vv')
require(sy.expand(-4*sg**4*(-uu**2)*vv**2-(2*sg**2*uu*vv)**2)==0,'positive-square cross identity')
rng=random.Random(131013);receipts=[];negative=[]
for mode,ops,degree in [('polar',467,1245324),('linear',470,1179788),('cubic',473,1114252),('sixterm',507,1080888)]:
 body=read('integer10_'+mode+'.json');parent=base if mode=='polar'else read('source/'+mode+'.json');nodes=body['nodes'];ns=names(body)
 require(body['variables']==base['variables'],'variable order')
 require(body['fixed_recipes']==base['fixed_recipes'],'fixed recipe metadata')
 require(body['exact_degree']==degree,'exact-degree metadata')
 for i,n in enumerate(nodes):
  require(n['kind'] in ('variable','fixed','literal','add','sub','mul'),'operator')
  if 'left'in n:require(0<=n['left']<i and 0<=n['right']<i,'topological edge')
 reached=set();todo=[body['output']]
 while todo:
  i=todo.pop()
  if i in reached:continue
  reached.add(i);n=nodes[i]
  if 'left'in n:todo.extend([n['left'],n['right']])
 require(len(reached)==len(nodes),'dead nodes')
 counts=dict(Counter(n['kind']for n in nodes if 'left'in n))
 require(sum(counts.values())==ops and body['total_operations']==ops and counts==body['operation_counts'],'operation count')
 require({n['name']for n in nodes if n['kind']=='variable'}==set(body['variables']),'variable liveness')
 checked=exact_audit(body,parent,mode)
 trials=0;degree_receipts={}
 for p in [1000003,1000033,1000037]:
  lc=leading(base,p)
  require(all(lc[n][1] for n in ['halfA','B1','C','xi','Sigma','guard','lucas','cap','K','L','r']),'nonzero source top coefficient')
  vals=[lc[n][1]for n in ['halfA','B1','C','xi']]+[1]
  if mode in ('linear','cubic'):
   J=defects[mode];jd=weighted_degrees[mode]
   jlc=sum(int(co)*math.prod(pow(v,e,p)for v,e in zip(vals,exps))for exps,co in J.terms()if sum(a*b for a,b in zip(exps,weights))==jd)%p
   require(jlc!=0,'nonzero defect leading form');lead=pow(lc['Sigma'][1],4,p)*jlc*jlc%p
   require(4*lc['Sigma'][0]+2*jd==degree,'derived exact degree')
  elif mode=='sixterm':
   lead=-4*pow(lc['Sigma'][1],4,p)*lc['guard'][1]*lc['lucas'][1]%p
   require(4*lc['Sigma'][0]+lc['guard'][0]+lc['lucas'][0]==degree,'cross-term exact degree')
  else:lead=pow(lc['Sigma'][1],4,p)*pow(lc['lucas'][1],2,p)%p
  require(lead!=0,'leading coefficient vanished');degree_receipts[str(p)]=lead
  for _ in range(120):
   inputs=[rng.randrange(-35,36)for n in body['variables']];expected,env=evaluate(inputs,p,[v%p for v in ports],code,kernel)
   subvals=[env['A']*pow(2,-1,p)%p,env['B1'],env['C'],env['xi'],inputs[7]%p]
   rt=sum(int(co)*math.prod(pow(v,e,p)for v,e in zip(subvals,exps))for exps,co in rootterms[mode])%p;shift=inputs[:];shift[-1]=(shift[-1]+rt)%p
   target,_=evaluate(shift,p,[v%p for v in ports],code,kernel)
   require(run(body,inputs,p)[body['output']]==target,'full native replay')
   trials+=1
 # Mutation retains topology, count and domain; exact proof must reject it.
 mutated=copy.deepcopy(body);mutated['nodes'][mutated['output']]['kind']='add'
 try:exact_audit(mutated,parent,mode)
 except RuntimeError:negative.append(mode)
 else:raise RuntimeError('negative control escaped')
 receipts.append({'mode':mode,'operations':ops,'exact_degree':degree,'prefix_register_identities':len(checked),'complete_native_modular_replays':trials,'nonzero_actual_numeral_leading_coefficients':degree_receipts,'sha256':hashlib.sha256((R/('integer10_'+mode+'.json')).read_bytes()).hexdigest()})
result={'status':'PASS','proof':'Universal exact local polynomial identities plus the pinned mathematical calibration; modular tests are supplemental.','translation_lower_bound':1080888,'a0_top_is_negative_square':True,'a1_top_is_positive_square':True,'weighted_defect_degrees':weighted_degrees,'negative_controls_rejected':negative,'candidates':receipts}
print(json.dumps(result,indent=2))
