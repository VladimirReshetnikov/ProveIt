#!/usr/bin/env python3
"""Independent four-source audit from saved JSON; no author module execution."""
import argparse, ast, hashlib, json
from pathlib import Path
from collections import Counter, deque
if not __debug__: raise RuntimeError('Run without -O')
STEM='group_projective_inverse_macro_sharing'
AUTHOR_PINS={'.py':'c23f1cff1ccf1d7ad004c29670cf08926e05790eb02baeaddf4c691bd9b02957','.json':'4f02c041fcb8db78849c5d95c2b23cabab615c88e42ef648f9c8377d876fb09b','.md':'8ba6acdfcbf932c2814b44de590ac456ae223d7d686d19d72d54e17e2e0c8ac0'}
BASE_PINS={
'group_projective_shared_macro_automaton.py':'2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7',
'group_projective_shared_macro_automaton.json':'284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497',
'group_projective_shared_macro_automaton.md':'5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6',
'group_inverse_stallings_controller.py':'f55cc2536854c2c3448558541dc35f1888b33ae941307798f02e78dd20ff6230',
'group_inverse_stallings_controller.json':'283ddbff12ef0e42be06ca2ab123a15cdbcdb4f02e5daa50571127549cb3db90',
'group_inverse_stallings_controller.md':'219917bda05e9bdbe460cab56a4768f67a6eb1da9ef816b06307df43039c6237'}
P_NAME='controller__geometry_power'
RT=(2,3,6,7);BM=(1,5)*5;AM=RT+BM
inverse=lambda w:tuple(a+1 if a%2 else a-1 for a in reversed(w))
CODES=(AM,BM,inverse(AM),inverse(BM));NIELSEN=(RT,BM,inverse(RT),inverse(BM))
FACTORS=('first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit')
def require(x, message):
 if not x: raise ValueError(message)
def sha(b): return hashlib.sha256(b).hexdigest()
def typed(a,b):
 if type(a) is not type(b): return False
 if isinstance(a,dict): return a.keys()==b.keys() and all(typed(a[k],b[k]) for k in a)
 if isinstance(a,list): return len(a)==len(b) and all(typed(x,y) for x,y in zip(a,b))
 return a==b
# Independent sparse polynomial arithmetic for the complete outer cones.
def const(x): return {():x} if x else {}
def atom(x): return {((x,1),):1}
def add(a,b,sign=1):
 z=dict(a)
 for m,c in b.items():
  z[m]=z.get(m,0)+sign*c
  if not z[m]: del z[m]
 return z
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   e=dict(m)
   for v,k in n:e[v]=e.get(v,0)+k
   mon=tuple(sorted(e.items()));z[mon]=z.get(mon,0)+c*d
 return {m:c for m,c in z.items() if c}
def power(a,n):
 z=const(1)
 while n:
  if n&1:z=mul(z,a)
  a=mul(a,a);n//=2
 return z
def total(xs):
 z={}
 for x in xs:z=add(z,x)
 return z
def scale(n,p): return mul(const(n),p)
def value(x,e): return e[x] if isinstance(x,str) else const(x)
def poly_cone(rows,free,target,cuts):
 defs={n:(o,a,b) for n,o,a,b in rows};env={n:atom(n) for n in free};env.update(cuts)
 def go(n):
  if type(n) is int:return const(n)
  if n not in env:
   op,a,b=defs[n];a,b=go(a),go(b);env[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
  return env[n]
 return go(target)
def run(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def account(p):
 free=p['free'];degree={n:1 for n in free};defs={};c=Counter()
 require(len(free)==len(set(free)),'unique input leaves')
 for n,o,a,b in p['source']:
  require(n not in degree and o in ('+','-','*'),'fresh legal gate')
  require(all(type(t) is int or type(t) is str and t in degree for t in (a,b)),'closed exact-type schedule')
  da,db=(degree.get(t,0) for t in (a,b));degree[n]=da+db if o=='*' else max(da,db)
  defs[n]=(a,b);c['M' if o=='*' else 'A']+=1
 seen=set();used=set();stack=[p['output']]
 while stack:
  n=stack.pop()
  if type(n) is int:continue
  if n not in defs:used.add(n)
  elif n not in seen:seen.add(n);stack.extend(defs[n])
 require(seen==set(defs) and used==set(free),'all gates and supplied leaves live')
 ans=dict(operations=len(defs),M=c['M'],A=c['A'],degree_upper=degree[p['output']])
 require(ans==p['ledger'],'literal full ledger')
 return ans
# Exact ring-expression DAG: addition is a sparse linear combination of
# nonlinear node IDs, sufficient for D=(D-u)+u without a proof cut.
class Ring:
 def __init__(self):self.memo={};self.next=1
 def leaf(self,key):
  if key not in self.memo:self.memo[key]=self.next;self.next+=1
  return ((self.memo[key],1),)
 def number(self,n):return ((0,n),) if n else ()
 def op(self,o,a,b):
  if o in ('+','-'):
   z=dict(a)
   for k,v in b:z[k]=z.get(k,0)+(v if o=='+' else -v)
   return tuple(sorted((k,v) for k,v in z.items() if v))
  if not a or not b:return ()
  if len(a)==1 and a[0][0]==0:return tuple((k,a[0][1]*v) for k,v in b)
  if len(b)==1 and b[0][0]==0:return tuple((k,b[0][1]*v) for k,v in a)
  return self.leaf(('*',tuple(sorted((a,b)))))
 def execute(self,p,env):
  e=dict(env)
  for n,o,a,b in p['source']:
   av=e[a] if isinstance(a,str) else self.number(a);bv=e[b] if isinstance(b,str) else self.number(b)
   e[n]=self.op(o,av,bv)
  return e


def load_pinned(root,name,digest):
 path=root/name
 if not path.exists():path=Path(__file__).resolve().parent/name
 data=path.read_bytes();require(sha(data)==digest,'authenticated bytes '+name)
 return data

def authenticate(root):
 base={n:load_pinned(root,n,h) for n,h in BASE_PINS.items()}
 manifest=json.loads(base['group_projective_shared_macro_automaton.json'])['pins']|BASE_PINS
 require(len(manifest)==38,'independently chained dependency inventory')
 blobs={n:load_pinned(root,n,h) for n,h in manifest.items()}
 author={ext:load_pinned(root,STEM+ext,h) for ext,h in AUTHOR_PINS.items()}
 saved=json.loads(author['.json'])
 require(saved['source_sha256']==sha(author['.py']) and saved['pins']==manifest,'saved selfsource and exact dependency pins')
 tree=ast.parse(author['.py']);literal={}
 for node in tree.body:
  if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='PINS' for t in node.targets):literal.update(ast.literal_eval(node.value))
  if isinstance(node,ast.Expr) and isinstance(node.value,ast.Call):
   call=node.value
   if isinstance(call.func,ast.Attribute) and isinstance(call.func.value,ast.Name) and call.func.value.id=='PINS' and call.func.attr=='update':literal.update(ast.literal_eval(call.args[0]))
 require(literal==manifest,'source literal manifest matches independently authenticated inventory')
 for n in ast.walk(tree):
  if isinstance(n,ast.Import):require(all(x.name in ('argparse','copy','json','hashlib','itertools','random') for x in n.names),'stdlib imports only')
  if isinstance(n,ast.ImportFrom):require(n.module in ('fractions','collections','pathlib'),'stdlib from imports only')
 return saved,blobs,manifest

def own_paths(words):
 edges=[];fresh=1
 for w in words:
  states=[0]+list(range(fresh,fresh+len(w)-1))+[0];fresh+=len(w)-1
  edges.extend([states[i],states[i+1],l] for i,l in enumerate(w))
 return edges

def path(edges,word):
 active={0:[]}
 for label in word:
  following={}
  for index,(a,b,l) in enumerate(edges):
   if l==label and a in active and b not in following:following[b]=active[a]+[index]
  active=following
 require(0 in active,'actual hub loop')
 return active[0]

def nfa_equal(a,b):
 def transition(edges,states,label):return frozenset(y for x,y,l in edges if l==label and x in states)
 start=(frozenset([0]),frozenset([0]));seen={start};todo=[start]
 while todo:
  x,y=todo.pop();require((0 in x)==(0 in y),'whole regular word language equivalence')
  for l in range(1,9):
   z=(transition(a,x,l),transition(b,y,l))
   if z not in seen:seen.add(z);todo.append(z)
 return len(seen)

def graph_check(packets,core):
 require(packets['private']['edges']==own_paths(CODES),'original literal private paths')
 require(packets['nielsen']['edges']==own_paths(NIELSEN),'literal Nielsen private paths')
 require(packets['folded']['edges']==core,'actual frozen inverse graph')
 count=nfa_equal(packets['private']['edges'],packets['shared']['edges'])
 require(count==37,'complete reachable subset-pair count')
 cycles=[path(core,w) for w in (RT,BM)]
 internal=[];used=set()
 for ids in cycles:
  states=[0]+[core[i][1] for i in ids]
  require(states[-1]==0 and len(set(states[:-1]))==len(ids),'simple core cycle')
  internal.append(set(states[1:-1]))
  for i in ids:
   a,b,l=core[i];used.update(((a,b,l),(b,a,l+1 if l%2 else l-1)))
 require(not internal[0]&internal[1] and used==set(map(tuple,core)),'two-cycle inverse bouquet spans every edge')
 for tag,p in packets.items():
  n=len(p['edges']);m=1<<(max(8,n)-1).bit_length()
  require(m==p['m'] and len(set(map(tuple,p['edges'])))==n,'padded lanes and distinct physical edges')
  require(all(type(v) is int and 0<=v<m for e in p['edges'] for v in e[:2]),'state bounds')
  require(set(e[2] for e in p['edges'])==set(range(1,9)),'eight literal physical labels')
  require(len(p['positions'])==n and len(set(p['positions']))==n and all(type(i)is int and 0<=i<m for i in p['positions']),'injective exact lane assignment')
  if tag in ('private','nielsen'):
   states=set(v for e in p['edges'] for v in e[:2])-{0}
   require(all(sum(a==v for a,b,l in p['edges'])==sum(b==v for a,b,l in p['edges'])==1 for v in states),'private path flow premise')
   require(all(b==a+1 for a,b,l in p['edges'] if a and b),'consecutive private state codes')
 return dict(exact_language_subset_pairs=count,inverse_cycle_lengths=[4,10],graphs=4)

def source_ledger(p):
 q=dict(source=p['source'],free=p['free'],output='joint_outer_output')
 count=Counter(o for n,o,a,b in q['source']);d={n:1 for n in q['free']}
 for n,o,a,b in q['source']:d[n]=d.get(a,0)+d.get(b,0) if o=='*' else max(d.get(a,0),d.get(b,0))
 q['ledger']=dict(operations=len(q['source']),M=count['*'],A=count['+']+count['-'],degree_upper=d[q['output']])
 ans=account(q);saved=p['ledger'];require(all(ans[k]==saved['naive_degree_upper' if k=='degree_upper' else k] for k in ans),'full complete ledger metadata')
 require(saved['certificate_operations']==ans['operations']-17 and saved['certificate_M']==ans['M']-6 and saved['certificate_A']==ans['A']-11,'charged seventeen-row finalizer ledger')
 require(saved['positive_witnesses']==len(q['free'])-1==len(p['edges'])+26,'actual full witness interface')
 require(saved['controller_states']==len({v for e in p['edges'] for v in e[:2]}) and saved['comparisons']==6 and saved['finalizer_operations']==17,'state/equation count metadata')
 return ans

def outer_coefficients(p,T):
 # Expanded independently in supplied hats and P,D,x,H,Zhat. D is first
 # proved to equal the complete paid ordinary-input prefix, not a new input.
 require(p['source'][:5]==T['source'][:5],'unchanged complete height prefix')
 require(T['source'][:5]==[['history__input_product','*',24,'x'],['history__u','+','history__input_product',13],['D','+','history__u','height_slack'],['history__c0','-','D',1],['B','*',16,'D']],'literal retained ordinary loader')
 pp=atom('P');dd=atom('D');bb=scale(16,dd);hh=[atom('H'+str(i)) for i in range(4)]
 ee=[add(atom('controller__edge_hat'+str(i+1)),const(1),-1) for i in range(len(p['edges']))]
 zz=[add(atom('Zhat'+str(i)),const(1),-1) for i in range(8)]
 ss=[total(e for e,edge in zip(ee,p['edges']) if edge[2]==l) for l in range(1,9)];jj=total(ee)
 hc=total(mul(e,power(pp,j)) for e,j in zip(ee,p['positions']));mc=mul(jj,total(power(pp,j) for j in range(p['m'])))
 hb=total(mul(hh[(i//2)^1],power(pp,i)) for i in range(8));zb=total(mul(z,power(pp,i)) for i,z in enumerate(zz));sp=total(mul(s,power(pp,i)) for i,s in enumerate(ss))
 tt=power(pp,p['m']+8);t2=power(pp,2*p['m']+8);rr=mul(add(scale(2,dd),const(1),-1),mc)
 H=total([hb,mul(power(pp,8),hc),mul(tt,hb),mul(bb,t2)])
 M=total([mul(add(bb,const(1),-1),sp),mul(power(pp,8),mc),mul(tt,rr),scale(2,t2)])
 Z=total([zb,mul(power(pp,8),hc),mul(tt,hb)]);q=scale(32,mul(bb,t2))
 cuts={'computed_J':jj,'physical_Sbatch':sp,'controller__edge_word':hc,'controller__flow_left':total(scale(edge[0],e) for edge,e in zip(p['edges'],ee)), 'controller__flow_right':mul(bb,total(scale(edge[1],e) for edge,e in zip(p['edges'],ee))), 'controller__origin_mask':mc,'joint_scale':tt,'range_body_scale':t2}
 for i in range(4):cuts['history__dS'+str(i)]=add(ss[2*i],ss[2*i+1],-1)
 require(set(cuts)==set(p['cuts']),'exact declared cut interface')
 targets={p['cuts'][k]:v for k,v in cuts.items()}
 targets.update({P_NAME:add(mul(add(bb,const(1),-1),jj),const(1)), 'selection__Hbatch':hb,'selection__Zbatch':zb,'range_H':H,'range_M':M,'range_Z':Z,'selection__q':q,'selection__padded_A':add(scale(16,H),const(13)),'selection__padded_B':add(scale(16,M),const(10)),'selection__F3':add(scale(16,Z),const(8))})
 u=add(scale(24,atom('x')),const(13));c0=add(dd,const(1),-1)
 for i in range(4):
  delta=add(add(zz[2*i],zz[2*i+1],-1),mul(c0,add(ss[2*i],ss[2*i+1],-1)),-1)
  targets['history__delta'+str(i)]=delta
  targets['history__left'+str(i)]=mul(bb,add(hh[i],delta))
  targets['history__right'+str(i)]=add(add(hh[i],mul(dd if i%2 else c0,pp)),add(c0,u) if i%2 else dd,-1)
 targets['joint_bound_unit']=add(total(hh+[atom('Zhat'+str(i)) for i in range(8)]+[atom('selection__bound_global')]),pp,-1)
 for n,want in targets.items():
  overrides={'D':dd}
  if n!=P_NAME:overrides[P_NAME]=pp
  require(poly_cone(p['source'],p['free'],n,overrides)==want,'expanded full outer polynomial '+n)
 nq,nh,nm,nz=[atom(n) for n in ('q','H','M','Z')]
 fields=[total([nq,scale(-16,nh),scale(-16,nm),scale(16,nz),const(-15)]),add(scale(16,add(nh,nz,-1)),const(4)),add(scale(16,add(nm,nz,-1)),const(2)),add(scale(16,nz),const(8))]
 want=total(mul(f,power(nq,i)) for i,f in enumerate(fields))
 require(poly_cone(p['source'],p['free'],'selection__bs_packed',{'selection__q':nq,'range_H':nh,'range_M':nm,'range_Z':nz})==want,'all four truth-field index coefficients')
 return len(targets)+1

def static_interface(T,p):
 # Independent conditional DAG proof: the only permitted substitutions are
 # twelve already-expanded ports and four actual product/tail row changes.
 reference=[]
 for n,o,a,b in T['source']+T['polynomial_finalizer']:
  if n in p['cuts'] or n.startswith(('controller__flow','selection__Spack')) or n=='range_total_scale':continue
  if n=='selection__Mbatch':b='physical_Sbatch'
  if n=='range_Bminus_shift':b=2
  if n=='selection__q':a,b=32,'range_Bshift'
  if n=='shifted_native_quotient':b='packed_z_product'
  reference.append([n,o,a,b])
 ring=Ring();inputs={n:ring.leaf(('free',n)) for n in p['free']};symbols={n:ring.leaf(('cut',n)) for n in p['cuts']}
 def evaluate(rows,actual):
  env=dict(inputs)
  override={p['cuts'][n]:v for n,v in symbols.items()} if actual else symbols
  if not actual:env.update(override)
  pending=list(rows)
  while pending:
   nextrows=[]
   for n,o,a,b in pending:
    if any(type(v)is str and v not in env for v in (a,b)):nextrows.append([n,o,a,b]);continue
    get=lambda v:env[v] if type(v)is str else ring.number(v)
    env[n]=override[n] if actual and n in override else ring.op(o,get(a),get(b))
   require(len(nextrows)<len(pending),'closed independent static DAG');pending=nextrows
  return env
 old=evaluate(reference,False);new=evaluate(p['source'],True)
 shared=set(old)&{r[0] for r in p['source']}
 require(all(old[n]==new[n] for n in shared),'every retained static computed expression')
 require(old['joint_outer_output']==new['joint_outer_output'],'entire same-graph polynomial interface')
 for (a,b),(c,d) in zip(T['comparisons'],p['comparisons']):
  val=lambda v,e:e[v] if type(v)is str else ring.number(v)
  require(ring.op('-',val(a,old),val(b,old))==ring.op('-',val(c,new),val(d,new)),'whole comparison interface')
 rows={r[0]:r for r in p['source']}
 expected=[[n,o,p['cuts'].get(a,a),p['cuts'].get(b,b)] for n,o,a,b in T['polynomial_finalizer']]
 require([rows[r[0]] for r in expected]==expected,'literal seventeen-row finalizer')
 require(p['parameters']==['x'] and p['domains']=={'parameters':'positive integers','auxiliaries':'positive integers'},'actual positive ordinary interface')
 require(p['free']==['x']+[n for n in T['auxiliaries'] if not n.startswith('controller__edge_hat')]+['controller__edge_hat'+str(i+1) for i in range(len(p['edges']))],'full supplied native interface preserved')
 require(p['auxiliaries']==p['free'][1:],'complete witness list')
 return len(shared)

def degree_check(p):
 rows=p['source'];defs={n:(o,a,b) for n,o,a,b in rows}
 X,A,C,G,H='selection__wn2','selection__R12','selection__R10a','selection__gam','selection__a4m5'
 guards={'selection__R15':('-','selection__L15','selection__Ac2'),'selection__L15':('*','selection__R14','selection__R14'),'selection__R14':('+','selection__D1',G),'selection__D1':('+',X,'selection__cam2'),'selection__cam2':('*',C,A),'selection__A':('+','selection__a_square',H),'selection__a_square':('*',A,A),H:('+','selection__a4',3),'selection__a4':('*',4,A),G:('*','selection__ga',H),'selection__Ac2':('*','selection__A','selection__c2'),'selection__c2':('*',C,C)}
 require(all(defs[n]==v for n,v in guards.items()),'actual cancellation cone producer guards')
 # Independently expand the cofactor identity d^2-Delta*c^2
 # = v*(v+2ac)-H*c^2, v=X+gamma, before using its degree.
 x,a,c,g,h=[atom(n) for n in ('X','a','c','gamma','H')];v=add(x,g);ac=mul(a,c)
 left=add(power(add(ac,v),2),mul(add(power(a,2),h),power(c,2)),-1)
 right=add(mul(v,add(v,scale(2,ac))),mul(h,power(c,2)),-1)
 require(left==right,'cofactor cancellation full ring identity')
 certificates=[]
 target=73+2*(29*(2*p['m']+8)+7*p['m']+106)
 expected=[1255,2234,1652,980,980,1960,2] if p['m']==64 else [679,1210,884,532,532,1064,2]
 for prime in (2147483647,1000000007):
  weights={n:1+int(sha((n+':independent-degree').encode()),16)%127 for n in p['free']}
  env={n:(1,w%prime) for n,w in weights.items()}
  def plus(a,b,sign=1):
   d=max(a[0],b[0]);return d,((a[1] if a[0]==d else 0)+sign*(b[1] if b[0]==d else 0))%prime
  def times(a,b):return a[0]+b[0],a[1]*b[1]%prime
  for n,o,a,b in rows:
   av=env[a] if type(a)is str else (0,a%prime);bv=env[b] if type(b)is str else (0,b%prime)
   if n=='selection__R15':
    vv=plus(env[X],env[G]);twiceac=times((0,2),times(env[A],env[C]));norm=times(vv,plus(vv,twiceac));env[n]=plus(norm,times(env[H],times(env[C],env[C])),-1)
   else:env[n]=times(av,bv) if o=='*' else plus(av,bv,1 if o=='+' else -1)
  require([env[n][0] for n in FACTORS]==expected,'independent seven factor upper degrees')
  require(env['joint_outer_positive'][0]==6 and env['joint_outer_output'][0]==target and env['joint_outer_output'][1]!=0,'nonzero attained complete source coefficient')
  require(target==sum(expected)+6==p['degree_certificate']['exact_degree']==p['ledger']['exact_degree']==p['ledger']['degree_upper'],'complete exact degree metadata')
  require(p['degree_certificate']['factor_degrees']==dict(zip(FACTORS,expected)),'literal reported factor degrees')
  certificates.append(dict(prime=prime,coefficient=env['joint_outer_output'][1]))
 return dict(exact_degree=target,factor_degrees=expected,weights=weights,certificates=certificates)

def declared_maps(edges,m):
 result=[list(range(len(edges)))]
 for backwards in (False,True):
  order=sorted(range(len(edges)),key=lambda i:(edges[i][2],-i if backwards else i))
  grouped=[order.index(i) for i in range(len(edges))];result.append(grouped)
  slots=[None]*len(edges);counts=Counter()
  for i in (reversed(range(len(edges))) if backwards else range(len(edges))):
   label=edges[i][2];q=label-1+8*counts[label];counts[label]+=1
   if q<m:slots[i]=q
  unused=iter(sorted(set(range(m))-{v for v in slots if v is not None}))
  slots=[next(unused) if v is None else v for v in slots];result.append(slots)
 require(len(set(map(tuple,result)))==5,'five distinct declared maps')
 return result

def census_metadata(saved):
 expected={(tag,tuple(pos),packing) for tag,p in saved['packets'].items() for pos in declared_maps(p['edges'],p['m']) for packing in ('direct','shared','grouped')}
 actual=[(r['graph'],tuple(r['positions']),r['packing']) for r in saved['records']]
 require(len(actual)==len(set(actual))==60 and set(actual)==expected,'complete distinct declared sixty-recipe census')
 for tag,p in saved['packets'].items():
  records=[r for r in saved['records'] if r['graph']==tag]
  best=min(records,key=lambda r:(r['ledger']['operations'],r['ledger']['M'],r['packing'],r['positions']))
  require(best['positions']==p['positions'] and best['packing']==p['packing']=='direct','winner minimum within recorded metadata')
  require(best['ledger']==p['ledger'] and best['source_sha256']==sha(json.dumps(p['source'],separators=(',',':')).encode()),'saved complete winner matches its census row')
 require(sum(r['ledger']['operations'] for r in saved['records'])==28436,'reported census operation sum')
 return dict(recipes=60,metadata_only_nonwinner_recipes=56,full_sources_independently_audited=4)

def matrices_and_language():
 def mat(word):
  out=[[int(i==j) for j in range(4)] for i in range(4)]
  for l in word:
   row=(l-1)//2;out[row]=[x+(1 if l%2 else -1)*y for x,y in zip(out[row],out[row^1])]
  return out
 def product(a,b):return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
 eye=mat(());r=mat(RT);bm=mat(BM);am=mat(AM)
 require(r==[[1,-1,0,0],[1,0,0,0],[0,0,1,-1],[0,0,1,0]],'chronological R action')
 require(bm==[[1,5,0,0],[0,1,0,0],[0,0,1,5],[0,0,0,1]],'chronological B action')
 require(am==product(bm,r) and mat(AM+inverse(BM))==r,'chronological Nielsen identities')
 require(all(product(mat(w),mat(inverse(w)))==eye for w in (AM,BM,RT)),'actual physical inverses')
 orbit=[];v=(0,1)
 for _ in range(6):orbit.append(v);v=((v[0]-v[1])%5,v[0])
 require(v==(0,1) and len(set(orbit))==6 and {b for a,b in orbit if a==1}=={0,1},'finite group orbit modulo five')
 require((24+13)%5 not in (0,1),'ordinary x1 excluded')
 # Affine identity in symbolic u under u=5e+1. This proves the infinite
 # accepted progression algebraically, beyond finite outer fixtures.
 e=atom('e');u=add(scale(5,e),const(1));after_r=(add(const(1),u,-1),const(1))
 require(add(after_r[0],scale(5,e))=={} and after_r[1]==const(1),'all e identity R B^e endpoint')
 return dict(matrix_R=r,matrix_B=bm,matrix_A=am,mod5_orbit=[list(v) for v in orbit],sufficient_positive_residue=2,necessary_positive_residues=[2,3],excluded_input=1,empty_identity_cannot_reach_endpoint=True)

def outer_fixture(p,x):
 u=24*x+13;e=(u-1)//5;word=RT+BM*e
 require(word==AM+BM*(e-1) and e>=1,'literal accepted original macro decomposition')
 choices=path(p['edges'],word);state=[1,u,1,u];before=[]
 for l in word:
  before.append(list(state));j=(l-1)//2;state[j]+=(1 if l%2 else -1)*state[j^1]
 require(state==[0,1,0,1] and len(word)==48*x+28,'complete genuine paired trajectory')
 D=128 if x==2 else 256;B=16*D;P=B**len(word);J=(P-1)//(B-1)
 require(D>u and D>1+max(abs(v) for st in before+[state] for v in st),'height/range sufficient margin')
 radixpowers=[B**i for i in range(len(word))];v={'x':x,'height_slack':D-u}
 for j in range(4):v['H'+str(j)]=sum((D-1+st[j])*b for st,b in zip(before,radixpowers))
 for l in range(1,9):v['Zhat'+str(l-1)]=1+sum((D-1+st[((l-1)//2)^1])*b for st,b,label in zip(before,radixpowers,word) if label==l)
 for edge in range(len(p['edges'])):v['controller__edge_hat'+str(edge+1)]=1+sum(b for i,b in zip(choices,radixpowers) if i==edge)
 v['selection__bound_global']=P+1-sum(v['H'+str(j)] for j in range(4))-sum(v['Zhat'+str(j)] for j in range(8))
 require(min(v.values())>0 and B>p['m'],'actual positive outer witness coordinates')
 definitions={n:(o,a,b) for n,o,a,b in p['source']};env=dict(v)
 def get(n):
  if type(n)is int:return n
  if n not in env:
   o,a,b=definitions[n];a,b=get(a),get(b);env[n]=a*b if o=='*' else a+b if o=='+' else a-b
  return env[n]
 require(get(P_NAME)==P and get(p['cuts']['computed_J'])==J,'literal paid P/repunit source')
 require(all(get(a)==get(b) for i,(a,b) in enumerate(p['comparisons']) if i!=4),'all five true outer equations')
 require(get('joint_bound_unit')==1,'true joint factor')
 H,M,Z=[get(n) for n in ('range_H','range_M','range_Z')];q=get('selection__q');Q=q//16
 require(H&M==Z and 0<=max(H,M,Z)<Q and q==32*B*P**(2*p['m']+8),'actual whole joined AND and paid product scale')
 fields=[16*(Q-H-M+Z)-15,16*(H-Z)+4,16*(M-Z)+2,16*Z+8]
 require(min(fields)>0 and sum(fields)==q-1 and all(fields[i]&fields[j]==0 for i in range(4) for j in range(i)),'positive disjoint truth fields')
 return dict(x=x,u=u,D=D,B=B,duration=len(word),edge_path=choices,q_bit_length=q.bit_length(),all_outer_equations=True,full_AND=True,native_Pell_zero_materialized=False)

def verify(root):
 saved,blobs,manifest=authenticate(root)
 T=json.loads(blobs['group_projective_label_aligned_lanes.json'])['source']['source_example']
 require(T['m']==8 and T['compute_length'] is True and T['codes']==[[8,6,4,2,7,5,3,1]],'actual authenticated static template')
 packets=saved['packets'];require(set(packets)=={'private','shared','nielsen','folded'},'exact four maintained saved sources')
 graph=graph_check(packets,json.loads(blobs['group_inverse_stallings_controller.json'])['core']['edges'])
 records={};fixtures=[]
 for tag,p in sorted(packets.items()):
  ledger=source_ledger(p);outer=outer_coefficients(p,T);static=static_interface(T,p);degree=degree_check(p)
  expected={'private':(492,191,301,74,45),'shared':(432,178,254,56,27),'nielsen':(371,150,221,54,25),'folded':(376,147,229,54,13)}[tag]
  require((ledger['operations'],ledger['M'],ledger['A'],p['ledger']['positive_witnesses'],p['ledger']['controller_states'])==expected,'independent complete winner totals')
  records[tag]=dict(ledger=ledger,outer_polynomial_identities=outer,static_register_identities=static,whole_comparisons=6,whole_output_identity=True,degree=degree)
  for x in (2,7):fixtures.append(dict(graph=tag,**outer_fixture(p,x)))
 require(len(saved['accepting_outer_histories'])==8,'eight saved outer fixtures')
 for row in saved['accepting_outer_histories']:
  p=packets[row['graph']];word=row['word'];ids=row['edge_path'];require(len(ids)==len(word)==48*row['x']+28,'reported finite fixture duration')
  state=0
  for i,l in zip(ids,word):
   a,b,label=p['edges'][i];require(a==state and label==l,'reported actual graph path');state=b
  require(state==0 and not row['full_native_pell_zero_materialized'],'reported endpoint/nonmaterialization scope')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,dependency_pins=manifest,records=records,graph=graph,census=census_metadata(saved),matrix_language=matrices_and_language(),outer_fixtures=fixtures,totals=dict(dependency_files=len(manifest),complete_sources=4,paid_live_gates=sum(r['ledger']['operations'] for r in records.values()),outer_polynomial_identities=sum(r['outer_polynomial_identities'] for r in records.values()),static_register_identities=sum(r['static_register_identities'] for r in records.values()),whole_comparisons=24,whole_output_identities=4,exact_degree_certificates=8,genuine_outer_fixtures=8),scope='Independent four saved complete circuits; remaining56 schedules checked as census metadata only. All-value static-interface and outer-port proofs, same represented positive-input predicate via reviewed native converse and subgroup proof. No author/historical execution, no cross-graph polynomial equality or zero-fiber bijection, no materialized native Pell zero, no numerical universality or global optimum. Reviewer authored the separately frozen graph packet, not this arithmetic compiler.')

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,required=True);parser.add_argument('--output',type=Path);parser.add_argument('--expect',type=Path);args=parser.parse_args();result=verify(args.root)
 if args.expect:require(typed(result,json.loads(args.expect.read_text())),'exact typed independent saved receipt')
 if args.output:args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=result['status'],totals=result['totals'],ledgers={k:v['ledger'] for k,v in result['records'].items()})))
if __name__=='__main__':main()
