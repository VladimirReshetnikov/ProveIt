#!/usr/bin/env python3
"""Paid shared-typing matrix compiler with finite macro-automaton sharing.
Reads pinned saved sources; imports no historical modules and runs no
historical builders or suites. An authenticated isolated path-flow planner
supplies only the specialized baseline.
"""
import argparse,ast,copy,hashlib,itertools,json,random
from collections import Counter,defaultdict,deque
from pathlib import Path
PINS={'group_shared_typing_matrix_compiler.py': '3ef20018fb7f4e31d1a0ebc9cac2914fe506dd6d16fd71bfe6ced6c1374eb04a', 'group_shared_typing_matrix_compiler.json': 'ec52b3502de67c578176dfab0ae347158feedc0a9d9fd65c761c0ef5d183118f', 'group_shared_typing_matrix_compiler.md': 'c8830b16ad8f9ce973e21eb68199949a331c30b76a04d82664c20ac44a400ae3', 'group_complete_matrix_compiler.py': '9877dbab8c5a44d27615bec6d1ba0a2eebe79f19b288609adf0b95f00ac6fef7', 'group_complete_matrix_compiler.md': 'b474c7f7ab92f6067abd417f34cade3403cbc53364b6b33bdf61b1755d04ecb1', 'group_regular_macro_controller.py': '159a51c9171309ef68d13e1662e4b8e3b6e3d752ab1199ed021084e4564a8a8d', 'group_regular_macro_controller.md': '91d8932360bdc998811c5727c983602d37edc9943fab0114f00532a6bba49ec5', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_four_register_canonical_history47.md': '78c80b9cdd178ce70d40238cd773d67720bac11b194d7581725b0c225f1b6c52', 'group_four_register_history.md': 'c77c586185d7acf918b4123e301c04db4d868c302fc24a6385538f93c7e6625b', 'group_linked_binary_geometry47.md': '4be87c7429b89e171417ce54065b575947cea21e9bb1986112cee0ad0a259f96'}
FIXTURE=((1,1,2),(2,3,2),(4,5))
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def pad(edges):
 m=2
 while m<len(edges):m*=2
 return list(edges)+[(0,0,0)]*(m-len(edges))
def separate(codes):
 need(all(all(type(l)is int and 1<=l<=8 for l in w)for w in codes),'physical macro alphabet')
 edges=[(0,0,0)];next_state=1
 for word in codes:
  state=0
  for i,label in enumerate(word):
   dest=0 if i==len(word)-1 else next_state
   if dest:next_state+=1
   edges.append((state,dest,label));state=dest
 return edges

def share(codes):
 need(all(all(type(l)is int and 1<=l<=8 for l in w)for w in codes),'physical macro alphabet')
 codes=sorted(set(tuple(w)for w in codes));proper={()}
 for word in codes:proper.update(word[:i]for i in range(1,len(word)))
 outgoing={p:set()for p in proper}
 for word in codes:
  for i,label in enumerate(word):outgoing[word[:i]].add((label,word[:i+1]if i<len(word)-1 else()))
 # The hub stays distinguished. Proper-prefix transitions strictly increase
 # prefix length; bottom-up identical labeled continuations are bisimilar.
 classes={():0};signatures={};representatives={}
 for p in sorted(proper-{()},key=lambda p:(-len(p),p)):
  sig=tuple(sorted((label,classes[q])for label,q in outgoing[p]))
  if sig not in signatures:signatures[sig]=len(signatures)+1;representatives[signatures[sig]]=sig
  classes[p]=signatures[sig]
 hub=tuple(sorted((label,classes[q])for label,q in outgoing[()]))
 raw={(0,0,0)}
 for label,q in hub:raw.add((0,q,label))
 for state,sig in representatives.items():
  for label,q in sig:raw.add((state,q,label))
 # Deterministic state relabeling puts most incidences at cheap numeral1.
 states=sorted(representatives,key=lambda s:(-sum(s in(a,b)for a,b,l in raw),s));rename={0:0,**{s:i+1 for i,s in enumerate(states)}}
 edges=sorted({(rename[a],rename[b],l)for a,b,l in raw},key=lambda e:(e!=(0,0,0),e))
 return edges,dict(proper_prefixes=[list(p)for p in sorted(proper)],prefix_class=[dict(prefix=list(p),state=rename[c])for p,c in sorted(classes.items())],class_continuations={str(rename[k]):[[l,rename[v]]for l,v in sig]for k,sig in representatives.items()},root_continuations=[[l,rename[v]]for l,v in hub])

def language_equivalence(left,right):
 def step(edges,S,label):return frozenset(b for a,b,l in edges if a in S and l==label)
 start=(frozenset({0}),frozenset({0}));seen={start};todo=deque([start])
 while todo:
  a,b=todo.popleft();need((0 in a)==(0 in b),'exact automaton accepting-state equivalence')
  for label in range(9):
   pair=step(left,a,label),step(right,b,label)
   if pair not in seen:seen.add(pair);todo.append(pair)
 return len(seen)

class Emitter:
 def __init__(self):self.rows=[];self.serial=0;self.memo={}
 def gate(self,op,a,b,name=None):
  if op=='+'and a==0:return b
  if op=='+'and b==0:return a
  if op=='-'and b==0:return a
  if op=='*'and(a==0 or b==0):return 0
  if op=='*'and a==1:return b
  if op=='*'and b==1:return a
  key=(op,tuple(sorted((a,b),key=repr))if op in('+','*')else(a,b))
  if key in self.memo:return self.memo[key]
  name=name or 'controller__flow_'+str(self.serial);self.serial+=1;self.rows.append([name,op,a,b]);self.memo[key]=name;return name
 def total(self,values):
  out=0
  for value in values:out=self.gate('+',out,value)
  return out

def general_flow(edges,by):
 E=Emitter();hats=[f'controller__edge_hat{i}'for i in range(len(edges))]
 groups={k:[i for i,e in enumerate(edges)if e[by]==k]for k in sorted({e[by]for e in edges})}
 raw={k:E.total([hats[i]for i in ids])for k,ids in groups.items()};checksum=E.total(list(raw.values()));split=len(E.rows)
 def word(coordinate):
  parts=[]
  for k in sorted({e[coordinate]for e in edges}-{0}):
   ids=[i for i,e in enumerate(edges)if e[coordinate]==k]
   group=raw[k]if coordinate==by else E.total([hats[i]for i in ids]);parts.append(E.gate('*',k,group))
  return E.gate('-',E.total(parts),sum(e[coordinate]for e in edges))
 src,dst=word(0),word(1);rhs=E.gate('*','B',dst)
 return dict(checksum_rows=E.rows[:split],flow_rows=E.rows[split:],checksum=checksum,pair=[src,rhs],orientation='source'if by==0 else'target')

def build(template,codes,edges,flow_method='generic',alpha=24,beta=12,sparse_module=None,margin=None):
 m=len(edges);h=m.bit_length()-1;need(m>=2 and m==1<<h and all(0<=a<m and 0<=b<m and 0<=l<=8 for a,b,l in edges),'fixed edge bounds')
 margin=m if margin is None else margin;need(type(margin)is int and margin>=m,'paid fixed radix margin')
 # Reuse only the literal history, selector and geometry blocks. This is the
 # actual shared-typing source, with no path-specific sparse-flow assumptions.
 old=template['source'];sel0=next(i for i,r in enumerate(old)if r[0]=='selection__P2');sel1=next(i for i,r in enumerate(old)if r[0]=='controller__source_weighted0');geo0=next(i for i,r in enumerate(old)if r[0].startswith('geometry__'))
 hist=copy.deepcopy(old[:47]);need(hist[0]==['history__input_product','*',24,'x']and hist[1]==['history__r','+','history__input_product',12],'literal input prefix');hist[0][2]=alpha;hist[1][3]=beta
 selectors=copy.deepcopy(old[sel0:sel1]);geometry=copy.deepcopy(old[geo0:]);need(len(selectors)==126 and len(geometry)==47,'unchanged complete native blocks')
 prefix=[['controller__cell_minus1','-','B',1],['controller__geometry_product','*','controller__cell_minus1','J'],['controller__geometry_power','+','controller__geometry_product',1],['controller__radix_margin','+',margin,'controller__radix_beta']]
 hats=[f'controller__edge_hat{i}'for i in range(m)]
 if flow_method=='dense':
  cs=[];acc=hats[0]
  for i,v in enumerate(hats[1:],1):cs.append([f'controller__edge_sum{i}','+',acc,v]);acc=cs[-1][0]
  flow=[];outputs=[]
  for coordinate,tag in((0,'source'),(1,'target')):
   terms=[]
   for i,e in enumerate(edges):n=f'controller__{tag}_weighted{i}';flow.append([n,'*',e[coordinate],hats[i]]);terms.append(n)
   value=terms[0]
   for i,term in enumerate(terms[1:],1):n=f'controller__{tag}_sum{i}';flow.append([n,'+',value,term]);value=n
   n=f'controller__{tag}_word';flow.append([n,'-',value,sum(e[coordinate]for e in edges)]);outputs.append(n)
  flow.append(['controller__shifted_target','*','B',outputs[1]]);plan=dict(checksum_rows=cs,flow_rows=flow,checksum=acc,pair=[outputs[0],'controller__shifted_target'],orientation='dense')
 elif flow_method=='path_sparse':
  need(sparse_module is not None,'pinned path planner');tmp=sparse_module({'edges':edges,'m':m})
  ren=lambda x:'controller__'+x if type(x)is str and x not in('B','P','J')else x
  plan={'checksum_rows':[[ren(n),o,ren(a),ren(b)]for n,o,a,b in tmp['checksum_source']], 'flow_rows':[[ren(n),o,ren(a),ren(b)]for n,o,a,b in tmp['flow_source']], 'checksum':ren(tmp['total']),'pair':[ren(x)for x in tmp['pair']],'orientation':'historical_private_paths'}
 else:
  plans=[general_flow(edges,by)for by in(0,1)];plan=min(plans,key=lambda p:(len(p['checksum_rows'])+len(p['flow_rows']),sum(r[1]=='*'for r in p['flow_rows']),p['orientation']))
 prefix+=plan['checksum_rows'];prefix.append(['controller__edge_checksum','+','J',m]);powers=['P']
 for i in range(1,h):n=f'controller__lane_power{i}';prefix.append([n,'*',powers[-1],powers[-1]]);powers.append(n)
 factors=[]
 for i,power in enumerate(powers):n=f'controller__lane_factor{i}';prefix.append([n,'+',power,1]);factors.append(n)
 rep=factors[0]
 for i,factor in enumerate(factors[1:],1):n=f'controller__lane_repunit{i}';prefix.append([n,'*',rep,factor]);rep=n
 value=hats[-1]
 for i in range(m-2,-1,-1):n=f'controller__edge_pack_mult{i}';prefix.append([n,'*','P',value]);value=f'controller__edge_pack_sum{i}';prefix.append([value,'+',hats[i],n])
 prefix.extend([['controller__edge_word','-',value,rep],['controller__origin_mask','*','J',rep]])
 for row in selectors:
  if row[0]=='joint_Pm':row[2:]=[powers[-1],powers[-1]]
 ports=[];port_pairs=[];port_cost=0
 for label in range(1,9):
  ids=[i for i,e in enumerate(edges)if e[2]==label]
  value=1 if not ids else hats[ids[0]]
  if len(ids)>1:
   for j,i in enumerate(ids[1:],1):n=f'controller__port{label}_sum{j}';ports.append([n,'+',value,hats[i]]);value=n
   n=f'controller__port{label}';ports.append([n,'-',value,len(ids)-1]);value=n;port_cost+=len(ids)
  port_pairs.append([value,f'Shat{label-1}'])
 pairs=copy.deepcopy(template['comparisons'][:22])+[['controller__geometry_power','P'],['controller__radix_margin','B'],[plan['checksum'],'controller__edge_checksum'],plan['pair']]+port_pairs+copy.deepcopy(template['comparisons'][34:])
 rows=hist+prefix+selectors+plan['flow_rows']+ports+geometry
 aux=[n for n in template['auxiliaries']if not n.startswith('controller__edge_hat')];pos=aux.index('controller__radix_beta');aux[pos:pos]=hats
 return dict(codes=[list(c)for c in codes],edges=[list(e)for e in edges],m=m,radix_margin_minimum=margin,alpha=alpha,beta=beta,source=rows,comparisons=pairs,parameters=['x'],auxiliaries=aux,flow_plan=plan,projection_additions=port_cost)

def finalize(p):
 rows=copy.deepcopy(p['source'])
 for i,(a,b)in enumerate(p['comparisons']):rows.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 value='square_0'
 for i in range(1,len(p['comparisons'])):n=f'sum_{i}';rows.append([n,'+',value,f'square_{i}']);value=n
 p['polynomial_source']=rows;p['output']=value
 return p

def execute(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def ledger(rows,free,roots):
 d={n:1 for n in free};defs={};M=0
 for n,o,a,b in rows:
  need(n not in d and o in('+','-','*'),'fresh gate');need(all(type(v)is int or type(v)is str and v in d for v in(a,b)),'closure')
  da=d[a]if type(a)is str else 0;db=d[b]if type(b)is str else 0;d[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);M+=o=='*'
 seen=set();used=set();todo=list(roots)
 while todo:
  n=todo.pop()
  if type(n)is int:continue
  if n not in defs:used.add(n)
  elif n not in seen:seen.add(n);todo.extend(defs[n])
 need(seen==set(defs)and used==set(free),'full source liveness')
 return dict(operations=len(rows),M=M,A=len(rows)-M,degree_upper=max(d[n]if type(n)is str else 0 for n in roots))

def poly_atom(v):return {(v,):1}if type(v)is str else({():v}if v else{})
def poly_op(op,a,b):
 out=Counter()
 if op=='*':
  for u,c in a.items():
   for v,d in b.items():out[tuple(sorted(u+v))]+=c*d
 else:
  out.update(a)
  for v,d in b.items():out[v]+=d if op=='+'else-d
 return {m:c for m,c in out.items()if c}
def local_polynomials(rows):
 env={}
 def get(v):return env[v]if v in env else poly_atom(v)
 for n,o,a,b in rows:env[n]=poly_op(o,get(a),get(b))
 return env,get

def formal_controller_identity(p,dense):
 rows=[r for r in p['source']if r[0].startswith('controller__')]
 oldrows=[r for r in dense['source']if r[0].startswith('controller__')]
 env,get=local_polynomials(rows);oe,oget=local_polynomials(oldrows)
 residuals=[]
 for a,b in p['comparisons'][22:34]:residuals.append(poly_op('-',get(a),get(b)))
 oldres=[poly_op('-',oget(a),oget(b))for a,b in dense['comparisons'][22:34]]
 need(residuals==oldres,'twelve exact controller residual coefficient identities')
 retained=[r for r in p['source']if not r[0].startswith('controller__')]
 need(retained==[r for r in dense['source']if not r[0].startswith('controller__')],'all noncontroller instructions unchanged')
 need(p['comparisons'][:22]+p['comparisons'][34:]==dense['comparisons'][:22]+dense['comparisons'][34:],'all other comparisons unchanged')
 needed={v for n,o,a,b in retained for v in(a,b)if type(v)is str and v.startswith('controller__')}
 needed|={v for ab in p['comparisons'][:22]+p['comparisons'][34:]for v in ab if type(v)is str and v.startswith('controller__')}
 for v in needed:need(get(v)==oget(v),'exact live controller cut '+v)
 # The noncontroller rows have identical order and operands; their literal
 # ring-polynomial identities follow inductively from these complete cuts.
 return dict(residual_coefficient_identities=len(residuals),downstream_cut_identities=len(needed),downstream_cuts=sorted(needed),unchanged_instructions=len(retained),unchanged_comparisons=35)

def path_for_word(edges,word):
 states={0:[]}
 for label in word:
  nxt={}
  for state,path in sorted(states.items()):
   for i,(a,b,l)in enumerate(edges):
    if a==state and l==label and b not in nxt:nxt[b]=path+[i]
  states=nxt
 need(0 in states,'accepted outer fixture');return states[0]
def outer_fixture(p,word):
 # Genuine positive controller interface; neither native Pell core is
 # materialized. The matrix target is not asserted for these control words.
 t=len(word);need(t>=2,'common linked duration');B=8*4**t;P=B**t;J=sum(B**i for i in range(t));path=path_for_word(p['edges'],word)
 v={'B':B,'P':P,'J':J,'controller__radix_beta':B-p['radix_margin_minimum']}
 for i in range(p['m']):v['controller__edge_hat'+str(i)]=1+sum(B**j for j,e in enumerate(path)if e==i)
 for l in range(1,9):v['Shat'+str(l-1)]=1+sum(B**j for j,a in enumerate(word)if a==l)
 need(all(type(a)is int and a>0 for a in v.values()),'all supplied outer ports positive')
 env=execute([r for r in p['source']if r[0].startswith('controller__')],v)
 value=lambda a:env[a]if type(a)is str else a
 need(all(value(a)==value(b)for a,b in p['comparisons'][22:34]),'all twelve controller comparisons')
 H=env['controller__edge_word'];M=env['controller__origin_mask']
 need(H&M==H and 0<=H<=M<P**p['m'],'actual subset typing')
 need([p['edges'][i][2]for i in path]==list(word),'same physical word')
 return dict(duration=t,subset=True,positive_ports=len(v),state_path=[p['edges'][i][0]for i in path]+[0])

def verify(root):
 root=Path(root);blobs={}
 for n,h in PINS.items():data=(root/n).read_bytes();need(sha(data)==h,'pin '+n);blobs[n]=data
 template=json.loads(blobs['group_shared_typing_matrix_compiler.json'])['source']['packets'][0];need(template['codes']==[]and template['m']==2,'literal fixed template')
 # This is an actual named repository verification fixture, not invented sizes.
 tree=ast.parse(blobs['group_regular_macro_controller.py']);fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef)and n.name=='verify');examples=ast.literal_eval(next(n.value for n in fn.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='examples'for t in n.targets)));need(FIXTURE in examples,'authenticated named controller fixture')
 # Isolate only the old guarded path-flow planner, not imports/builders/tests.
 st=ast.parse(blobs['group_sparse_macro_flow.py']);groups=next(n for n in st.body if isinstance(n,ast.FunctionDef)and n.name=='groups');fn=copy.deepcopy(next(n for n in st.body if isinstance(n,ast.FunctionDef)and n.name=='rewrite_controller'))
 stop=next(i for i,n in enumerate(fn.body)if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='old_source'for t in n.targets));fn.body=fn.body[:stop]+[ast.Return(ast.Call(ast.Name('locals',ast.Load()),[],[]))];ast.fix_missing_locations(fn);env={'Counter':Counter};exec(compile(ast.Module(body=[groups,fn],type_ignores=[]),'pinned_path_planner','exec'),env);planner=env['rewrite_controller']
 raw=separate(FIXTURE);shared,certificate=share(FIXTURE);need((len(raw),len(shared))==(9,8),'actual active-edge saving');counts=Counter();records=[]
 for graph,edges in(('separate',pad(raw)),('shared',pad(shared))):
  for method in(('dense','generic','path_sparse')if graph=='separate'else('dense','generic')):
   p=finalize(build(template,FIXTURE,edges,method,sparse_module=planner,margin=16));free=['x']+p['auxiliaries'];p['certificate_ledger']=ledger(p['source'],free,[v for ab in p['comparisons']for v in ab]);p['polynomial_ledger']=ledger(p['polynomial_source'],free,[p['output']]);need(len(p['comparisons'])==47,'all complete constraints retained');need(len(p['auxiliaries'])==p['m']+67,'complete interface');records.append(dict(graph=graph,flow=method,packet=p))
 equiv=language_equivalence(pad(raw),pad(shared));counts['reachable_language_equivalence_states']+=equiv
 boundary_codes=[(),((),),((1,),),((1,),(1,)),((1,),(1,2),(1,2,3)),((1,2),(1,3)),((1,2),(3,2)),((1,2,1),(2,1),(1,)),FIXTURE]
 language_checks=[]
 for codes in boundary_codes:
  se=separate(codes);sh,cert=share(codes);n=language_equivalence(pad(se),pad(sh));language_checks.append(dict(codes=[list(w)for w in codes],subset_pairs=n,separate_active=len(se),shared_active=len(sh)))
  need(all(0<=a<len(pad(sh))and 0<=b<len(pad(sh))for a,b,l in sh),'state codes fit paid radix')
 counts['complete_finite_language_decisions']=len(language_checks)
 words=[(0,0)]+[tuple(a for i in choice for a in((0,)if i==0 else FIXTURE[i-1]))for length in(1,2,3)for choice in itertools.product(range(4),repeat=length)]
 words=sorted(set(w+(0,)*(max(0,2-len(w)))for w in words))
 formal=[]
 expected={('separate','dense'):(205,287),('separate','generic'):(181,265),('separate','path_sparse'):(179,264),('shared','dense'):(179,253),('shared','generic'):(169,245)}
 for item in records:
  p=item['packet'];edges=p['edges'];rng=random.Random(981)
  need((p['polynomial_ledger']['M'],p['polynomial_ledger']['A'])==expected[(item['graph'],item['flow'])],'complete paid reference ledger')
  need(p['polynomial_ledger']['operations']-p['certificate_ledger']['operations']==140,'all 47 residual subtractions/squares/sum')
  need(p['radix_margin_minimum']==16,'common original paid radix margin')
  dense=next(r['packet']for r in records if r['graph']==item['graph']and r['flow']=='dense')
  proof=formal_controller_identity(p,dense);formal.append(dict(graph=item['graph'],flow=item['flow'],**proof));counts['formal_controller_residuals']+=proof['residual_coefficient_identities'];counts['formal_downstream_cuts']+=proof['downstream_cut_identities'];counts['unchanged_downstream_rows']+=proof['unchanged_instructions']
  for word in words:outer_fixture(p,word);counts['positive_controller_outer_fixtures']+=1
  for case in range(8):
   v={n:rng.randrange(-2,4)for n in p['auxiliaries']+['x']};e=execute(p['polynomial_source'],v);a=execute(dense['polynomial_source'],v)
   need([e[f'residual_{i}']for i in range(47)]==[a[f'residual_{i}']for i in range(47)],'entire dense/general residual identity');need(e[p['output']]==a[dense['output']],'full finalizer value');counts['complete_numeric_flow_identities']+=1
  counts['live_polynomial_gates']+=p['polynomial_ledger']['operations']
 return dict(status='PASS',scope='Five finite complete fixed-controller sources; exact same-graph flow identities and cross-graph ordinary-input language theorem, not a numerical universal alphabet.',source_sha256=sha(Path(__file__).read_bytes()),pins=copy.deepcopy(PINS),counts=dict(counts),fixture=[list(c)for c in FIXTURE],automaton_certificate=certificate,language_checks=language_checks,formal_flow_proofs=formal,outer_fixture_scope='Controller ports and subset only; no complete matrix-target/Pell zeros materialized.',forms=records)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],forms=[dict(graph=f['graph'],flow=f['flow'],m=f['packet']['m'],ledger=f['packet']['polynomial_ledger'])for f in r['forms']])))
if __name__=='__main__':main()
