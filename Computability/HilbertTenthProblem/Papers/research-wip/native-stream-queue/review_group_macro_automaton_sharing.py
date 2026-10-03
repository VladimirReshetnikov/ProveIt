#!/usr/bin/env python3
"""Independent bounded audit; JSON sources only, no author or historical imports."""
import argparse,ast,copy,hashlib,itertools,json,random,subprocess,sys,tempfile
from collections import Counter,deque
from fractions import Fraction
from pathlib import Path
PINS = {'group_shared_typing_matrix_compiler.py': '3ef20018fb7f4e31d1a0ebc9cac2914fe506dd6d16fd71bfe6ced6c1374eb04a', 'group_shared_typing_matrix_compiler.json': 'ec52b3502de67c578176dfab0ae347158feedc0a9d9fd65c761c0ef5d183118f', 'group_shared_typing_matrix_compiler.md': 'c8830b16ad8f9ce973e21eb68199949a331c30b76a04d82664c20ac44a400ae3', 'group_complete_matrix_compiler.py': '9877dbab8c5a44d27615bec6d1ba0a2eebe79f19b288609adf0b95f00ac6fef7', 'group_complete_matrix_compiler.md': 'b474c7f7ab92f6067abd417f34cade3403cbc53364b6b33bdf61b1755d04ecb1', 'group_regular_macro_controller.py': '159a51c9171309ef68d13e1662e4b8e3b6e3d752ab1199ed021084e4564a8a8d', 'group_regular_macro_controller.md': '91d8932360bdc998811c5727c983602d37edc9943fab0114f00532a6bba49ec5', 'group_sparse_macro_flow.py': '74604c1a9d1071a823e0df3388d2c89eb639cf3e088a39fa7fff3eae5113238a', 'group_sparse_macro_flow.md': '4e4356902a52de1464c91ac5aea2a654900492b74ee252d9ea22a34e5dd6febc', 'group_four_register_canonical_history47.md': '78c80b9cdd178ce70d40238cd773d67720bac11b194d7581725b0c225f1b6c52', 'group_four_register_history.md': 'c77c586185d7acf918b4123e301c04db4d868c302fc24a6385538f93c7e6625b', 'group_linked_binary_geometry47.md': '4be87c7429b89e171417ce54065b575947cea21e9bb1986112cee0ad0a259f96'}
AUTHOR = {'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585'}
CODES=((1,1,2),(2,3,2),(4,5))

def require(c,msg):
 if not c: raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def load_pinned(root,name,pin):
 data=(root/name).read_bytes();require(digest(data)==pin,'source pin '+name);return data

def path_table(codes):
 ans=[(0,0,0)];n=1
 for code in codes:
  cur=0
  for i,l in enumerate(code):
   nxt=0 if i+1==len(code) else n
   if nxt:n+=1
   ans.append((cur,nxt,l));cur=nxt
 return ans

def padding(edges):
 size=2
 while size<len(edges):size*=2
 return edges+[(0,0,0)]*(size-len(edges))

def trie(codes):
 prefixes={()}
 for w in codes:prefixes.update(w[:i] for i in range(1,len(w)))
 ids={p:i for i,p in enumerate(sorted(prefixes))}
 edges={(ids[()],ids[()],0)}
 for w in codes:
  for i,l in enumerate(w):edges.add((ids[w[:i]],ids[w[:i+1]] if i+1<len(w) else 0,l))
 return sorted(edges),ids

def equivalence(a,b):
 alphabet=sorted({e[2] for e in a+b});todo=deque([(frozenset([0]),frozenset([0]))]);seen=set(todo)
 while todo:
  x,y=todo.popleft();require((0 in x)==(0 in y),'regular-language disagreement')
  for label in alphabet:
   nx=frozenset(v for u,v,l in a if u in x and l==label)
   ny=frozenset(v for u,v,l in b if u in y and l==label)
   pair=nx,ny
   if pair not in seen:seen.add(pair);todo.append(pair)
 return len(seen)

class Ring:
 """Exact linear forms over interned nonlinear products; no tested-value cuts."""
 def __init__(self):self.atoms={};self.serial=0
 def atom(self,k):
  if k not in self.atoms:self.serial+=1;self.atoms[k]=self.serial
  return ((self.atoms[k],1),)
 def var(self,k):return self.atom(('variable',k))
 def num(self,k):return ((0,k),) if k else ()
 def scale(self,x,k):return tuple((v,c*k) for v,c in x if c*k)
 def add(self,x,y,k=1):
  d=dict(x)
  for v,c in y:d[v]=d.get(v,0)+k*c
  return tuple((v,c) for v,c in sorted(d.items()) if c)
 def mul(self,x,y):
  if not x or not y:return ()
  if len(x)==1 and x[0][0]==0:return self.scale(y,x[0][1])
  if len(y)==1 and y[0][0]==0:return self.scale(x,y[0][1])
  return self.atom(('product',*sorted((x,y))))
 def rows(self,rows,env):
  env=dict(env)
  for n,op,a,b in rows:
   a=env[a] if type(a)is str else self.num(a);b=env[b] if type(b)is str else self.num(b)
   env[n]=self.mul(a,b) if op=='*' else self.add(a,b,-1 if op=='-' else 1)
  return env

def run(rows,values):
 env=dict(values)
 for n,op,a,b in rows:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b
  env[n]=a*b if op=='*' else a-b if op=='-' else a+b
 return env

def ledger(rows,free,roots):
 degrees={v:1 for v in free};defs={};counts=Counter()
 for row in rows:
  require(type(row)is list and len(row)==4,'literal four-field row');n,op,a,b=row
  require(type(n)is str and n not in degrees and op in ('+','-','*'),'fresh operation')
  require(all(type(v)is int or type(v)is str and v in degrees for v in (a,b)),'closed operands')
  d=[degrees[v] if type(v)is str else 0 for v in (a,b)];degrees[n]=sum(d) if op=='*' else max(d)
  defs[n]=(a,b);counts['M' if op=='*' else 'A']+=1
 todo=list(roots);live=set();leaves=set()
 while todo:
  v=todo.pop()
  if type(v)is int:continue
  if v in defs:
   if v not in live:live.add(v);todo.extend(defs[v])
  else:leaves.add(v)
 require(live==set(defs) and leaves==set(free),'complete literal liveness')
 return dict(operations=len(rows),M=counts['M'],A=counts['A'],degree_upper=max(degrees[v] if type(v)is str else 0 for v in roots)),degrees

def finalizer(source,comparisons):
 rows=copy.deepcopy(source)
 for i,(a,b) in enumerate(comparisons):rows.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 out='square_0'
 for i in range(1,len(comparisons)):
  rows.append([f'sum_{i}','+',out,f'square_{i}']);out=f'sum_{i}'
 return rows,out

def expected_controller(ring,env,edges,margin):
 m=len(edges);get=lambda v:env[v] if type(v)is str else ring.num(v)
 hats=[get(f'controller__edge_hat{i}') for i in range(m)]
 total=lambda xs:__import__('functools').reduce(ring.add,xs,())
 sm=total(hats);src=total([ring.scale(h,a) for h,(a,b,l) in zip(hats,edges)])
 dst=total([ring.scale(h,b) for h,(a,b,l) in zip(hats,edges)])
 src=ring.add(src,ring.num(sum(e[0] for e in edges)),-1);dst=ring.add(dst,ring.num(sum(e[1] for e in edges)),-1)
 one=ring.num(1);B=get('B');P=get('P');J=get('J')
 pair=[ring.add(ring.add(ring.mul(ring.add(B,one,-1),J),one),P,-1),ring.add(ring.add(ring.num(margin),get('controller__radix_beta')),B,-1),ring.add(sm,ring.add(J,ring.num(m)),-1),ring.add(src,ring.mul(B,dst),-1)]
 for l in range(1,9):
  ids=[i for i,e in enumerate(edges) if e[2]==l]
  port=ring.add(total([hats[i] for i in ids]),ring.num(1-len(ids)))
  pair.append(ring.add(port,get('Shat'+str(l-1)),-1))
 return pair

def check_controller_polynomials(rows,edges,margin):
 # Multivariate coefficient expansion of the actual small controller block.
 def add(a,b,k=1):
  c=dict(a)
  for m,v in b.items():c[m]=c.get(m,0)+k*v
  return {m:v for m,v in c.items() if v}
 def mul(a,b):
  c={}
  for m,v in a.items():
   for n,w in b.items():
    key=tuple(sorted(m+n));c[key]=c.get(key,0)+v*w
  return {m:v for m,v in c.items() if v}
 num=lambda n:{():n} if n else {}
 variable=lambda n:{(n,):1}
 m=len(edges);names=['B','P','J','controller__radix_beta']+[f'controller__edge_hat{i}' for i in range(m)]
 env={n:variable(n) for n in names}
 for n,op,a,b in rows:
  if not n.startswith('controller__'):continue
  a=env[a] if type(a)is str else num(a);b=env[b] if type(b)is str else num(b)
  env[n]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 power=num(1);repun={};packed={}
 for i in range(m):
  repun=add(repun,power);packed=add(packed,mul(power,env[f'controller__edge_hat{i}']));power=mul(power,env['P'])
 require(env['controller__edge_word']==add(packed,repun,-1),'exact polynomial edge packing without free hat decoding')
 require(env['controller__origin_mask']==mul(env['J'],repun),'exact polynomial controller mask')
 for i in range(1,m.bit_length()-1):require(env[f'controller__lane_power{i}']=={('P',)*(2**i):1},'every paid lane power')
 require(env['controller__radix_margin']==add(num(margin),env['controller__radix_beta']),'actual retained fixed margin')
 return sum(len(v) for v in env.values())

def polynomial_degree(rows,free,output):
 # Exact specialization all supplied coordinates to t over Z. Combined with
 # the global degree upper bound this establishes exact degree, not sampling.
 def add(a,b,s=1):
  out=list(a)+[0]*max(0,len(b)-len(a))
  for i,v in enumerate(b):out[i]+=s*v
  while out and out[-1]==0:out.pop()
  return out
 def mul(a,b):
  if not a or not b:return []
  out=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   if x:
    for j,y in enumerate(b):
     if y:out[i+j]+=x*y
  while out and out[-1]==0:out.pop()
  return out
 env={v:[0,1] for v in free}
 for n,op,a,b in rows:
  a=env[a] if type(a)is str else [a] if a else [];b=env[b] if type(b)is str else [b] if b else []
  env[n]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 return len(env[output])-1,env[output][-1]

def verify(root,artifacts):
 blobs={n:load_pinned(root,n,h) for n,h in PINS.items()}
 author={n:load_pinned(artifacts,n,h) for n,h in AUTHOR.items()};receipt=json.loads(author['group_macro_automaton_sharing.json'])
 require(receipt['status']=='PASS','frozen successful author receipt')
 require(receipt['source_sha256']==AUTHOR['group_macro_automaton_sharing.py'] and exact(receipt['pins'],PINS),'author provenance matches independently authenticated bytes')
 template=json.loads(blobs['group_shared_typing_matrix_compiler.json'])['source']['packets'][0]
 require(template['codes']==[] and template['m']==2,'saved complete template')
 # Authenticate the named historical fixture by source AST only, never execute it.
 module=ast.parse(blobs['group_regular_macro_controller.py']);fn=next(v for v in module.body if isinstance(v,ast.FunctionDef) and v.name=='verify')
 examples=ast.literal_eval(next(v.value for v in fn.body if isinstance(v,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='examples' for t in v.targets)))
 require(CODES in examples and receipt['fixture']==[list(w) for w in CODES],'actual named fixture')
 cert=receipt['automaton_certificate'];te,prefixes=trie(CODES);classes={tuple(v['prefix']):v['state'] for v in cert['prefix_class']}
 require(set(classes)==set(prefixes) and classes[()]==0 and all(c!=0 for p,c in classes.items() if p),'distinguished hub quotient')
 quotient={(classes[p],classes[q],l) for a,b,l in te for p in prefixes if prefixes[p]==a for q in prefixes if prefixes[q]==b}
 for p in prefixes:
  sig={(l,classes[q]) for a,b,l in te if a==prefixes[p] for q in prefixes if prefixes[q]==b}
  for q in prefixes:
   if classes[p]==classes[q]:require(sig=={(l,classes[z]) for a,b,l in te if a==prefixes[q] for z in prefixes if prefixes[z]==b},'class bisimulation')
 require(cert['proper_prefixes']==[list(p) for p in sorted(prefixes)],'complete prefix inventory')
 for state in set(classes.values())-{0}:
  expected_signature=sorted([[l,b] for a,b,l in quotient if a==state])
  require(cert['class_continuations'][str(state)]==expected_signature,'quotient continuation metadata')
 require(cert['root_continuations']==sorted([[l,b] for a,b,l in quotient if a==0 and l!=0]),'hub continuation metadata')
 shared=sorted(quotient,key=lambda e:(e!=(0,0,0),e));separate=path_table(CODES)
 require((len(separate),len(shared),len({a for e in shared for a in e[:2]}))==(9,8,5),'actual edge/state census')
 reachable=equivalence(separate,shared);require(equivalence(te,shared)>0,'trie quotient exact language')
 # Independent cost and source boundaries; imported native blocks remain literal.
 selstart=next(i for i,r in enumerate(template['source']) if r[0]=='selection__P2');selend=next(i for i,r in enumerate(template['source']) if r[0]=='controller__source_weighted0')
 geostart=next(i for i,r in enumerate(template['source']) if r[0].startswith('geometry__'))
 selection=template['source'][selstart:selend];geometry=template['source'][geostart:]
 require((len(selection),len(geometry))==(126,47),'actual native block sizes')
 expected={('separate','dense'):(492,205,287,16,304),('separate','generic'):(446,181,265,16,304),('separate','path_sparse'):(443,179,264,16,304),('shared','dense'):(432,179,253,8,208),('shared','generic'):(414,169,245,8,208)}
 require({(v['graph'],v['flow']) for v in receipt['forms']}==set(expected) and len(receipt['forms'])==5,'exact five-form coverage')
 counts=Counter();summaries=[]
 # The supported interface is the source-pinned CLI. These only enter its
 # authentication failure path; the author arithmetic verifier is not run.
 with tempfile.TemporaryDirectory(prefix='macro-review-pins-') as tmp:
  tmp=Path(tmp)
  for name in PINS:(tmp/name).symlink_to((root/name).resolve())
  for name in PINS:
   p=tmp/name;p.unlink();p.write_bytes(blobs[name]+b'\n')
   fail=subprocess.run([sys.executable,str((artifacts/'group_macro_automaton_sharing.py').resolve()),'--root',str(tmp)],capture_output=True,text=True,timeout=15)
   require(fail.returncode!=0 and 'pin '+name in fail.stderr,'CLI rejects altered dependency '+name)
   counts['cli_bad_pin_rejections']+=1;p.unlink();p.symlink_to((root/name).resolve())
 for form in receipt['forms']:
  p=form['packet'];key=(form['graph'],form['flow']);cost,M,A,m,degree=expected[key];edges=padding(separate if key[0]=='separate' else shared)
  require(all(0<=a<m and 0<=b<m and 0<=l<=8 for a,b,l in edges),'actual fixed-state digit ranges')
  require(p['edges']==[list(e) for e in edges] and p['m']==m and (p['alpha'],p['beta'],p['radix_margin_minimum'])==(24,12,16),'actual complete table/input data')
  require(p['codes']==[list(w) for w in CODES],'current macro-code metadata')
  labels=Counter(e[2] for e in edges);require(p['projection_additions']==sum(v for k,v in labels.items() if k and v>=2),'fully paid selector-port metadata')
  plan=p['flow_plan'];byname={row[0]:row for row in p['source']}
  require(len(plan['checksum_rows'])==m-1 and all(byname[row[0]]==row for row in plan['checksum_rows']+plan['flow_rows']),'actual source plan metadata')
  require(p['comparisons'][24][0]==plan['checksum'] and p['comparisons'][25]==plan['pair'],'actual checksum/flow interface metadata')
  rows=p['source'];require(rows[:47]==template['source'][:47],'unchanged actual ordinary-input history47')
  gotselect=[r for r in rows if r[0].startswith('selection__') or r[0].startswith('joint_')]
  wanted=copy.deepcopy(selection)
  for r in wanted:
   if r[0]=='joint_Pm':r[2:]=[f'controller__lane_power{m.bit_length()-2}']*2
  require(gotselect==wanted and rows[-47:]==geometry,'unchanged native selection126/geometry47 with sole paid power rewire')
  require(all(r[0].startswith('controller__') for r in rows[47:] if r not in gotselect and r not in geometry),'only controller rows replaced')
  require(len(p['comparisons'])==47 and p['comparisons'][:22]==template['comparisons'][:22] and p['comparisons'][34:]==template['comparisons'][34:],'all fixed comparisons retained')
  aux=[n for n in template['auxiliaries'] if not n.startswith('controller__edge_hat')];idx=aux.index('controller__radix_beta');aux[idx:idx]=[f'controller__edge_hat{i}' for i in range(m)]
  require(p['auxiliaries']==aux and p['parameters']==['x'] and len(aux)==m+67,'complete positive supplied interface')
  counts['local_polynomial_terms']+=check_controller_polynomials(rows,edges,16)
  free=['x']+aux;certled,dg=ledger(rows,free,[v for pair in p['comparisons'] for v in pair]);polyled,_=ledger(p['polynomial_source'],free,[p['output']])
  require((polyled['operations'],polyled['M'],polyled['A'],polyled['degree_upper'])==(cost,M,A,degree),'independent full paid ledger')
  require(exact(certled,p['certificate_ledger']) and exact(polyled,p['polynomial_ledger']),'saved ledger exactness')
  poly,out=finalizer(rows,p['comparisons']);require(poly==p['polynomial_source'] and out==p['output'],'all47 paid square residuals/finalizer')
  ring=Ring();base={v:ring.var(v) for v in free};env=ring.rows(poly,base)
  residuals=[ring.add(env[a] if type(a)is str else ring.num(a),env[b] if type(b)is str else ring.num(b),-1) for a,b in p['comparisons']]
  require(residuals[22:34]==expected_controller(ring,env,edges,16),'every exact controller residual, general branching allowed')
  dense=next(v['packet'] for v in receipt['forms'] if v['graph']==key[0] and v['flow']=='dense');denv=ring.rows(dense['polynomial_source'],base)
  require(all(env[f'residual_{i}']==denv[f'residual_{i}'] for i in range(47)) and env[out]==denv[dense['output']],'47 whole-source residuals and SOS equal same-table dense source over any ring')
  exactdeg,coef=polynomial_degree(poly,free,out);require((exactdeg,coef)==(degree,16**12),'complete exact degree attainment')
  residualdegrees=[max(dg[a] if type(a)is str else 0,dg[b] if type(b)is str else 0) for a,b in p['comparisons']]
  require(residualdegrees[9]==degree//2 and max(residualdegrees[:9]+residualdegrees[10:])<degree//2,'unique maximal first norm, fixed native index not substituted')
  rng=random.Random(6307)
  for case in range(12):
   values={n:Fraction(rng.randrange(-3,4),rng.randrange(1,4)) if case<4 else rng.randrange(-3,4) for n in free}
   ev=run(poly,values);dv=run(dense['polynomial_source'],values)
   require(ev[out]==dv[dense['output']],'complete rational/integer value');counts['complete_evaluations']+=1;counts['rational_evaluations']+=case<4
  counts['complete_sources']+=1;counts['residual_identities']+=47;counts['live_gates']+=cost;counts['exact_degree_proofs']+=1
  summaries.append(dict(graph=key[0],flow=key[1],certificate=certled,polynomial=polyled,witnesses=len(aux),equations=47,exact_degree=exactdeg,diagonal_top_coefficient=coef))
 return dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),author_pins=AUTHOR,parent_pins=PINS,counts=dict(counts),language=dict(active_edges_before=9,active_edges_after=8,shared_states=5,exact_subset_product_states=reachable,unbounded_language_equivalence=True,witness_bijection_claimed=False),forms=summaries,scope='Independent actual saved complete sources and language proof; no author/historical execution; not a numerical universal subgroup alphabet.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:require(exact(r,json.loads(a.expect.read_bytes())),'exact typed reviewer receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],forms=[(p['graph'],p['flow'],p['polynomial']['operations']) for p in r['forms']])))
if __name__=='__main__':main()
