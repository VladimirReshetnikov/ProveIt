#!/usr/bin/env python3
"""Independent complete-source review of the pinned native Grill weak input cone."""
import argparse,copy,hashlib,itertools,json,random,sys,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
SOURCE_SHA256='8f636a7954fce4335c2977baf849da0107b29d146aaa008fbb9732acedcf60b9'
PARENT_SHA256='760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069'
PADDING_SHA256='299acc95d66b60fb7fe2b3e3a85ffd3ec7c77f8c53ce2f11d1b59d9f7d59ba48'
PROGRAMS=((0,),(1,),(0,1,1),(2,0,1))

def need(b,m):
 if not b:raise ValueError(m)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def load(path,pin,name):
 data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==pin,'Source pin '+str(path))
 m=types.ModuleType(name);m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m
def run(p,v):
 e=dict(v)
 for n,o,a,b in p['polynomial_source']:
  need(n not in e,'SSA output');a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def at(e,v):return e[v] if type(v)is str else v
# Tiny exact sparse integer polynomials, used only for width/global-row ancestors.
def poly(v):return {():v} if type(v)is int and v else {} if type(v)is int else {(v,):1}
def add(a,b,sgn=1):
 z=dict(a)
 for k,v in b.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   q=tuple(sorted(k+l));z[q]=z.get(q,0)+v*w
 return {k:v for k,v in z.items() if v}
def symbolic(p,sub=None):
 rows={n:(o,a,b) for n,o,a,b in p['polynomial_source']};env={n:poly(n) for n in p['parameters']+p['auxiliaries']};env.update(sub or {})
 def get(v):
  if type(v)is int:return poly(v)
  if v not in env:
   o,a,b=rows[v];a=get(a);b=get(b);env[v]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return env[v]
 return get

def prove_source(strong,weak,c):
 cut=strong['interfaces']['P0'];removed='three_x__0';old=strong['polynomial_source'];new=weak['polynomial_source']
 need([(n,o,a,b) for n,o,a,b in old if n==removed]==[(removed,'*','x',3)],'Literal input multiplication')
 need([(n,o,a,b) for n,o,a,b in old if n==cut]==[(cut,'+','Z0',removed)],'Literal strong width')
 for token in (removed,'Z0'):
  need([n for n,o,a,b in old for v in (a,b) if v==token]==[cut],'Only proved-width consumer '+token)
 expected=[(n,o,'Z0','x') if n==cut else (n,o,a,b) for n,o,a,b in old if n!=removed]
 need(exact(expected,new),'Every complete paid source row is the exact width rewrite')
 need(exact(strong['comparisons'],weak['comparisons']),'All residual pairs retained')
 a=symbolic(strong,{'Z0':add(poly('Z0'),mul(poly(-2),poly('x')))});b=symbolic(weak)
 need(a(cut)==b(cut)==add(poly('x'),poly('Z0')),'Symbolic width identity under actual coordinate map')
 # Since there are no other consumers and all other instructions are literal,
 # induction through the complete topological source proves each later value.
 known=set(weak['parameters']+weak['auxiliaries']);degrees={n:1 for n in known};live={weak['output']};ops=Counter()
 for n,o,a,b in new:
  need(type(n)is str and n not in known and o in ('+','-','*'),'Typed SSA source')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Closed source')
  da=degrees[a] if type(a)is str else 0;db=degrees[b] if type(b)is str else 0;degrees[n]=da+db if o=='*' else max(da,db)
  known.add(n);ops['M' if o=='*' else 'A']+=1
 for n,o,a,b in reversed(new):
  need(n in live,'No dead paid gate');live.update(v for v in (a,b) if type(v)is str)
 need(live-set(n for n,o,a,b in new)==set(weak['parameters']+weak['auxiliaries']),'Exact free-coordinate set')
 for k in ('parameters','auxiliaries','comparisons','interfaces','maps','baselines','groups_U','groups_V','K','scale_exponent','region_exponents','unit_factors','projection_aliases'):
  need(exact(strong.get(k),weak.get(k)),'Unchanged actual native/phase/domain interface '+k)
 cert=Counter('M' if o=='*' else 'A' for n,o,a,b in weak['source'])
 need(exact(new[:len(weak['source'])],weak['source']),'Paid certificate prefix')
 need(exact(strong['polynomial_source'][len(strong['source']):],new[len(weak['source']):]),'Literal complete finalizer preserved')
 need(weak['operations']==sum(cert.values()) and weak['multiplications']==cert['M'] and weak['additions_subtractions']==cert['A'],'Certificate counts')
 led=weak['polynomial_ledger'];need(led['operations']==len(new) and all(led[k]==ops[k] for k in ('M','A')),'Complete ledger')
 need(strong['polynomial_ledger']['M']==ops['M']+1 and strong['polynomial_ledger']['A']==ops['A'],'Exactly one multiplication saved')
 need(degrees[weak['output']]==led['degree_upper']==strong['polynomial_ledger']['degree_upper'] and weak['exact_degree']is None,'Formal upper degree, no exact claim')
 need(led['witnesses']==len(weak['auxiliaries']) and led['comparisons']==len(weak['comparisons']),'Paid witnesses and rows')
 need(weak['full_polynomial_identity']is False and weak['input_cone']['positive_fiber_bijection']is False,'Current relation metadata')
 need(weak['strong_parent_metadata']['full_polynomial_identity']is True,'Historical phase identity scoped separately')
 # Separate same-coordinate statement, proven from the actual global residual.
 a=symbolic(strong);b=symbolic(weak);u,v=strong['comparisons'][0];delta=add(add(a(u),a(v),-1),add(b(u),b(v),-1),-1)
 desired=mul(poly(-2*weak['K']),mul(poly('x'),mul(poly('Vfinal'),b(weak['interfaces']['J']))))
 need(delta==desired,'Exact same-coordinate global residual correction')
 c['complete_literal_source_proofs']+=1;c['residual_pairs_under_substitution']+=len(weak['comparisons']);c['native_factor_identities']+=len(weak.get('unit_factors',[]));c['retained_complete_gates']+=len(new)-1
 c['symbolic_same_coordinate_global_corrections']+=1;c['complete_ledgers_and_upper_degrees']+=1
 return dict(program=list(weak['program']),unit_product=weak['unit_product'],ledger=led,complete_source_sha256=hashlib.sha256(json.dumps(new,separators=(',',':')).encode()).hexdigest(),same_coordinate_delta_terms=len(delta))

def fixture(p,heads,x,width):
 m=len(p['program']);tiles=[2*(i%m)+heads[i] for i in range(len(heads)-1,-1,-1)];U=V=1;hu=[];hv=[]
 for k in tiles:
  hu.append(U);hv.append(V);a,c,b,d=p['maps'][k];U,V=a*U+c,b*V+d
 need(U==width*V+x and 0<x<width,'Weak sentinel relation')
 phase=tiles[0]//2+1;D=1<<(U+phase).bit_length();B=p['K']*D;P=B**len(heads)
 pack=lambda row:sum(v*B**i for i,v in enumerate(row))
 e={n:1 for n in p['parameters']+p['auxiliaries']};e.update(x=x,Z0=width-x,Vfinal=V,phase_initial=phase,height_slack=D-U-phase,H_U=pack(hu),H_V=pack(hv))
 for i in range(p['tiles']):e[f'Shat{i}']=pack([int(k==i) for k in tiles])+1
 hats=[]
 for tag,groups,history in [('U',p['groups_U'],hu),('V',p['groups_V'],hv)]:
  for i,g in enumerate(groups):
   n=f'Z{tag}hat{i}';e[n]=pack([v if k in g['tiles'] else 0 for k,v in zip(tiles,history)])+1;hats.append(e[n])
 e['global_bound']=P-e['H_U']-e['H_V']-sum(hats);need(min(e.values())>0,'Positive supplied fixture')
 env=run(p,e);face={k:at(env,v) for k,v in p['interfaces'].items()}
 need(all(at(env,a)==at(env,b) for a,b in p['comparisons'][:4]),'Complete four outer source rows')
 need(face['P0']==width and face['P']==P and face['D']==D,'Actual width/height/packing')
 need(face['H']&face['M']==face['Z'] and max(face['H'],face['M'],face['Z'])<face['scale'],'Exact semantic prescribed AND ports')
 need(env[p['output']]!=0,'Fixture deliberately has placeholder native witnesses, not a full zero')
 return e,face

def semantics(p,c):
 m=len(p['program']);examples=[]
 for t in range(1,7):
  for heads in itertools.product((0,1),repeat=t):
   U=V=1
   for i in range(t-1,-1,-1):
    d=heads[i];n=p['program'][i%m];U=2*U+d
    if d:V=2*4**n*V+2*(4**n-1)//3
   c['chronological_head_words']+=1
   for ell in range(1,t+1):
    width=2**ell;x=U-width*V
    if not 0<x<width:continue
    queue=''.join(str((x>>i)&1) for i in range(ell));word=queue;halt=None
    for i,d in enumerate(heads):
     if not queue:halt=i;break
     need(int(queue[0])==d,'Closure implies correct actual head before halt');queue=queue[1:]+('0'+'10'*p['program'][i%m] if d else '')
    if halt is None:need(not queue,'Word closure must halt');halt=t
    e,face=fixture(p,heads,x,width);c['positive_outer_AND_fixtures']+=1;c['posthalt_outer_fixtures']+=halt<t;c['weak_but_not_strong_input_widths']+=width<=3*x
    if len(examples)<2:examples.append(dict(program=list(p['program']),unit_product=p['unit_product'],heads=list(heads),word=word,x=x,width=width,first_halt=halt,full_native_zero_materialized=False))
 return examples

def verify(source,root):
 m=load(source,SOURCE_SHA256,'_review_weak_cone');parent_path=source.parent/m.PARENT_NAME
 if not parent_path.is_file():parent_path=root/m.PARENT_NAME
 parent=load(parent_path,PARENT_SHA256,'_review_strong_cone');need(m.PADDING_REFERENCE['sha256']==PADDING_SHA256,'Frozen proved padding reference')
 c=Counter();forms=[];rng=random.Random(208442);examples=[]
 def rejects(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):c['malformed_rejections']+=1;return
  raise ValueError('Malformed public call accepted')
 for program in PROGRAMS:
  for unit in (False,True):
   p=m.build(program,unit_product=unit,root=root);q=parent.build(program,unit_product=unit,root=root)
   need(exact(m.canonical_parent(p,root=root),q),'Actual independently loaded canonical parent')
   need(exact(m.rewrite(q,root=root),p),'Public guarded rewrite')
   forms.append(prove_source(q,p,c))
   names=p['parameters']+p['auxiliaries']
   for case in range(12):
    signed=case>=6;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in names};w=dict(v);w['Z0']-=2*w['x']
    a=run(q,w);b=run(p,v);need(a[q['output']]==b[p['output']],'Independent complete signed substitution')
    need(m.evaluate(p,v,signed=signed,root=root)==b[p['output']],'Public full evaluator')
    need(all(at(a,x)-at(a,y)==at(b,x)-at(b,y) for x,y in p['comparisons']),'Every numeric residual under substitution')
    need(exact(m.integer_pullback(p,v,signed=signed,root=root),w),'Public coordinate map')
    need(m.identity(p,v,signed=signed,root=root)['output']==b[p['output']],'Public output identity')
    c['complete_integer_substitutions']+=1;c['signed_substitutions']+=signed;c['numeric_residual_identities']+=len(p['comparisons'])
    if not signed:
     forward=dict(v);forward['Z0']+=2*forward['x'];need(exact(m.strong_to_weak_assignment(p,v,root=root),forward),'Positive forward map')
     need(run(q,v)[q['output']]==run(p,forward)[p['output']],'Positive one-way polynomial map')
     D=at(b,p['interfaces']['D']);U=at(b,p['interfaces']['Ufinal']);W=at(b,p['interfaces']['P0'])
     need(D>=5 and D>U>W>v['x'] and U>v['Vfinal'] and D>v['phase_initial'],'Weak-cone unconditional pretyping')
     c['positive_forward_maps_and_height_checks']+=1
   v={n:Fraction(rng.randrange(-3,4),rng.randrange(1,4)) for n in names};w=dict(v);w['Z0']-=2*w['x'];need(run(q,w)[q['output']]==run(p,v)[p['output']],'Independent rational identity');c['rational_substitutions']+=1
   examples+=semantics(p,c)
   vals={n:1 for n in names}
   for key in p:
    bad=copy.deepcopy(p);bad[key]=None if p[key] is not None else 0;rejects(lambda bad=bad:m.checked(bad,root=root))
   for name in names[::5]:
    for value in (True,1.0,Fraction(1),0,-1,None):
     bad=dict(vals);bad[name]=value;rejects(lambda bad=bad:m.evaluate(p,bad,root=root))
   for bad in ({},dict(vals,extra=1)):
    rejects(lambda bad=bad:m.integer_pullback(p,bad,root=root));rejects(lambda bad=bad:m.strong_to_weak_assignment(p,bad,root=root))
   bad=copy.deepcopy(q);bad['polynomial_source'][-1]=(q['output'],'-',0,0);rejects(lambda:m.rewrite(bad,root=root))
   for getter in (lambda:m.build(program,unit_product=unit,root=root),lambda:m.canonical_parent(p,root=root),lambda:m.polynomial_source(p,root=root),lambda:m.rewrite(q,root=root)):
    a=getter();expected=copy.deepcopy(a)
    if type(a)is dict:a['polynomial_source'][-1]=('poison','+',0,0)
    else:a.clear()
    need(exact(getter(),expected),'Independent defensive-copy check');c['defensive_copy_checks']+=1
 for bad in ((),[],(True,),(1.0,),(-1,),None):rejects(lambda bad=bad:m.build(bad,root=root))
 for bad in (0,1,None,1.0):rejects(lambda bad=bad:m.build(unit_product=bad,root=root))
 p=m.build(root=root);vals={n:1 for n in p['parameters']+p['auxiliaries']}
 for bad in (0,1,None):
  rejects(lambda bad=bad:m.evaluate(p,vals,signed=bad,root=root));rejects(lambda bad=bad:m.integer_pullback(p,vals,signed=bad,root=root))
 class StringSubclass(str):pass
 bad=dict(vals);bad[StringSubclass('x')]=bad.pop('x');rejects(lambda:m.evaluate(p,bad,root=root))
 bad=copy.deepcopy(p);bad[StringSubclass('program')]=bad.pop('program');rejects(lambda:m.checked(bad,root=root))
 # Source-only loaders must neither trust nor clobber warm untrusted modules.
 sentinel=types.ModuleType(m.PARENT_NAME[:-3]);old=sys.modules.get(sentinel.__name__);present=sentinel.__name__ in sys.modules
 sys.modules[sentinel.__name__]=sentinel
 try:
  cold=load(source,SOURCE_SHA256,'_independent_cold_weak');need(exact(cold.build((0,),root=root),m.build((0,),root=root)),'Cold source loader ignores warm fake sibling');need(sys.modules[sentinel.__name__]is sentinel,'Caller fake module restored exactly');c['cold_fake_module_checks']+=1
 finally:
  if present:sys.modules[sentinel.__name__]=old
  else:sys.modules.pop(sentinel.__name__,None)
 with tempfile.TemporaryDirectory(prefix='independent-weak-pins-') as tmp:
  tmp=Path(tmp);child=tmp/source.name;child.write_bytes(source.read_bytes());target=tmp/m.PARENT_NAME;data=parent_path.read_bytes();target.write_bytes(data)
  isolated=load(child,SOURCE_SHA256,'_independent_warm_pin');before=isolated.build((0,),root=root)
  target.write_bytes(data+b'\n# rejected private mutation\n');rejects(lambda:isolated.build((0,),root=root));target.write_bytes(data)
  need(exact(isolated.build((0,),root=root),before),'Warm pinned cache recovers unchanged source');c['warm_pin_checks']+=1
 # Explicit weak-cone fixture with a negative strong pullback.
 fixture_records=[]
 for unit in (False,True):
  p=m.build((0,),unit_product=unit,root=root);e,f=fixture(p,(1,0),1,2)
  need(e['H_U']==129 and e['H_V']==65 and e['global_bound']==3837 and f['D']==8,'Independent concrete tiny fixture')
  need(m.integer_pullback(p,e,root=root)['Z0']==-1,'Positive inverse cannot be claimed')
  q=parent.build((0,),unit_product=unit,root=root);old=run(q,e);a,b=q['comparisons'][0]
  need(at(old,a)-at(old,b)==-2080,'Concrete same-tuple global residual separation')
  fixture_records.append(dict(program=[0],unit_product=unit,x=1,width=2,Z0=1,formal_strong_slack=-1,D=8,B=64,P=4096,H_U=129,H_V=65,global_bound=3837,strong_same_tuple_global_residual=-2080,full_native_witnesses_materialized=False))
 return json.loads(json.dumps(dict(status='PASS_INDEPENDENT_NATIVE_GRILL_WEAK_CONE',reviewed_source_sha256=SOURCE_SHA256,parent_sha256=PARENT_SHA256,padding_sha256=PADDING_SHA256,counts=dict(c),forms=forms,semantic_examples=examples,strict_weak_fixtures=fixture_records,
 scope='Independent literal full-source substitution and paid ledgers, domain proof, bounded actual word/outer/AND fixtures and strict public API checks. No giant positive native zero materialized; no universal raw-input recognizer or exact-degree claim.')))

if __name__=='__main__':
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--source',type=Path,default=Path(__file__).with_name('grill_tag_native_weak_cone.py'));a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);args=a.parse_args();r=verify(args.source.resolve(),args.root.resolve())
 if args.expect:need(exact(r,json.loads(args.expect.read_text())),'Exact typed saved receipt')
 if args.output:args.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'ledgers':[x['ledger'] for x in r['forms']]},indent=2))
