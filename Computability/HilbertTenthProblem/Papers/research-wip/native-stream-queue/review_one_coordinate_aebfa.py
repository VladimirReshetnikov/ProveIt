"""Pinned review and explicit ten-row projection over N[X], never an integer-arity claim."""
from __future__ import annotations
import argparse,copy,hashlib,importlib.util,itertools,json,random,shutil,subprocess,sys,tempfile
from pathlib import Path
PINS={'MANIFEST.sha256': '08b7c7f9a2d846383193e89154f3ffe00915e8817a35169c15f3e97d5fddd996', 'README.md': 'e0fc100f7b16feabad8b220490f9fee8bd7c35bf1109bc5583595232df0b930c', 'code/bounded_linear.py': '8d6067aa27ca0de53353318c3e0663e91396fa838e4727ee1af7163842dbd5df', 'code/compiler.py': '363d147ccc30ffa9e20a9630bf0d7c14168fe686209f212c9ddb8371ca1df726', 'code/export_example.py': '5b8bd8f7f784b8141945f092e8c0fb5fb2e617d188f295596a92361908c16a14', 'code/verify.py': '5941156adcf92de95dca2cd590ba107725591954870269f2332f48b1c6e55e62', 'one_coordinate_certificates.pdf': 'b830c07470b8f606b9537d8048e866112c77c0d93fb9fd2905b2a4688542ba7e', 'one_coordinate_certificates.tex': '73d3a0ef2363ae2497bc8c41f4352f56fd74ca18b20ee09585a3225f505ef029', 'results/build_validation.json': 'e305ebf447e034b9760a370f9a06eb367ae4ebb531fc33684877be6821acd4ef', 'results/example_quartic.json': '06b717e6608a3b23d5f74e9c008dcc0c1a65ff0ac7b883b099b424e2bb3ae6d5', 'results/example_receipt.json': '746e05b38536f0e3a4174b1e44bdcc3ab5ee9b189de722d633c6652a0a7ada97', 'results/example_system.json': '191da1929694d5c9c9a6a51b076f616fc3756d104f940f35c0da5cfa86273e51', 'results/example_witness.json': '52538a31549437e38b4e7e1d8478a097dbf695af9c60911dc0403272f0cff251', 'results/export_hashes.json': 'beb3c4963bc4b7e46a17e442a7f00cf62b9689f49ba8e27eaf0d236335d63f22', 'results/test_binary.json': '21e90c98b423d9c485306e323f4aec2c9aadd8883e3dec3896e83528727039cb', 'results/test_bounded_linear.json': '12ef5ae3b7d36a03f2332209a473189e59afe925dbffa9357b21231a3fea7a5a', 'results/test_independent_tiles.json': '6e1c2733bc4e6324dd7448272d58e7d6fde5cd1a9f74e4c2e23be0fda662d124', 'results/test_interfaces.json': '9ad95e8d72d0b95642e964a122ea72eac14addbf2e56bc7323da2cda5a91e4cf', 'results/test_multistate.json': 'd0ba4ac42872d2fc1f786a5dbea023de73bd55a814e300308693f1729399de17', 'results/test_mutations.json': '1687c611181c992d4e6e3edf9e149db8afde6aeacc30af1d49d7b9b3cacbd8cc', 'results/test_ray_geometry.json': '41b4faa5904875adb9f4d346d110f64a417e5c6e5a187ab9f5c5e03bb7b1f68a', 'results/verification.json': '274645f20ca0836830191fe8b1ee71a7dc70d19286366a0390ddede0fb2bf735'}
PATCH_SHA='a7a1013b214624a30d3166aab758e5c6e48cae426a1b0cd59cf2e3e562b0ab55'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def same(a,b):return type(a) is type(b) and (a.keys()==b.keys() and all(same(a[k],b[k]) for k in a) if isinstance(a,dict) else len(a)==len(b) and all(same(x,y) for x,y in zip(a,b)) if isinstance(a,list) else a==b)
def load(p,name):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m

def project_system(q,old):
 """Prototype restricted to an actual compile_system result constructed by this review."""
 def transform(expr):
  out={}
  for (e,names),coeff in expr.items():
   new=[]
   for name in names:
    if name=='d':new+=['stride0','b']
    elif name=='stride':new.append('stride0');e+=1
    elif name=='stride_prefix':new.append('stride_prefix0');e+=1
    else:new.append(name)
   key=(e,tuple(sorted(new)));out[key]=out.get(key,0)+coeff
  return {k:v for k,v in out.items() if v}
 transformed={k:transform(v) for k,v in old.residuals.items()}
 assert not transformed['calibration']
 rows={k:v for k,v in transformed.items() if k!='calibration'}
 assert all(e>=1 for e,names in rows['positive_stride'])
 rows['positive_stride']={(e-1,n):c for (e,n),c in rows['positive_stride'].items()}
 names=tuple({'stride':'stride0','stride_prefix':'stride_prefix0'}.get(n,n) for n in old.names if n!='d')
 return q.System(old.rule,old.word,names,rows,old.feature_count),transform

def lift(q,w):
 out={k:dict(v) for k,v in w.items() if k not in ('stride0','stride_prefix0')}
 out.update(d=q.mul(w['stride0'],w['b']),stride=q.shift(w['stride0'],1),stride_prefix=q.shift(w['stride_prefix0'],1));return out

def project_zero(q,old,w):
 w=old.checked_witness(w)
 if not old.accepts(w):raise ValueError('projection requires a full parent zero')
 assert not w['stride'].get(0,0) and not w['stride_prefix'].get(0,0)
 out={k:v for k,v in w.items() if k not in ('d','stride','stride_prefix')}
 out.update(stride0={e-1:c for e,c in w['stride'].items()},stride_prefix0={e-1:c for e,c in w['stride_prefix'].items()})
 assert lift(q,out)==w;return out

def run(root,patch,authors=False):
 if not __debug__:raise RuntimeError('review requires assertions enabled')
 root=Path(root);patch=Path(patch)
 if sha(patch)!=PATCH_SHA:raise ValueError("patch hash mismatch")
 for f,h in PINS.items():
  if sha(root/f)!=h:raise ValueError('source/member hash mismatch: '+f)
 q=load(root/'code/compiler.py','coordinate_review_compiler');bl=load(root/'code/bounded_linear.py','coordinate_review_solver')
 out={'archive_sha256':'453ae5f3b3726a288ae30325cbf8e1b6aa15bf6495fb5f23f4e8e8985f713829','source_pins':PINS,'checks':{}};cnt=out['checks']
 def check(k,v):assert v,k;cnt[k]=cnt.get(k,0)+1
 rng=random.Random(813550)
 # Independently simulate a fixed wide window with leading/trailing blank sentinels.
 def truth(rule,word,h):
  offset=h+2;a=[0]*offset+list(word)+[0]*offset;counts=[]
  for t in range(h+1):
   counts.append(sum(x in rule.accepting for x in a))
   a=[0]+[rule.table[(a[i-1]*rule.s+a[i])*rule.s+a[i+1]] for i in range(1,len(a)-1)]+[0]
  return counts[-1]==1 and not any(counts[:-1])
 examples=[(q.example_rule(),(1,0,0,0,2),h) for h in range(7)]
 for s in (3,4):
  for _ in range(12):
   rule=q.Rule(s,[0]+[rng.randrange(s) for _ in range(s**3-1)],{s-1});word=tuple(rng.randrange(s) for _ in range(rng.randrange(1,5)))
   examples.extend((rule,word,h) for h in range(4))
 schemas=set();accepted=0
 for rule,word,h in examples:
  old=q.compile_system(rule,word);new,transform=project_system(q,old);w=q.candidate(old,h);want=truth(rule,word,h)
  check('independent_dense_semantics',old.accepts(w)==want)
  check('projection_interface',len(new.names)==rule.s**3+rule.s+6 and len(new.residuals)==10)
  check('projection_quadratic_shared_stride',all(len(ns)<=2 and (len(ns)<2 or 'stride0' in ns) for row in new.residuals.values() for e,ns in row))
  # All four coefficient-algebra obligations, on complete emitted expressions.
  if (rule.s,word,rule.table) not in schemas:
   schemas.add((rule.s,word,rule.table));old_graph=transform(old.quartic());new_sos=new.quartic();r=new.residuals['positive_stride'];r2=q.emul(r,r)
   check('symbolic_complete_quartic_graph_identity',old_graph==q.eadd(new_sos,q.eshift(r2,2),q.escale(r2,-1)))
  if want:
   child=project_zero(q,old,w);check('natural_zero_bijection',new.accepts(child) and lift(q,child)==w);accepted+=1
   W=len(word)+2*h+2
   check('projected_exact_degree_mass',max((max(p,default=-1) for p in child.values()))==W*(h+1)-1 and sum(sum(p.values()) for p in child.values())==sum(sum(p.values()) for p in w.values())-1)
   for name in new.names:
    bad=copy.deepcopy(child);bad[name][W*(h+1)+3]=1
    check('projected_off_region_false_witness',not new.accepts(bad))
 for i in range(24):
  old=q.compile_system(q.example_rule(),(1,0,2));new,transform=project_system(q,old)
  v={name:{e:c for e in range(3) if (c:=rng.randrange(-2 if i%2 else 0,3))} for name in new.names}
  restored=lift(q,v);nr=new.evaluate(v,validate=False);pr=old.evaluate(restored,validate=False)
  check('arbitrary_signed_full_residual_graph',not pr['calibration'] and all(pr[k]==(q.shift(vv,1) if k=='positive_stride' else vv) for k,vv in nr.items()))
  check('full_quartic_evaluation_identity',q.evaluate(transform(old.quartic()),v)==q.add(*(q.mul(p,p) for p in pr.values())))
 # Compile canonical zero and check exact input boundaries plus immutable ownership.
 old=q.compile_system(q.example_rule(),(1,0,0,0,2));w=q.candidate(old,4)
 for name in ('stride','z_0_0_0','t_3','j'):
  for e,c in ((-1,1),(True,1),(0.5,1),(0,True),(0,0.5),(0,-1)):
   bad=copy.deepcopy(w);bad[name]={e:c}
   try:old.accepts(bad)
   except ValueError:check('exact_polynomial_witness_guard',True)
   else:raise AssertionError('bad coefficient or exponent accepted')
 for name in ('absent','extra'):
  bad=copy.deepcopy(w)
  if name=='absent':bad.pop('b')
  else:bad['bad']={}
  try:old.accepts(bad)
  except ValueError:check('complete_witness_interface_guard',True)
  else:raise AssertionError('bad interface accepted')
 table=list(q.example_rule().table);accept={3};word=[1,0,0,0,2];r=q.Rule(4,table,accept);owned=q.compile_system(r,word);table[:]=[0]*64;accept.clear();word[:]=[0]
 check('rule_and_word_snapshots',r.table==q.example_rule().table and r.accepting==frozenset({3}) and owned.word==(1,0,0,0,2) and owned.accepts(w))
 for mutate in (lambda:owned.residuals.__setitem__('bad',{}),lambda:next(iter(owned.residuals.values())).__setitem__((0,()),1)):
  try:mutate()
  except (TypeError,AttributeError):check('deep_residual_immutability',True)
  else:raise AssertionError('mutable compiler residual')
 # Bounded linear solver: two unknowns, one-step memory, enumerate all finite
 # coefficient vectors through the theorem's cutoff independently of graph search.
 for case in range(32):
  A=[[[rng.randrange(-1,2) for _ in range(2)]] for _ in range(2)];rhs=[[rng.randrange(-1,2)] for _ in range(2)];sol=bl.solve(A,rhs,1);found=False
  for bits in itertools.product(range(2),repeat=12):
   u=[bits[i:i+2] for i in range(0,12,2)];outputs=[sum(A[0][0][j]*u[t][j] for j in range(2))+sum(A[1][0][j]*u[t-1][j] for j in range(2)) if t else sum(A[0][0][j]*u[0][j] for j in range(2)) for t in range(6)]+[sum(A[1][0][j]*u[-1][j] for j in range(2))]
   if outputs==[rhs[0][0],rhs[1][0],0,0,0,0,0]:found=True;break
  check('bounded_two_unknown_exhaustive',found==(sol is not None))
  if sol is not None:
   prod=q.add(*(q.mul({i:A[i][0][j] for i in range(2)},sol[j]) for j in range(2)))
   check('bounded_solver_supplied_witness',prod==q.clean({i:rhs[i][0] for i in range(2)}))
 # Full expanded 74-variable, ten-row example is preserved in receipt.
 old=q.compile_system(q.example_rule(),(1,0,0,0,2));new,trans=project_system(q,old);child=project_zero(q,old,q.candidate(old,4));poly=new.quartic()
 out['projected_example']={'variables':list(new.names),'residuals':{k:q.expression_json(v) for k,v in new.residuals.items()},'witness':{k:q.polynomial_json(v) for k,v in child.items()},'quartic_terms':len(poly),'quartic_unknown_degree':max(map(lambda key:len(key[1]),poly)),'maximum_coordinate_coefficient_degree':max(e for e,n in poly),'maximum_witness_degree':max(max(v,default=-1) for v in child.values()),'witness_mass':sum(sum(v.values()) for v in child.values()),'accepted_cases':accepted}
 if authors:
  with tempfile.TemporaryDirectory(prefix='coordinate-review-') as tmp:
   dest=Path(tmp)/'original';shutil.copytree(root,dest)
   for script in ('code/verify.py','code/export_example.py'):
    subprocess.run([sys.executable,script],cwd=dest,check=True,capture_output=True,text=True,timeout=300);check('original_author_command',True)
   saved={p.name:json.loads(p.read_text()) for p in sorted((root/'results').glob('*.json'))};actual={p.name:json.loads(p.read_text()) for p in sorted((dest/'results').glob('*.json'))}
   check('all_saved_json_exactly_reproduced',same(saved,actual));out['author_json_sha256']={name:hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest() for name,value in actual.items()}
   for f in ('example_system.json','example_witness.json','example_quartic.json'):
    check('author_mathematical_export_bytes',(root/'results'/f).read_bytes()==(dest/'results'/f).read_bytes())
 # Direct descriptor exactness is separate from high-level compile_system correctness.
 badsystem=q.System(q.Rule(2,[0]*8,{1}),(0,),('x',),{'test':{(0,()):float(2**60),(0,('x',)):-1.0}},1)
 check('original_descriptor_float_false_zero',badsystem.accepts({'x':{0:2**60+1}}))
 check('original_accepting_bool_alias',q.Rule(2,[0]*8,[1,True]).accepting==frozenset({1}))
 out['patch_sha256']=PATCH_SHA
 with tempfile.TemporaryDirectory(prefix='coordinate-fixed-review-') as tmp:
  fixed=Path(tmp)/'fixed';shutil.copytree(root,fixed)
  subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch.resolve())],cwd=fixed,check=True,capture_output=True,timeout=240)
  f=load(fixed/'code/compiler.py','coordinate_fixed_review');out['patched_source_sha256']=sha(fixed/'code/compiler.py');rule=f.Rule(2,[0]*8,{1})
  descriptors=[{(0,()):0.0},{(0,()):False},{(-1,()):1},{(True,()):1},{(0.5,()):1},{(0,('bad',)):1},{(0,('x','a')):1},{(0,(True,)):1},{('bad',()):1}]
  calls=[lambda terms=terms:f.System(rule,(0,),('a','x'),{'row':terms},1) for terms in descriptors]
  calls += [lambda:f.System(rule,(0,),('x','x'),{},1),lambda:f.System(rule,(True,),('x',),{},1),lambda:f.System(rule,(0,),('x',),{},True),lambda:f.System(rule,(0,),('x',),{True:{}},1),lambda:f.Rule(2,[0]*8,[1,True]),lambda:f.Rule(2,[0]*8,[1,1.0])]
  for call in calls:
   try:call()
   except (ValueError,TypeError):check('patched_system_descriptor_rejected',True)
   else:raise AssertionError('invalid System descriptor accepted')
  word=[0];names=['x'];terms={(0,('x',)):1};rows={'row':terms};owned=f.System(rule,word,names,rows,1)
  word[0]=1;names[0]='bad';terms[(0,('x',))]=0;rows.clear()
  check('patched_all_descriptor_containers_snapshot',owned.word==(0,) and owned.names==('x',) and not owned.accepts({'x':{0:1}}) and owned.accepts({'x':{}}))
  canonical=f.compile_system(f.example_rule(),(1,0,0,0,2));projected,_=project_system(f,canonical)
  check('patched_projection_remains_valid',projected.accepts(project_zero(f,canonical,f.candidate(canonical,4))))
  if authors:
   for script in ('code/verify.py','code/export_example.py'):
    subprocess.run([sys.executable,script],cwd=fixed,check=True,capture_output=True,text=True,timeout=300);check('patched_author_command',True)
   saved={p.name:json.loads(p.read_text()) for p in sorted((root/'results').glob('*.json'))};repaired={p.name:json.loads(p.read_text()) for p in sorted((fixed/'results').glob('*.json'))}
   check('patched_full_author_json_unchanged',same(saved,repaired))
   for filename in ('example_system.json','example_witness.json','example_quartic.json'):
    check('patched_mathematical_export_bytes',(root/'results'/filename).read_bytes()==(fixed/'results'/filename).read_bytes())
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=Path);p.add_argument('--patch',required=True,type=Path);p.add_argument('--authors',action='store_true');p.add_argument('--output',required=True,type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.root,a.patch,a.authors)
 if a.expect and not same(r,json.loads(a.expect.read_text())):raise AssertionError('receipt mismatch')
 a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps(r['checks'],sort_keys=True))
if __name__=='__main__':main()
