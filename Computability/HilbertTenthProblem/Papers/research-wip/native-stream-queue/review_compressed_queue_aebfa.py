"""Portable independent queue review; --root points to untouched extracted package."""
from __future__ import annotations
import argparse,hashlib,importlib.util,itertools,json,random,shutil,subprocess,sys,tempfile
from pathlib import Path
PINS={
'code/queue_certificates.py':'d5fbf10fdaa26818f6ca0c925cf2c6d10e59a633b74fd465cb370a6ed035fbe6',
'code/verify.py':'8e848c8417a3c947bd5145014ceab359f9aea0fe10c9646d13d8bc10d0169fa8',
'code/check_certificate.py':'0d30d7f5e685f08be03c8282664f804f2cee743ff43f80a55c5b3fc2cd70a362',
'article.tex':'26dd9baa1a9df5ece3474f322728767ef5576bb5d5b79653694eb13312287f41'}
PATCH_SHA='ed4aa5503033bb2c89dbe16eccdef62ad16101014c7c5c080d6c6f8d77a33501'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p,name):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
def same(a,b):return type(a) is type(b) and (a.keys()==b.keys() and all(same(a[k],b[k]) for k in a) if isinstance(a,dict) else len(a)==len(b) and all(same(x,y) for x,y in zip(a,b)) if isinstance(a,list) else a==b)
def projection(q,nodes,initial,final):
 old=q.compile_certificate(nodes,initial,final); newnames=[];newvals=[]; expr=[];retained=[];cursor=0
 def var(name,v):
  p=q.Poly.variable(len(newnames));newnames.append(name);newvals.append(v);return p
 for i,node in enumerate(nodes):
  summary=old.summaries[i]
  if isinstance(node,q.Leaf):
   expr.extend(q.Poly.coerce(x) for x in summary.six());cursor+=6
  else:
   four=[var(f'n{i}_{s}',v) for s,v in zip(('PU','CU','PV','CV'),summary.six())]
   sx,sy=old.summaries[node.left],old.summaries[node.right]
   alpha=var(f'n{i}_alpha',max(sx.s-sy.r,0));beta=var(f'n{i}_beta',max(sy.r-sx.s,0))
   def row(k):return offsets[k]
   x,y=row(node.left),row(node.right)
   r=expr[x+4]+beta;s=expr[y+5]+alpha;cancel=expr[x+5]-alpha
   expr.extend(four+[r,s,cancel,alpha,beta]);retained.extend([cursor+j for j in (0,1,2,3,5,6)]);cursor+=9
  if i==0: offsets=[]
  offsets.append(len(expr)-(6 if isinstance(node,q.Leaf) else 9))
 expr.append(var('root_slack',old.witness[-1]));retained.extend(range(cursor,cursor+3))
 def subst(p):
  ans=q.Poly()
  for mon,c in p.terms.items():
   t=q.Poly.coerce(c)
   for j in mon:t=t*expr[j]
   ans=ans+t
  return ans
 allrows=[subst(p) for p in old.residuals]
 assert all(not p.terms for j,p in enumerate(allrows) if j not in retained)
 new=q.Certificate(newnames,[allrows[j] for j in retained],newvals,old.summaries)
 return old,new,expr

def run(root,patch,authors=False):
 if not __debug__:raise RuntimeError('review requires assertions enabled')
 root=Path(root);patch=Path(patch)
 for f,h in PINS.items():
  if sha(root/f)!=h:raise ValueError('source hash mismatch: '+f)
 if sha(patch)!=PATCH_SHA:raise ValueError('patch hash mismatch')
 q=load(root/'code/queue_certificates.py','queue_original_review')
 out={'archive_sha256':'cd3cfe40497cca4a3b4781a25b37405f5452e0dae26b70163245d80b53ad0a20','source_pins':PINS,'patch_sha256':PATCH_SHA,'checks':{}}
 counts=out['checks']
 def check(k,v):
  assert v,k;counts[k]=counts.get(k,0)+1
 bad=q.Certificate(['x'],[q.Poly({():float(2**60),(0,):-1.0})],[2**60+1],[])
 check('original_float_false_zero',bad.accepts() and 2**60-bad.witness[0]==-1)
 a=q.Action(['0'],'0');old=q.compile_certificate([q.Leaf(a)],'0','0');a.read[0]='1'
 check('original_mutable_action',old.accepts() and not q.compile_certificate([q.Leaf(a)],'0','0').accepts())
 with tempfile.TemporaryDirectory(prefix='queue-exact-review-') as temp:
  fixed=Path(temp)/'fixed';shutil.copytree(root,fixed)
  subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch.resolve())],cwd=fixed,check=True,capture_output=True,timeout=240)
  p=load(fixed/'code/queue_certificates.py','queue_fixed_review')
  out['patched_source_sha256']=sha(fixed/'code/queue_certificates.py')
  badcalls=[lambda:p.Action(['0'],'0'),lambda:p.Action('0',['0']),lambda:p.Action('0','0',True),lambda:p.Action('0','0',0,0.0),lambda:p.Leaf({}),lambda:p.Concat(True,0),lambda:p.Concat(0,-1),lambda:p.Concat(0.0,0),lambda:p.encode(['0']),lambda:p.encode('0',['0','1']),lambda:p.Poly({():0.0}),lambda:p.Poly({():False}),lambda:p.Poly({(True,):1}),lambda:p.Poly({(-1,):1}),lambda:p.Poly({(1,0):1}),lambda:p.Poly({('0',):1}),lambda:p.Poly([]),lambda:p.Poly.variable(0.0)]
  for f in badcalls:
   try:f()
   except (TypeError,ValueError):check('patched_invalid_boundary_rejected',True)
   else:raise AssertionError('malformed input accepted')
  terms={(0,):2}; pp=p.Poly(terms);terms[(0,)]=3;check('constructor_snapshots_dictionary',pp.evaluate([7])==14)
  rng=random.Random(88517);words=['','0','1','00','01','10','11']
  for case in range(160):
   nodes=[q.Leaf(q.Action(rng.choice(words),rng.choice(words))) for _ in range(2)]
   nodes += [q.Concat(rng.randrange(len(nodes)),rng.randrange(len(nodes)))]
   for _ in range(rng.randrange(3)):
    nodes.append(q.Concat(rng.randrange(len(nodes)),rng.randrange(len(nodes))))
   ini=rng.choice(words);trace=q.expand(nodes);actual=q.run(trace,ini);fin=actual if actual is not None and case%2 else rng.choice(words)
   old,new,expr=projection(q,nodes,ini,fin);c=sum(isinstance(n,q.Concat) for n in nodes)
   check('projection_exact_count',len(new.names)==6*c+1 and len(new.residuals)==6*c+3)
   check('projection_degree',new.polynomial().degree<=4)
   check('canonical_execution',old.accepts()==new.accepts()==(actual==fin))
   fixednodes=[p.Leaf(p.Action(n.action.read,n.action.write)) if isinstance(n,q.Leaf) else p.Concat(n.left,n.right) for n in nodes]
   fixedcert=p.compile_certificate(fixednodes,ini,fin)
   check('valid_compiler_output_unchanged',old.names==fixedcert.names and old.witness==fixedcert.witness and [r.export() for r in old.residuals]==[r.export() for r in fixedcert.residuals])
   for signed in (False,True):
    v=[rng.randrange(-2 if signed else 0,4) for _ in new.names];restored=[e.evaluate(v) for e in expr]
    check('complete_graph_polynomial_identity',old.polynomial().evaluate(restored)==new.polynomial().evaluate(v))
   if new.accepts():
    restored=[e.evaluate(new.witness) for e in expr]
    check('zero_restoration_natural_unique',restored==old.witness and min(restored)>=0)
    for i in range(len(new.witness)):
     mutated=new.witness.copy();mutated[i]+=1
     check('projected_false_witness_rejected',not new.accepts(mutated))
  # Complete bounded solutions of the reduced min gadget, not only canonical witnesses.
  for x,y in itertools.product(range(8),repeat=2):
   sols=[(a,b) for a,b in itertools.product(range(8),repeat=2) if y-x+a-b==0 and a*b==0]
   check('reduced_min_complete_fiber',sols==[(max(x-y,0),max(y-x,0))] and all(x-a==min(x,y)>=0 for a,b in sols))
  # Independent macro checker with empty/multiple reads and writes.
  for reads,writes in itertools.product(words,repeat=2):
   if not reads:continue
   for ini in words:
    trace=[q.Action(reads,writes)];n=q.maximum_repetitions(trace,ini);current=ini
    for k in range(20):
     nxt=current[len(reads):]+writes if current.startswith(reads) else None
     if nxt is None:break
     current=nxt
    check('bounded_loop_direct_semantics',(n is None and nxt is not None) or (n is not None and n==k and nxt is None) or (n is not None and n>=20 and nxt is not None))
  if authors:
   orig=Path(temp)/'original';shutil.copytree(root,orig)
   records=[]
   for tree in (orig,fixed):
    proc=subprocess.run([sys.executable,'code/verify.py'],cwd=tree,check=True,capture_output=True,text=True,timeout=300)
    proc2=subprocess.run([sys.executable,'code/check_certificate.py','data/example_quartic.json','data/infinite_growth_quartic.json'],cwd=tree,check=True,capture_output=True,text=True,timeout=240)
    receipt=json.loads((tree/'data/verification.json').read_text());receipt.pop('python',None)
    records.append(receipt)
    check('independent_export_checker_exit_zero',proc2.returncode==0)
   check('full_author_receipt_unchanged',same(*records))
   saved=json.loads((root/'data/verification.json').read_text());saved.pop('python',None)
   check('saved_author_receipt_reproduced',same(saved,records[0]))
   for f in ('example_quartic.json','infinite_growth_quartic.json'):
    check('author_export_bytes_unchanged',(orig/'data'/f).read_bytes()==(fixed/'data'/f).read_bytes()==(root/'data'/f).read_bytes())
   out['author_receipt']=records[0]
 return out

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True,type=Path);p.add_argument('--patch',required=True,type=Path);p.add_argument('--authors',action='store_true');p.add_argument('--output',required=True,type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.root,a.patch,a.authors)
 if a.expect and not same(r,json.loads(a.expect.read_text())):raise AssertionError('receipt differs')
 a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps(r['checks'],sort_keys=True))
if __name__=='__main__':main()
