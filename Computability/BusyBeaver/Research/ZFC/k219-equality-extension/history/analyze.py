from pathlib import Path
import collections,functools,importlib.util,json,sys,hashlib,time
p=Path('/tmp/k219-equality-extension');repo=Path('/home/codex/.codex/worktrees/ec20/Proofs');base=repo/'Computability/BusyBeaver/Research/ZFC'
sys.dont_write_bytecode=True;sys.path.insert(0,str(base/'k219-continuation-search/compiler-inputs'));import source_language as s
spec=importlib.util.spec_from_file_location('v',Path('/tmp/zfc-intake186/execution-copy/research/encoding/verify_clean_eq.py'));v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
def tup(t):return tuple(tup(x) if isinstance(x,list) else x for x in t)
atoms=list(map(tup,json.loads((p/'atoms.json').read_text())));nodes=atoms[:];roots=[]
for line in (p/'cost8-complete.nodes').read_text().splitlines():
 a=line.split()
 if a[0]=='H':roots.append((int(a[1]),int(a[2])))
 else:
  i,l,r,c=map(int,a);assert i==len(nodes) and l<i and r<i;nodes.append((nodes[l],nodes[r]))
assert len(nodes)==377821 and len(roots)==263
old=tup(json.loads(Path('/tmp/zfc-intake186/execution-copy/machine/new_equality_macro.json').read_text()));tree=s.tree(json.loads((base/'candidate-k219/sites219.json').read_text()))
@functools.cache
def replace(t,n):
 if t==old:return n,1
 if s.leaf(t):return t,0
 a,ac=replace(t[0],n);b,bc=replace(t[1],n);return (a,b),ac+bc
cases=[(a,b) for a in range(16) for b in range(16)]+[(0,100),(100,0),(100,100),(99,100),(100,99)]
results=[];t0=time.monotonic()
for j,(a,b) in enumerate(roots):
 macro=(nodes[a],nodes[b]);new,count=replace(tree,macro);assert count==4
 rows=s.sites(new);assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
 result={'id':j,'root':[a,b],'metrics':s.metrics(new),'macro':macro,'macro_leaves':len(s.sites(macro)),'right_decrements':sum(op=='CD' and path[-1]=='1' for path,op,arg in rows),'right_increments':sorted(set(arg for path,op,arg in s.sites(macro) if op=='CI' and path[-1]=='1'))}
 try:
  graph=v.compile_cfg(((macro,('CI',0)),('CH',None)));total=0
  for ca,cb in cases:total+=v.run(graph,ca,cb)
  result.update(finite='PASS',cases=len(cases),steps=total)
 except (AssertionError,ValueError,IndexError) as e:result.update(finite='FAIL',failure=str(e),pair=[ca,cb] if 'ca' in locals() else None)
 results.append(result)
 if result['metrics']['dag_nodes']<=206 and result['finite']=='PASS':
  (p/f'candidate-{j:03d}.sites.json').write_bytes(s.compact(rows))
(p/'analysis.json').write_text(json.dumps({'scope':'Finite discovery only; all-natural contract not proved','seconds':time.monotonic()-t0,'results':results},indent=2)+'\n')
print(json.dumps({'seconds':time.monotonic()-t0,'census':dict(collections.Counter((r['metrics']['dag_nodes'],r['finite']) for r in results)) if False else [(list(k),n) for k,n in sorted(collections.Counter((r['metrics']['dag_nodes'],r['finite']) for r in results).items())],'best':[r for r in results if r['metrics']['dag_nodes']<=206]},indent=2))
