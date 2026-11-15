from pathlib import Path
import sys,json,time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
sys.path.insert(0,str(HERE/'vendor'))
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c, build as s
I=('leaf','inc',1);c.MACROS[(I,I)]=99;c.MACROS[((I,I),(I,I))]=190
g=c.read_grammar(ROOT/'reference/primary/grammar.json')
baseline_ins=json.loads((ROOT/'reference/primary/instructions.json').read_text())
def tup(x):return tuple(tup(y)for y in x)if isinstance(x,list)else x
def read_table(path):
 out={}
 for l in path.read_text().splitlines():
  if not l.strip()or l.startswith('#'):continue
  q,b,w,d,n=l.split();out[int(q),int(b)]=int(w),d=='R',int(n)
 return out
def reach(rows):
 seen={74};todo=[74]
 for q in todo:
  for b in (0,1):
   n=rows[q,b][2]
   if n!=254 and n not in seen:seen.add(n);todo.append(n)
 return{k:v for k,v in rows.items()if k[0]in seen}
import argparse
p=argparse.ArgumentParser(description='Replay rejected shortened-scanner compositions; no accepted consistency machine.')
p.add_argument('--index',type=int)
a=p.parse_args()
results=[]
for k in [3,6,7,8,9,11,12]:
 if a.index is not None and k!=a.index:continue
 p=HERE/f'loop{k}'
 n={q:tup(v)for q,v in json.loads((p/'nodes.json').read_text()).items()}
 raw=read_table(p/'raw.native.tm')
 # Source-preserving rotations already checked in the previous corpus, now composed with the new loop.
 n.update(node21=('node20','node170'),node171=('node21','node23'),node172=('node7','node171'),node162=('node37','node163'),node164=('node75','node162'))
 c.raw_nodes=lambda:n
 sites,ins,contracts=c.source(g)
 assert json.loads(json.dumps(ins))==baseline_ins
 raw.update({(84,0):(0,True,68),(53,0):(0,True,333),(53,1):(1,True,214),(310,0):(0,True,53),(100,0):(0,True,213),(100,1):(1,True,174),(174,0):(0,True,28),(174,1):(1,True,164),(333,0):(0,True,105),(333,1):(1,True,31),(23,0):(0,False,75)})
 del raw[34,0];del raw[34,1]
 raw=reach(raw)
 ops=c.opportunities_fast(raw,{q:None for q,b in raw});pairs=c.max_matching(ops);optmap={(a,b):opts for a,b,opts in ops}
 folds=[[a,b,[o[0]for o in optmap[a,b]]]for a,b in pairs]
 child,aliases=s.apply_folds(raw,folds)
 try:s.check_folds(raw,child,aliases,folds);local=True
 except Exception as e:local=repr(e)
 failures=[]
 for j,ct in enumerate(contracts):
  if c.run(child,ct)is None:failures.append([j,ct[0],ct[1]])
 r=dict(loop=k,raw=len(raw)//2,states=len(child)//2,folds=folds,local=local,source_graph_equal=True,failing_outcomes=len(failures),failures=failures)
 results.append(r);print(json.dumps({k:v for k,v in r.items()if k not in ['folds','failures']}),flush=True)
 assert child==read_table(p/'rejected.native.tm')
 assert len(child)//2==194 and local is True and len(failures)==47
print(json.dumps({'status':'PASS_REJECTED_COMPOSITIONS_REPLAY','tables':len(results)}))
