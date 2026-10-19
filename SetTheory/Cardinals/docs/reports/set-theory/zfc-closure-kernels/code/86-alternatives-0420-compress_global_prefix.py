#!/usr/bin/env python3
from pathlib import Path
import sys,json,random,time,argparse
H=Path(__file__).resolve().parent;R=H.parent/'context_folds/recovered/67/research'
sys.path[:0]=[str(R/'agent_audit/layout_search'),str(R/'agent_logic')]
from verify_reassociation import Decoder,read_json
import grammar_layout as g
ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=3000);ap.add_argument('--input',type=Path,default=H/'permuted_prefix_helpers.json');ap.add_argument('--name',default='permuted_global');a=ap.parse_args()
g.original,g.original_root,_=read_json(a.input)
g.seqs,g.controls,g.root=g.dt.seq_regions(g.dt.unfold(g.original,g.original_root));g.alphabet=sorted({e for seq in g.seqs.values()for e in seq});g.encode={e:i for i,e in enumerate(g.alphabet)};g.words=[tuple(g.encode[e]for e in g.seqs[i])for i in range(len(g.seqs))]
base=Decoder(g.original,g.original_root);normal=base.normal(('N',base.root));graph=base.graph();rng=random.Random(20261018);start=time.monotonic();best=(999,999,999);feasiblebest=(999,999,999);hist=[]
for trial in range(a.runs):
 noise,top=[(0,1),(1,1),(.05,3),(.15,4),(.3,6)][trial%5];rules,roots=g.compress(rng,noise,top);n,r=g.emit(rules,roots);p,z,dep=g.rot.zero_metrics(n,r);metric=(len(n),z,dep)
 if metric<best or z<=7 and dep<=40 and metric<feasiblebest:
  g.verify(rules,roots,n,r);d=Decoder(n,r);assert d.normal(('N',r))==normal and d.graph()==graph
  record=dict(trial=trial,root=r,nodes=n,metrics=metric,noise=noise,top=top,exact_normal_and_guarded_graph_equal=True);hist.append([trial,*metric]);print(hist[-1],flush=True)
  if metric<best:best=metric;(H/f'{a.name}_best.json').write_text(json.dumps(record,indent=2)+'\n')
  if z<=7 and dep<=40 and metric<feasiblebest:feasiblebest=metric;(H/f'{a.name}_feasible.json').write_text(json.dumps(record,indent=2)+'\n')
 if trial%100==0:print('progress',trial,'best',best,'feasible',feasiblebest,flush=True)
 (H/f'{a.name}_result.json').write_text(json.dumps(dict(status='DONE'if trial==a.runs-1 else'RUNNING',trials=trial+1,best=best,feasiblebest=feasiblebest,hist=hist,seconds=time.monotonic()-start),indent=2)+'\n')
