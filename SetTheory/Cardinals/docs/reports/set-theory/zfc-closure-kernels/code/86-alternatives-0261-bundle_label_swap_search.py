#!/usr/bin/env python3
"""Exact gated-component a/b reindexing, preserving matrix/hull parameter c."""
from pathlib import Path
import sys,json,itertools,time,importlib,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'machine_encoding'))
import specialized_axiom_compiler as s
from permuted_row_search import remap
if not __debug__:raise RuntimeError('Run without -O.')
out=HERE/'bundle_label_swaps';out.mkdir(exist_ok=True);bd=out/'backend';bd.mkdir(exist_ok=True)
for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):(bd/name).write_bytes(s.recover.git_bytes(None,'ZF/generator/'+name))
sys.path.insert(0,str(bd));backend=importlib.import_module('TMBuilder')
bestrow=json.loads((HERE/'permuted_rows/best.json').read_text())
# Rebuild tuples, since JSON list nesting is otherwise not recognized by emitter.
def tuples(x):return tuple(map(tuples,x)) if isinstance(x,list) else x
rows=tuples(bestrow['rows']);prefix=[166,121,180,176]+[m for r in rows[1:] for m in s.emit(r,1)]
C,G,V=s.components('original');components=[C[2],G[1],*V];order=list(itertools.permutations(range(4)))[16]
framework={};results={};best=None;trials=0;start=time.monotonic()
def eval_(mask,seeds):
 global best,trials
 fs=[remap(f,{'a':'b','b':'a'}) if mask>>i&1 else f for i,f in enumerate(components)]
 bundle=s.L.trees([fs[i] for i in order],s.t)[1];word=prefix+s.emit(bundle,1)+s.t.TAIL
 actual,_=s.symbolic(word,1);assert actual==['old_top']+list(rows)+[bundle]
 tokens=s.coarsen(word);local=None
 for seed,exp in itertools.product(range(seeds),(2,4,8)):
  seq,grammar,_=s.common.safe_repair(tokens,seed,exp);assert s.common.expand(seq,grammar)==tokens
  nn,nm=s.transform(tokens,seq,grammar);depth=s.lg.dispatch_depth(nn);sig=(tuple(sorted(s.lg.framework_leaves(nn))),depth)
  if sig not in framework:
   m=s.H.compile_dag(backend,nn,nm);s.H.reextract(m,nn,nm);framework[sig]=len({q for q,b in m.states})-len(nn)
  metric=(len(nn)+framework[sig],len(nn),depth,len(grammar),len(seq),seed,exp);trials+=1
  record=dict(metric=metric,mask=mask,word=word,tokens=tokens,rows=rows,bundle=bundle,nodes=nn,names=nm,grammar=grammar,residual=seq)
  if local is None or metric<local['metric']:local=record
  if best is None or metric<best['metric']:
   best=record;print(json.dumps(dict(best_states=metric[0],nodes=metric[1],mask=mask,trials=trials,seconds=time.monotonic()-start)),flush=True)
 if mask not in results or local['metric']<results[mask]['metric']:results[mask]=local
for mask in range(16):eval_(mask,200)
for rec in sorted(results.values(),key=lambda r:r['metric'])[:4]:eval_(rec['mask'],1000)
m=s.H.compile_dag(backend,best['nodes'],best['names']);s.H.reextract(m,best['nodes'],best['names']);data,labels,missing=s.common.normalize(m);(out/'candidate.tm').write_bytes(data);(out/'best.json').write_text(json.dumps(best,indent=2)+'\n')
report=dict(working_states=best['metric'][0],decision_nodes=len(best['nodes']),metric=best['metric'],best_mask=best['mask'],component_order=['C','G','Vrel','Veq'],comparison={mask:r['metric'] for mask,r in results.items()},grammar_trials=trials,seconds=time.monotonic()-start,all_edges_reextracted=True,symbolic_AXIOM_emission_checked=True,gated_component_families_preserved=True,transition_rows=len(data.decode().splitlines())-1,sha256=hashlib.sha256(data).hexdigest(),missing_totalized=missing,status='Exact schema-family equivalence; no binary consistency endpoint.')
(out/'results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
