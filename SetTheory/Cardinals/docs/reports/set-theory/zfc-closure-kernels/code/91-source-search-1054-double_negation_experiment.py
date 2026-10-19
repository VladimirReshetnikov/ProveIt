#!/usr/bin/env python3
"""Classical double-negation normalization of the fixed CP/GIC bundle.

The logical rows, GEN, relative falsity, arithmetic tags and gates are kept.
Only fixed emitted formulas change by Boolean double-negation identities.
"""
import basis_experiment as b
from pathlib import Path
import itertools,json,time,hashlib
s,t,common,backend=b.s,b.t,b.common,b.backend
HERE=Path(__file__).resolve().parent

def is_not(f):return isinstance(f,tuple) and f[0]=='imp' and f[2]==1
def dne_nodes(f,path=()):
 out=[]
 if isinstance(f,tuple):
  if is_not(f) and is_not(f[1]):out.append(path)
  out+=dne_nodes(f[1],path+(1,))+dne_nodes(f[2],path+(2,))
 return out
def simplify(f,selected=None,path=()):
 if not isinstance(f,tuple):return f
 if is_not(f) and is_not(f[1]) and (selected is None or path in selected):
  return simplify(f[1][1],selected,path+(1,1))
 return (f[0],simplify(f[1],selected,path+(1,)),simplify(f[2],selected,path+(2,)))
def count_nodes(f):return 1+count_nodes(f[1])+count_nodes(f[2]) if isinstance(f,tuple) else 1

def main():
 out=HERE/'double_negation_results';out.mkdir(exist_ok=True)
 rows=s.SPEC['ax_rows']('a','h','b','c','u')
 C,G,V=s.components('original');fs=[C[2],G[1],*V];order=list(itertools.permutations(range(4)))[16]
 bundle=s.L.trees([fs[i] for i in order],t)[1]
 redexes=dne_nodes(bundle);print('redexes',redexes,flush=True)
 fwcache={};allresults=[];globalbest=None;started=time.monotonic();trials=0
 # Keep names and gates fixed; every subset has an explicit local identity.
 for mask in range(1<<len(redexes)):
  newbundle=simplify(bundle,{p for i,p in enumerate(redexes) if mask>>i&1})
  word=[166,121,180,176]+[m for r in rows[1:] for m in s.emit(r,1)]+s.emit(newbundle,1)+t.TAIL
  assert s.symbolic(word,1)[0]==['old_top']+rows+[newbundle]
  tokens=s.coarsen(word);best=None
  for seed,exponent in itertools.product(range(100),(2,4,8)):
   seq,grammar,_=common.safe_repair(tokens,seed,exponent)
   assert common.expand(seq,grammar)==tokens
   nn,names=s.transform(tokens,seq,grammar);depth=s.lg.dispatch_depth(nn)
   sig=tuple(sorted(s.lg.framework_leaves(nn))),depth
   if sig not in fwcache:
    m=s.H.compile_dag(backend,nn,names);s.H.reextract(m,nn,names)
    fwcache[sig]=len({q for q,bit in m.states})-len(nn)
   cost=len(nn)+fwcache[sig];metric=(cost,len(nn),depth,seed,exponent);trials+=1
   if best is None or metric<tuple(best['metric']):best=dict(metric=metric,mask=mask,nodes=nn,names=names,word=word,rows=rows,bundle=newbundle,grammar=grammar,residual=seq)
  result=dict(mask=mask,working_states=best['metric'][0],decision_states=best['metric'][1],depth=best['metric'][2],word_macros=len(word),formula_tree_nodes=count_nodes(newbundle))
  allresults.append(result)
  if globalbest is None or tuple(best['metric'])<tuple(globalbest['metric']):
   globalbest=best;print('BEST',json.dumps(result),flush=True)
   (out/'best.json').write_text(json.dumps(best,indent=2)+'\n')
  (out/'results.json').write_text(json.dumps(dict(redexes=redexes,results=allresults,trials=trials,seconds=time.monotonic()-started),indent=2)+'\n')
 m=s.H.compile_dag(backend,globalbest['nodes'],globalbest['names']);s.H.reextract(m,globalbest['nodes'],globalbest['names'])
 data,labels,missing=common.normalize(m);(out/'candidate.tm').write_bytes(data)
 print('FINAL',json.dumps(dict(metric=globalbest['metric'],mask=globalbest['mask'],trials=trials,sha256=hashlib.sha256(data).hexdigest())),flush=True)

if __name__=='__main__':main()
