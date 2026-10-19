#!/usr/bin/env python3
"""Complete source costs for three-parameter propositional basis controls.

No binary consistency endpoint is claimed.  Attributed compiler dependencies
are read unchanged from the pinned ProveIt checkout and incoming archives.
K/S/Peirce is proved complete in alternative_basis_controls.md.  K/B/Peirce
and K/S-only are exploratory controls, without a supplied calibration proof.
"""
from pathlib import Path
import sys, importlib.util, importlib, json, itertools, time, hashlib

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[1]/'sources/ProveIt'
sys.path.insert(0,str(REPO/'Computability/BusyBeaver/Research/ZFC'))
import recover_wade_dag as recover
recover.SNAPSHOT=HERE/'snapshot'
import theory_backend_experiment as theory
theory.SNAPSHOT=recover.SNAPSHOT
import full_grammar_experiment as common
SP=HERE/'vendor/sub246-audit-and-alternatives-20261018/sub246-audit-and-alternatives/research_sub246/machine_encoding/specialized_axiom_compiler.py'
spec=importlib.util.spec_from_file_location('specialized',SP)
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
sys.path.insert(0,str(recover.SNAPSHOT/'ZF/generator'))
backend=importlib.import_module('TMBuilder')
t=theory
I=t.Imp
a,b,c='a','b','c'
bases={
 'lukasiewicz': [s.SPEC['ax_rows']('a','h','b','c','u')[1]],
 'K_S_Peirce':[I(a,I(b,a)), I(I(a,I(b,c)),I(I(a,b),I(a,c))), I(I(I(a,b),a),a)],
 'K_B_Peirce':[I(a,I(b,a)), I(I(a,b),I(I(b,c),I(a,c))), I(I(I(a,b),a),a)],
 'K_S_only_UNPROVED':[I(a,I(b,a)), I(I(a,I(b,c)),I(I(a,b),I(a,c)))],
}

def main():
 out=HERE/'basis_results';out.mkdir(exist_ok=True)
 old=s.SPEC['ax_rows']('a','h','b','c','u')
 C,G,V=s.components('original');fs=[C[2],G[1],*V]
 order=list(itertools.permutations(range(4)))[16]
 bundle=s.L.trees([fs[i] for i in order],t)[1]
 results={};started=time.monotonic()
 for mode,base in bases.items():
  best=None;trials=0;fwcache={}
  # Each added basis row is retained as an independent stack theorem.
  for baseorder in itertools.permutations(base):
   rows=[old[0]]+list(baseorder)+old[2:]
   word=[166,121,180,176]+[m for r in rows[1:] for m in s.emit(r,1)]+s.emit(bundle,1)+t.TAIL
   assert s.symbolic(word,1)[0]==['old_top']+rows+[bundle]
   tokens=s.coarsen(word)
   for seed,exponent in itertools.product(range(100),(2,4,8)):
    seq,grammar,_=common.safe_repair(tokens,seed,exponent)
    assert common.expand(seq,grammar)==tokens
    nn,names=s.transform(tokens,seq,grammar);depth=s.lg.dispatch_depth(nn)
    sig=tuple(sorted(s.lg.framework_leaves(nn))),depth
    if sig not in fwcache:
     m=s.H.compile_dag(backend,nn,names);s.H.reextract(m,nn,names)
     fwcache[sig]=len({q for q,bit in m.states})-len(nn)
    cost=len(nn)+fwcache[sig];metric=(cost,len(nn),depth,seed,exponent)
    trials+=1
    if best is None or metric<tuple(best['metric']):
     best=dict(metric=metric,nodes=nn,names=names,word=word,rows=rows,grammar=grammar,residual=seq)
  dest=out/mode;dest.mkdir(exist_ok=True)
  machine=s.H.compile_dag(backend,best['nodes'],best['names'])
  s.H.reextract(machine,best['nodes'],best['names'])
  data,labels,missing=common.normalize(machine)
  (dest/'candidate.tm').write_bytes(data)
  (dest/'candidate.json').write_text(json.dumps(best,indent=2)+'\n')
  status=('Classically complete axiom-family replacement; binary and initializer theorem not supplied'
          if mode in ('lukasiewicz','K_S_Peirce') else
          'Exploratory emitted basis; no completeness proof supplied; not a calibrated consistency machine')
  result=dict(working_states=best['metric'][0],decision_states=best['metric'][1],dispatch_depth=best['metric'][2],macro_word_length=len(best['word']),extra_u_reads=best['word'].count(158),logical_rows=len(best['rows'])-1,grammar_trials=trials,sha256=hashlib.sha256(data).hexdigest(),all_source_edges_reextracted=True,status=status)
  results[mode]=result
  print(mode,json.dumps(result),flush=True)
 (out/'results.json').write_text(json.dumps(dict(results=results,seconds=time.monotonic()-started),indent=2)+'\n')

if __name__=='__main__':main()
