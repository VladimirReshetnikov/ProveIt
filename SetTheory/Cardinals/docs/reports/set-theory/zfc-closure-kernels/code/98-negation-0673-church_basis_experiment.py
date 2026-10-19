#!/usr/bin/env python3
"""Measure complete Church-basis / dual-B source controls, never claim a TM endpoint.
New experiment. Attributed frozen emitter/compiler code is loaded read-only.
"""
from pathlib import Path
import sys, importlib, importlib.util, json, itertools, time, hashlib, argparse
HERE=Path(__file__).resolve().parent
VENDOR=HERE/'vendor'
sys.path.insert(0,str(VENDOR/'research'))
import recover_wade_dag as recover
recover.SNAPSHOT=VENDOR/'snapshot'
import theory_backend_experiment as t
t.SNAPSHOT=recover.SNAPSHOT
import full_grammar_experiment as common
common.REPORT=VENDOR/'report'
SP=VENDOR/'specialized_axiom_compiler.py'
spec=importlib.util.spec_from_file_location('specialized',SP)
s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
sys.path.insert(0,str(recover.SNAPSHOT/'ZF/generator'))
backend=importlib.import_module('TMBuilder')
FINE=json.loads((HERE/'macro_to_fine.json').read_text())
I=t.Imp; N=t.Not
a,b,c='a','b','c'
bases={
 'L': [s.SPEC['ax_rows']('a','h','b','c','u')[1]],
 'KSP':[I(a,I(b,a)), I(I(a,I(b,c)),I(I(a,b),I(a,c))), I(I(I(a,b),a),a)],
 'KSDNE':[I(a,I(b,a)), I(I(a,I(b,c)),I(I(a,b),I(a,c))), I(N(N(a)),a)],
 'KSPF':[I(a,I(b,a)), I(I(a,I(b,c)),I(I(a,b),I(a,c))), I(I(N(a),a),a)],
}
def simplify(f):
 if not isinstance(f,tuple):return f
 if f[0]=='imp' and f[2]==1 and isinstance(f[1],tuple) and f[1][0]=='imp' and f[1][2]==1:return simplify(f[1][1])
 return f[0],simplify(f[1]),simplify(f[2])

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--seeds',type=int,default=50);ap.add_argument('--output',type=Path,default=HERE/'church-results');args=ap.parse_args()
 out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
 old=s.SPEC['ax_rows']('a','h','b','c','u')
 C,G,V=s.components('original');fs=[C[2],G[1],*V]
 order=list(itertools.permutations(range(4)))[16]
 bundle=s.L.trees([fs[i] for i in order],t)[1]
 results={};started=time.monotonic();fwcache={};allwords={}
 for mode,base in bases.items():
  for dual in (False,True):
   if mode!='KSDNE' and dual:continue # only explicit DNE supplies EFQ without old B
   for simp in (False,True):
    key=f'{mode}_{"dualB" if dual else "oldB"}_{"dne" if simp else "raw"}'
    best=None;trials=0
    for orderno,baseorder in enumerate(itertools.permutations(base)):
     rest=list(old[2:])
     if dual:rest[1]=I(b,t.All(a,t.Ex(a,b)))
     rows=[old[0]]+list(baseorder)+rest
     newbundle=simplify(bundle) if simp else bundle
     word=[166,121,180,176]+[m for r in rows[1:] for m in s.emit(r,1)]+s.emit(newbundle,1)+t.TAIL
     assert s.symbolic(word,1)[0]==['old_top']+rows+[newbundle]
     fine=''.join(FINE[str(m)] for m in word)
     allwords[f'{key}_{orderno}']=dict(word=fine,macro_word=word,rows=rows,bundle=newbundle)
     tokens=s.coarsen(word)
     for seed,exponent in itertools.product(range(args.seeds),(2,4,8)):
      seq,grammar,_=common.safe_repair(tokens,seed,exponent)
      assert common.expand(seq,grammar)==tokens
      nn,names=s.transform(tokens,seq,grammar);depth=s.lg.dispatch_depth(nn)
      sig=tuple(sorted(s.lg.framework_leaves(nn))),depth
      if sig not in fwcache:
       m=s.H.compile_dag(backend,nn,names);s.H.reextract(m,nn,names)
       fwcache[sig]=len({q for q,bit in m.states})-len(nn)
      cost=len(nn)+fwcache[sig];metric=(cost,len(nn),depth,orderno,seed,exponent);trials+=1
      if best is None or metric<tuple(best['metric']):
       best=dict(metric=metric,nodes=nn,names=names,word=word,fine=fine,rows=rows,bundle=newbundle,grammar=grammar,residual=seq)
    dest=out/key;dest.mkdir(exist_ok=True)
    m=s.H.compile_dag(backend,best['nodes'],best['names']);s.H.reextract(m,best['nodes'],best['names'])
    data,labels,missing=common.normalize(m);(dest/'candidate.tm').write_bytes(data)
    (dest/'candidate.json').write_text(json.dumps(best,indent=2)+'\n')
    results[key]=dict(working_states=best['metric'][0],decision_nodes=best['metric'][1],framework_states=best['metric'][0]-best['metric'][1],fine_terminals=len(best['fine']),macro_calls=len(best['word']),trials=trials,best_metric=best['metric'],sha256=hashlib.sha256(data).hexdigest(),missing_totalized=missing,logical_basis_complete=True,literal_TM_calibration_proved=False)
    (out/'results.json').write_text(json.dumps(dict(results=results,seconds=time.monotonic()-started),indent=2)+'\n')
    (out/'fine_words.json').write_text(json.dumps(allwords,indent=2)+'\n')
    print(key,results[key],flush=True)
if __name__=='__main__':main()
