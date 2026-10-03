"""Binding across >1 moving/direct source records, without source-universality claims."""
import json,time,gc
from pathlib import Path
from compiler import Certificate,ev
from sparse_parallel import SparseParallelCompiler
R=Path(__file__).resolve().parent;t=time.time();count=0
import argparse
_parser_args=argparse.ArgumentParser(description=__doc__)
_parser_args.add_argument('--output-dir',type=Path,default=R)
OUT=_parser_args.parse_args().output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
b=lambda name,source,target,side,delta,guard={'op':'true'}:dict(name=name,source=source,target=target,side=side,delta=delta,guard=guard)
sources=[dict(schema='reversible-two-counter-v1',controls=['q','r','s','h'],start='q',halt='h',class_cut=0,branches=[b('left','q','r',-1,1),b('right','r','s',1,1),b('done','s','h',1,0)]),dict(schema='reversible-two-counter-v1',controls=['q','h'],start='q',halt='h',class_cut=1,branches=[b('zero','q','h',1,0,{'op':'eq','counter':0,'value':0}),b('nonzero','q','h',1,0,{'op':'gt','counter':0,'value':0})])]
for si,source in enumerate(sources):
 ref=SparseParallelCompiler(source);m=ref.metadata
 # Source-uniform compiler does not enumerate templates. This small test oracle may.
 IDs=sorted(set([0,m.E_count-1,m.E_count,m.factors-1]+[i for i in range(m.factors)if any(k in m.gate_at(i).name for k in('dispatch','endpoint','commit','direct:'))]))
 cases=[]
 for ID in IDs:
  for shape in m.gate_at(ID).shapes:
   x=set(shape)
   if len(x)==2:x.add(1000000)
   cases.append(sorted(x))
 for inverse in(False,True):
  cert=Certificate(source,3,1,inverse)
  for x in cases:
   y=sorted(ref.step(set(x),inverse=inverse,verify=True));values=cert.witness(x,y)
   if [ev(v,values)for v in cert.output]!=y:raise RuntimeError(('multisource mismatch',si,inverse,x))
   count+=1
  del cert;gc.collect()
result=dict(status='PASS',optimized=not __debug__,sources=sources,endpoint_equalities=count,seconds=time.time()-t)
(OUT/('multisource-receipt-optimized.json'if not __debug__ else 'multisource-receipt.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({k:result[k]for k in('status','endpoint_equalities','seconds')}))
