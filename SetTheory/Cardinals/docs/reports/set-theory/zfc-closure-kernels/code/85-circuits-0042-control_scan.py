#!/usr/bin/env python3
"""Control-aware one-step reassociations of the T-only identity collapse."""
import argparse,json,time
from pathlib import Path
from collections import Counter
import specialize as z
import search246 as s
import rotate_search as r
import control_rotations as cr
from plateau_search import reach,minimize
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
if not __debug__:raise RuntimeError('Run without -O.')
z.OUTPUT=args.output.resolve();z.OUTPUT.mkdir(parents=True,exist_ok=True)
from audit_guard_transport import parse_source,cases,check_product
check_product(json.loads(z.CERT.read_text()),cases(parse_source(z.PACKAGE/'reference/context246/sources/Prog254.v')))
began=time.monotonic();candidate,failure=z.collapse('T');assert not failure
N,R,ss,cert,mapping,deleted=candidate
results=[];hist=Counter();best=247
for i,(n,exp,kind) in enumerate(cr.options(N)):
 nn,nr=r.mutate(N,R,n,exp);new=s.sites(nn,nr)
 ordermap=dict(zip(sorted(p for p,_,_ in ss),sorted(p for p,_,_ in new)))
 newmap={old:ordermap[pc] for old,pc in mapping.items()}
 repaired,fail=z.repair(new,newmap,deleted)
 record=dict(index=i,node=n,kind=kind)
 if fail:record.update(status='SOURCE_FAIL',failure=fail);hist['SOURCE_FAIL']+=1
 else:
  new,certificate=repaired;nn,nr=z.intern_sites(new)
  try:
   table,_=s.emit(nn,nr);states=reach(table);cost=minimize(table,states)
   record.update(status='PASS',graph_states=len(states),exact_bisimulation_states=cost,control_edits=len(certificate['control_edits']));hist[str(cost)]+=1
   if cost<best:
    best=cost;z.emit_record(f'controlT-{i}',nn,nr,new,certificate,dict(exact_bisimulation_states=cost,control_rotation_index=i));print('BEST',i,kind,len(states),cost,flush=True)
  except (KeyError,IndexError) as ex:record.update(status='UNSUPPORTED',failure=str(ex));hist['UNSUPPORTED']+=1
 results.append(record)
 if (i+1)%50==0:print('progress',i+1,dict(hist),flush=True)
out=dict(scope='All one-step global left/right binary reassociations of the T-only identity collapse, with existing CB/CC retargeting and invariant-conditioned source-edge checks.',best_exact_bisimulation_states=best,proposals=len(results),histogram=hist,seconds=time.monotonic()-began,results=results)
(z.OUTPUT/'control-scan-summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='results'},indent=2),flush=True)
