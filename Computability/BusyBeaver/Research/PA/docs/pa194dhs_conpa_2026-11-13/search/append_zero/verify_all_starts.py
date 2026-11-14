#!/usr/bin/env python3
"""Independent exact obstruction for the append-zero PA194 transplant.

Every working control is tried as a blank-tape initial state. Each run must
halt or reach a control whose zero action is a self-loop directed into an
entirely blank half-line. The latter condition is an induction certificate,
not a long finite nonhalting test. This checker uses sparse bit dictionaries
and does not import the discovery classifier or any source/runtime engine.
"""
import argparse,hashlib,json
from pathlib import Path

EXPECTED='49439961cb03177c0e2e65b9009000d7e005bca9c57193f90650f5dc79bb9c77'

def parse(path):
 rows={}
 for ln in path.read_text().splitlines():
  if not ln.strip() or ln.lstrip().startswith('#'):continue
  v=ln.split();assert len(v)==5
  q,b,w,t=map(int,(v[0],v[1],v[2],v[4]));d=v[3]
  assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b)not in rows
  rows[q,b]=w,d,t
 controls={q for q,b in rows}
 assert len(rows)==2*len(controls)
 assert len({t for w,d,t in rows.values()}-controls)==1
 return rows,controls

def inspect(rows,controls,start):
 state=start;head=0;memory={};trace=[]
 for elapsed in range(78):
  if state not in controls:
   assert state==254
   return {'initial_state':start,'outcome':'halt','steps':elapsed,
           'state':state,'head':head,'ones':sorted(memory),'trace':trace}
  bit=memory.get(head,0)
  write,direction,target=rows[state,bit]
  if bit==0 and target==state:
   boundary=max(memory,default=head-1) if direction=='R' else min(memory,default=head+1)
   blank_ahead=(boundary<head) if direction=='R' else (boundary>head)
   if blank_ahead:
    return {'initial_state':start,'outcome':'blank_half_line','steps':elapsed,
            'state':state,'head':head,'ones':sorted(memory),
            'direction':direction,'write':write,'trace':trace}
  trace.append({'state':state,'head':head,'read':bit,'write':write,'move':direction,'next':target})
  if write:memory[head]=1
  elif head in memory:del memory[head]
  head+=1 if direction=='R' else -1
  state=target
 raise AssertionError(('unclassified within 77 steps',start))

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('table',type=Path)
 ap.add_argument('--output',type=Path);ap.add_argument('--baseline',type=Path);ap.add_argument('--labels',type=Path)
 args=ap.parse_args();digest=hashlib.sha256(args.table.read_bytes()).hexdigest();assert digest==EXPECTED
 rows,states=parse(args.table);assert len(states)==194
 assert {t for w,d,t in rows.values()}-states=={254}
 delta=None
 if args.baseline:
  assert args.labels
  labels=json.loads(args.labels.read_text());base,_=parse(args.baseline)
  native={(labels[q],b):(w,d,labels[t])for(q,b),(w,d,t)in base.items()}
  assert set(native)==set(rows)
  changes=[(q,b,native[q,b],rows[q,b])for q,b in sorted(rows)if native[q,b]!=rows[q,b]]
  assert changes==[(198,0,(1,'L',40),(0,'L',40))],changes
  delta={'baseline_sha256':hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
         'labels_sha256':hashlib.sha256(args.labels.read_bytes()).hexdigest(),'changes':changes}
 results=[inspect(rows,states,q)for q in sorted(states)]
 counts={kind:sum(r['outcome']==kind for r in results)for kind in ('halt','blank_half_line')}
 assert counts=={'halt':4,'blank_half_line':190}
 report={'table_sha256':digest,'working_states':194,'counts':counts,
         'maximum_certificate_prefix':max(r['steps']for r in results),
         'halting_starts':[{k:r[k]for k in ('initial_state','steps','state','head','ones')}for r in results if r['outcome']=='halt'],
         'exact_mutation_check':delta,'all_results':results,
         'proof_rule':'At a zero self-loop, all nonzero cells lie strictly behind the head in its movement direction. Induction preserves an untouched blank half-line ahead and the nonhalting state.'}
 if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k!='all_results'},indent=2))

if __name__=='__main__':main()
