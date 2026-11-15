#!/usr/bin/env python3
"""Greatest unconditional action-preserving control congruence for each 194 graph.
This rules out a one-step literal-state quotient only, not contextual folds,
multi-step simulations, or a different TM implementation.
"""
from pathlib import Path
import json, argparse, collections
from verify_novelty import parse

def refine(path):
 rows,states,halt=parse(path);part={q:0 for q in states};rounds=0
 while True:
  keys={q:tuple((rows[q,b][0],rows[q,b][1],part.get(rows[q,b][2],-1)) for b in (0,1)) for q in sorted(states)}
  names={};nxt={}
  for q,k in keys.items():
   if k not in names:names[k]=len(names)
   nxt[q]=names[k]
  rounds+=1
  if all((part[x]==part[y])==(nxt[x]==nxt[y]) for x in states for y in states):break
  part=nxt
 groups=collections.defaultdict(list)
 for q,k in nxt.items():groups[k].append(q)
 return {'working_states':len(states),'quotient_states':len(groups),'refinement_rounds':rounds,'nontrivial_classes':[v for v in groups.values() if len(v)>1]}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--corpus',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();c=json.loads(a.corpus.read_text());out=[]
 for r in c['classes']:
  if r['states']!=194:continue
  p=a.corpus.parent/'representatives'/(r['graph_hash']+'.tm');out.append({'table_class':r['table_class'],**refine(p)})
 result={'snapshot':c['summary']['snapshot'],'scope':__doc__,'graphs_checked':len(out),'reducible_graphs':sum(r['quotient_states']<194 for r in out),'results':out};a.out.write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='results'})
if __name__=='__main__':main()
