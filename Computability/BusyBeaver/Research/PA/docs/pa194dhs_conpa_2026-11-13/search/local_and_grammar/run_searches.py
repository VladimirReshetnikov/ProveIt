#!/usr/bin/env python3
"""Replay finite local screens and optional heuristic searches. C++17 required.

The output directory must not already exist. Timed searches do not reproduce
identical iteration counts across machines. No search result certifies a machine.
"""
from pathlib import Path
import argparse, subprocess, json, os
ROOT=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--grammar',action='store_true',help='also run 600s + 600s + 120s heuristic searches')
 p.add_argument('--grammar-seconds',type=float,default=600)
 p.add_argument('--top-seconds',type=float,default=120)
 p.add_argument('--compiler',default='g++')
 a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 env=dict(os.environ,TMPDIR=str(out))
 targets=['pair_all','pair_blank','edge_bypass','pair_join','order_screen']
 if a.grammar:targets+=['reassociate','ordered_search']
 for name in targets:
  subprocess.run([a.compiler,'-O3','-std=c++17',str(ROOT/'code'/f'{name}.cpp'),'-o',str(out/name)],check=True,env=env)
 I=ROOT/'inputs'
 cases=[
  ('action194_all_k4','pair_all','pa194.native.tm',4,80),
  ('action194_blank_k6','pair_blank','pa194.native.tm',6,120),
  ('top195_blank_k6','pair_blank','top195.native.tm',6,300),
  ('dhs194_blank_k7','pair_blank','pa194dhs.native.tm',7,300),
  ('dhs194_bypass_k7','edge_bypass','pa194dhs.native.tm',7,300)]
 records=[]
 for name,exe,table,radius,horizon in cases:
  cmd=[str(out/exe),str(I/table),str(radius),str(horizon)]
  with (out/f'{name}.jsonl').open('w')as stdout,(out/f'{name}.log').open('w')as stderr:
   subprocess.run(cmd,stdout=stdout,stderr=stderr,check=True)
  found=[json.loads(s)for s in(out/f'{name}.jsonl').read_text().splitlines()if s.strip()]
  records.append({'name':name,'radius':radius,'horizon':horizon,'candidate_count':len(found),'command':cmd})
 for name,table,radius,old_bound,new_bound in [('dhs_join_k4','pa194dhs.native.tm',4,40,120),('dhs_join_k6','pa194dhs.native.tm',6,80,240),('top_join_k6','top195.native.tm',6,80,240)]:
  cmd=[str(out/'pair_join'),str(I/table),str(radius),str(old_bound),str(new_bound)]
  with(out/f'{name}.jsonl').open('w')as stdout,(out/f'{name}.log').open('w')as stderr:
   subprocess.run(cmd,stdout=stdout,stderr=stderr,check=True)
  found=[json.loads(s)for s in(out/f'{name}.jsonl').read_text().splitlines()if s.strip()]
  records.append({'name':name,'radius':radius,'old_prefix_bound':old_bound,'replacement_bound':new_bound,'candidate_count':len(found),'command':cmd})
 cmd=[str(out/'order_screen'),str(I/'dhs_ordered.txt'),str(I/'dhs_leaf_attrs.txt'),str(out/'order_screen')]
 with(out/'order_screen.log').open('w')as log:subprocess.run(cmd,stdout=log,check=True)
 if a.grammar:
  runs=[('dhs','reassociate','dhs_reassociation.txt','dhs_leaf_attrs.txt',a.grammar_seconds,202611141931),
        ('ordered','ordered_search','dhs_ordered.txt','dhs_leaf_attrs.txt',a.grammar_seconds,202611141932),
        ('top_normalized','reassociate','top_reassociation.txt','top_leaf_attrs.txt',a.top_seconds,202611141933)]
  for name,exe,inp,attr,seconds,seed in runs:
   cmd=[str(out/exe),str(I/inp),str(I/attr),str(out/name),str(seconds),str(seed)]
   with(out/f'{name}.log').open('w')as log:subprocess.run(cmd,stdout=log,check=True)
 (out/'local_summary.json').write_text(json.dumps(records,indent=2)+'\n')
 print(json.dumps(records,indent=2))
if __name__=='__main__':main()
