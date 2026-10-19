#!/usr/bin/env python3
"""Deterministically re-emit the retained normalized246 literal table.

Unlike the time-bounded searches, this replay has a fixed finite workload.
The independent source and runtime audits remain separate proof layers.
"""
from pathlib import Path
import argparse,json,hashlib
import colored_generic_search as search

def read_table(path):
 result={}
 for line in path.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,t=line.split();key=int(q),int(b)
   assert key not in result
   result[key]=int(w),d,int(t)
 return result

def main():
 root=Path(__file__).resolve().parents[2]
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=root/'experiments/logic/selected_emission_replay.json');a=ap.parse_args()
 inputs=root/'experiments/logic/inputs'
 search.rebase_rotated(inputs/'s7_best_018.json',inputs/'s7_best_018.tm')
 graph=root/'machines/normalized246.graph.json'
 roles=root/'machines/normalized246.roles.json'
 target=root/'machines/normalized246_old.tm'
 data=json.loads(graph.read_text());memo={}
 def imp(n):
  if n not in memo:
   e=data['entries'][str(n)]
   memo[n]=search.r.mk(('N',imp(e[1]),imp(e[2]))) if e[0]=='N' else search.r.mk(tuple(e))
  return memo[n]
 source=imp(data['root'])
 colors={memo[int(n)]:q for n,q in json.loads(roles.read_text())['roles'].items()}
 assert search.context(source,colors,2)
 source_result=search.r.check(source,search.leaves,search.cases,set())
 assert source_result is not None and source_result['exact_all_guards']
 table=search.compile_graph(source,colors)
 assert table==read_table(target)
 result=dict(status='PASS',source_pairs=len(colors),working_states=len(table)//2,
             full_source_guard_cases=len(search.cases),emitted_rows=len(table),
             exact_literal_rows_equal=True,source_check=source_result,
             graph_sha256=hashlib.sha256(graph.read_bytes()).hexdigest(),
             table_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
             qualification='deterministic compiler replay; independent source, bootstrap, and universal runtime audits are separate')
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
