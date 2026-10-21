#!/usr/bin/env python3
"""Exact rooted transition-graph classification and shared-scanner check."""
from pathlib import Path
import argparse,hashlib,json,importlib.util
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--summary',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
sp=importlib.util.spec_from_file_location('inv',HERE/'invariant.py');inv=importlib.util.module_from_spec(sp);sp.loader.exec_module(inv)
rows=[]
for x in json.loads(a.summary.read_text())['results']:
 path=a.source/x['relative_path'];T,start=inv.read(path);states={q for q,b in T};H=(set(z for w,d,z in T.values())-states).pop()
 assert hashlib.sha256(path.read_bytes()).hexdigest()==x['table_sha256']
 def can(reflect=1):
  order=[start];ids={start:0};rows=[]
  for q in order:
   row=[]
   for b in(0,1):
    w,d,z=T[q,b]
    if z!=H and z not in ids:ids[z]=len(order);order.append(z)
    row.append([w,reflect*d,'H' if z==H else ids[z]])
   rows.append(row)
  assert len(order)==len(states)
  return hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()
 scanner={(40,0):(0,-1,4),(40,1):(1,-1,54),(54,0):(0,-1,40),(54,1):(1,-1,54)}
 rows.append({'name':x['name'],'literal_sha256':x['table_sha256'],'rooted_graph_sha256':can(),'global_reflection_sha256':can(-1),'all_working_states_graph_reachable':True,'scanner40_54_same_as_primary':all(T[k]==v for k,v in scanner.items())})
out={'method':'BFS from declared start, read0 before read1; exact write, direction and numbered target labels; halt as H. Global reflection reverses all directions. This tests rooted labelled transition-graph isomorphism, not behavioral equivalence.','literal_tables':len(rows),'distinct_literal_hashes':len({x['literal_sha256'] for x in rows}),'distinct_rooted_graphs':len({x['rooted_graph_sha256'] for x in rows}),'distinct_up_to_reflection':len({min(x['rooted_graph_sha256'],x['global_reflection_sha256']) for x in rows}),'rows':rows}
a.out.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
