#!/usr/bin/env python3
"""Reproduce the exact K226 extension of the frozen K227 package."""
from pathlib import Path
import argparse,hashlib,json,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H/'verification'))
from verify_duplicate import read,prove

def encode(t,start):return(f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()

def main():
 p=argparse.ArgumentParser();p.add_argument('--base',type=Path,required=True,help='Frozen native227_evidence directory');p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 chain=json.loads((H/'selected/construction_chain.json').read_text());parent=a.base/'selected/k227_k230labels.tm'
 assert hashlib.sha256(parent.read_bytes()).hexdigest()==chain['parent_table_sha256']
 t=read(parent)
 def patch(stage):
  for e in stage['literal_edits']:
   key=tuple(e['row']);assert list(t[key])==e['before'];t[key]=tuple(e['after'])
 patch(chain['first_rotation'])
 before=encode(t,0);assert before==(H/'controls/prequotient227_k230labels.tm').read_bytes()
 assert t[65,0]==t[98,0]and t[65,1]==t[98,1]
 t={(q,b):(w,d,98 if z==65 else z)for(q,b),(w,d,z)in t.items()if q!=65}
 intermediate=encode(t,0);assert intermediate==(H/'controls/postquotient226_k230labels.tm').read_bytes()
 for stage in chain['repair_rotations']['history']:patch(stage)
 states=sorted({q for q,b in t});assert len(states)==226 and set(states)==set(range(230))-{65,79,140,175}
 m={int(q):z for q,z in json.loads((a.base/'reference/normalization230.json').read_text())['k230_to_native'].items()}
 number={q:i for i,q in enumerate(states)}|{230:226}
 assert number=={int(q):z for q,z in json.loads((H/'selected/numbering.json').read_text())['k230_to_canonical'].items()}
 raw={'k226_k230labels.tm':encode(t,0),'k226_native.tm':encode({(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in t.items()},95),
 'k226.tm':encode({(number[q],b):(w,d,number[z])for(q,b),(w,d,z)in t.items()},0)}
 a.output.mkdir(parents=True,exist_ok=True)
 for name,data in raw.items():
  assert data==(H/'selected'/name).read_bytes()
  assert hashlib.sha256(data).hexdigest()==chain['expected_table_sha256'][name]
  (a.output/name).write_bytes(data)
 visited=set();todo=[0]
 while todo:
  q=todo.pop()
  if q in visited:continue
  visited.add(q)
  if q!=230:todo.extend(t[q,b][2]for b in(0,1))
 assert visited==set(states)|{230}
 proof=prove(H/'controls/prequotient227_k230labels.tm',H/'controls/postquotient226_k230labels.tm')
 out={'status':'EXACT_K226_CONSTRUCTION_AND_QUOTIENT_PASS','working_states':226,'start':0,'dispatcher':82,'halt':226,
 'all_working_states_graph_reachable':True,'closed_rotation_stages':6,'checked_quotient_rows':proof['checked_old_rows'],
 'artifacts':{name:hashlib.sha256(data).hexdigest()for name,data in raw.items()}}
 (a.output/'construction_replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
