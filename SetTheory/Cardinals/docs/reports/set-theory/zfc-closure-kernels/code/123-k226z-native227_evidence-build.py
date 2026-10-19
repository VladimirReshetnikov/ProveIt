#!/usr/bin/env python3
"""Reconstruct the selected227 and native control tables from frozen K230."""
from pathlib import Path
import argparse,hashlib,json
H=Path(__file__).resolve().parent
sha=lambda data:hashlib.sha256(data).hexdigest()
def read(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  assert (q,b) not in t and b in(0,1) and w in(0,1) and d in('L','R')
  t[q,b]=(w,1 if d=='R' else -1,z)
 return t
def encode(t,start):
 return (f'#! start {start}\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z) in sorted(t.items()))).encode()
def delay(t):
 n={(q,b):(w,d,80 if z==169 else z) for(q,b),(w,d,z) in t.items() if q!=169}
 n[80,0]=(0,-1,106);n[91,1]=(1,-1,167);return n
def generate(output):
 recipe=json.loads((H/'selected/recipe.json').read_text());original=H/'reference/k230.tm'
 assert sha(original.read_bytes())==recipe['upstream_sha256']
 t=read(original);assert set(t)=={(q,b) for q in range(230) for b in(0,1)}
 m={int(q):z for q,z in json.loads((H/'reference/normalization230.json').read_text())['k230_to_native'].items()}
 assert set(m)==set(range(231)) and len(set(m.values()))==231 and(m[0],m[84],m[230])==(95,96,254)
 native={(m[q],b):(w,d,m[z]) for(q,b),(w,d,z) in t.items()}
 controls={'k230_native.tm':native,'k229_native.tm':delay(native)}
 rot=dict(native);assert rot[142,0]==(0,1,37) and rot[142,1]==(1,1,72)
 rot[142,0]=(0,1,72);rot[142,1]=(1,1,17);controls['k230_H_native.tm']=rot
 h={(q,b):(w,d,72 if z==90 else z) for(q,b),(w,d,z) in rot.items() if q!=90}
 h[72,0]=(0,-1,144);h[72,1]=(1,-1,36)
 controls['k229_H_native.tm']=h;controls['k228_H_native.tm']=delay(h)
 selected={(q,b):a for(q,b),a in t.items() if q not in recipe['delete']}
 for e in recipe['retained_row_edits']:
  k=e['state'],e['read'];assert list(t[k])==e['before'] and k in selected
  selected[k]=tuple(e['after'])
 states={q for q,b in selected};assert states==set(range(230))-set(recipe['delete']) and len(states)==227
 assert set(selected)=={(q,b) for q in states for b in(0,1)} and{z for w,d,z in selected.values()}-states=={230}
 dense={q:i for i,q in enumerate(sorted(states))}|{230:227}
 numbering=json.loads((H/'selected/numbering.json').read_text())
 assert dense=={int(q):z for q,z in numbering['k230_to_canonical'].items()}
 artifacts={'selected/k227_k230labels.tm':encode(selected,0),
 'selected/k227_native.tm':encode({(m[q],b):(w,d,m[z]) for(q,b),(w,d,z) in selected.items()},95),
 'selected/k227.tm':encode({(dense[q],b):(w,d,dense[z]) for(q,b),(w,d,z) in selected.items()},0)}
 artifacts.update({'controls/'+name:encode(table,95) for name,table in controls.items()})
 for name,raw in artifacts.items():
  assert raw==(H/name).read_bytes(),('Construction differs',name)
  target=output/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
 reached=set();todo=[0]
 while todo:
  q=todo.pop()
  if q in reached:continue
  reached.add(q)
  if q!=230:todo.extend(selected[q,b][2] for b in(0,1))
 assert reached==states|{230}
 receipt={'status':'ALL_EIGHT_LITERAL_TABLES_BYTE_IDENTICAL','selected_states':227,'all_selected_states_graph_reachable':True,
 'retained_row_edits':len(recipe['retained_row_edits']),'artifacts':{name:sha(raw) for name,raw in artifacts.items()}}
 (output/'construction_replay.json').write_text(json.dumps(receipt,indent=2)+'\n');return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args();print(json.dumps(generate(a.output),indent=2))
