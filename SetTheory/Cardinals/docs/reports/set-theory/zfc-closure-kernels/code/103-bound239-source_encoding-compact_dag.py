"""Discard unused search nodes while preserving source-ID order and replay history."""
import argparse,json
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('output',type=Path);a=p.parse_args();j=json.loads(a.input.read_text());s=j['structures'];keep=set(range(min(225,len(s))));todo=[j['root']]
if isinstance(j.get('original_root'),int):todo.append(j['original_root'])
for move in j.get('history',[]):
 if not isinstance(move,dict):continue
 for key in ('node','alternative'):
  if isinstance(move.get(key),int):todo.append(move[key])
 todo.extend(v for v in move.get('chunks',[]) if isinstance(v,int))
seen=set()
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);keep.add(n)
 if isinstance(s[n][0],int):todo.extend(s[n])
ids={n:i for i,n in enumerate(sorted(keep))};j['structures']=[[ids[x] for x in s[n]] if isinstance(s[n][0],int) else s[n] for n in sorted(keep)];j['root']=ids[j['root']]
if isinstance(j.get('original_root'),int):j['original_root']=ids[j['original_root']]
for move in j.get('history',[]):
 if not isinstance(move,dict):continue
 for key in ('node','alternative'):
  if isinstance(move.get(key),int):move[key]=ids[move[key]]
 if 'chunks' in move:move['chunks']=[ids[v] for v in move['chunks']]
if isinstance(j.get('score'),list) and isinstance(j['score'][-1],list):j['score'][-1]=[ids[v] for v in j['score'][-1]]
j['storage_compaction']={'original_records':len(s),'retained_records':len(keep),'ordered_old_ids_preserved':True}
a.output.write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j['storage_compaction']))
