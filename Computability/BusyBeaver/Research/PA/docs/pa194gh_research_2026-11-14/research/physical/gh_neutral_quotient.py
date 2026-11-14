from pathlib import Path
import json,subprocess,time
root=Path(__file__).resolve().parent
src=root/'gh_input/machine.native.tm'
rows={}
for l in src.read_text().splitlines():
 q,b,w,d,n=l.split();rows[int(q),int(b)]=[int(w),1 if d=='R'else-1,int(n)]
edits=[json.loads(l)for l in(root/'gh_neutral_k6.jsonl').read_text().splitlines()]
focused=[(i,x)for i,x in enumerate(edits)if x['state']in{38,214,312,11,122,20,188}]
out=root/'gh_focused_neutral';out.mkdir(exist_ok=True)
summary=[]
for i,e in focused:
 r=dict(rows);r[e['state'],e['read']]=e['new']
 path=out/f'edit_{i}.native.tm';path.write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'for(q,b),(w,d,n)in sorted(r.items())))
 with(out/f'edit_{i}.hits.jsonl').open('w')as hits,(out/f'edit_{i}.log.txt').open('w')as log:
  subprocess.run([str(root/'joint_return_merge'),str(path),'4','100',str(root/'gh_patterns_k4.txt')],stdout=hits,stderr=log,check=True)
 hitlines=(out/f'edit_{i}.hits.jsonl').read_text().splitlines();last=(out/f'edit_{i}.log.txt').read_text().splitlines()[-1]
 print(i,e,len(hitlines),last,flush=True)
 summary.append({'edit_index':i,'edit':e,'hit_count':len(hitlines),'last_log':last})
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
