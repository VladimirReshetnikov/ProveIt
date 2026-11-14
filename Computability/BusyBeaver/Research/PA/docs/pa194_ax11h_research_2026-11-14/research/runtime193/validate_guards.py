from pathlib import Path
import sys,json,hashlib
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'vendor'));import compiler as c
base={}
for l in (P/'runtime193.native.tm').read_text().splitlines():
 q,b,w,d,t=l.split();base[int(q),int(b)]=int(w),d=='R',int(t)
sites,ins,cs=c.source(c.read_grammar(P/'pa194.grammar.json'))
out=[]
for i,line in enumerate(Path(sys.argv[1]).read_text().splitlines()):
 a,b,_=line.split('|');rows=base.copy();es=[]
 for e in [a,b]:
  q,s,w,d,t=map(int,e.split());rows[q,s]=w,d==1,t;es.append([q,s,w,d,t])
 v=c.validate(rows,cs);v.update(index=i,edits=es);out.append(v);print(json.dumps(v),flush=True)
 if v['ok']:
  path=Path(sys.argv[2])/f'candidate{i}.tm';path.parent.mkdir(parents=True,exist_ok=True)
  path.write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {t}\n' for (q,b),(w,d,t) in sorted(rows.items())))
Path(sys.argv[2]).mkdir(parents=True,exist_ok=True);(Path(sys.argv[2])/'summary.json').write_text(json.dumps(out,indent=2))
