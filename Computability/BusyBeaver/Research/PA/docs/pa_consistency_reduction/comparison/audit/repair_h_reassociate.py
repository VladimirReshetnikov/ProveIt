import sys,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;m=S.load_machine(out/'h_reassociate.tm');sites=[(tuple(p),tuple(op)) for p,op in json.loads((out/'h_reassociate_sites.json').read_text())];S.all_sites=lambda:sites;cs=S.contracts();special=[c for c in cs if c[0]==3799];hits=[];partial=[]
for q in range(196):
 for w,d in [(0,1),(0,-1),(1,1),(1,-1)]:
  n=dict(m);n[18,1]=(w,d,q)
  if any(S.execute(n,br,s,t) is None for i,b,br,s,t in special):continue
  item={'row':[18,1,w,d,q]}
  try:summary,_=S.verify(n)
  except AssertionError as e:item['failure']=str(e);partial.append(item);continue
  item['summary']=summary;hits.append(item);print('HIT',item,flush=True)
  (out/f'h_reassociate_fixed_{q}_{w}_{d}.tm').write_text(''.join(f'{s} {b} {w} {"R" if d==1 else "L"} {t}\n' for (s,b),(w,d,t) in sorted(n.items())))
(out/'h_reassociate_repair_results.json').write_text(json.dumps({'hits':hits,'partial':partial},indent=2)+'\n');print('DONE',len(hits),len(partial),flush=True)
