import sys,json,time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;m=S.load_machine(out/'h_only_seed.tm');raw=json.loads((out/'h_only_seed_sites.json').read_text());sites=[(tuple(p),tuple(op)) for p,op in raw];S.all_sites=lambda:sites;cs=S.contracts();special=[c for c in cs if c[0]==3800];hits=[]
for q in range(196):
 for w,d in [(0,1),(0,-1),(1,1),(1,-1)]:
  n=dict(m);n[37,0]=(w,d,q)
  if any(S.execute(n,br,s,t) is None for i,b,br,s,t in special):continue
  try:summary,_=S.verify(n)
  except AssertionError:continue
  item={'row':[37,0,w,d,q],'summary':summary};hits.append(item);print('HIT',item,flush=True)
  (out/f'h_clear_{q}_{w}_{d}.tm').write_text(''.join(f'{s} {b} {w} {"R" if d==1 else "L"} {t}\n' for (s,b),(w,d,t) in sorted(n.items())))
(out/'h_clear_provider_results.json').write_text(json.dumps(hits,indent=2)+'\n');print('DONE',len(hits),flush=True)
