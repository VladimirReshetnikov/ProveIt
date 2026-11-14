from pathlib import Path
import sys,json,time,types
from site_contexts import contexts
import search_generic as G
import search_future as F
S=G.S;root=Path(__file__).resolve().parents[1]
variant=sys.argv[1]if len(sys.argv)>1 else'original'
if variant=='original':m=S.load_machine();sites=S.all_sites()
elif variant=='h':
 base=root/'comparison/audit/h_catalan_node170_3_133_37'
 m=S.load_machine(str(base)+'.tm')
 sites=[(tuple(p),tuple(op))for p,op in json.loads(Path(str(base)+'_sites.json').read_text())]
else:
 base=root/'verification/candidates/open_physical_61_201240_safe'
 m=S.load_machine(str(base)+'.tm')
 def tuples(v):return tuple(map(tuples,v))if isinstance(v,list)else v
 sites=S.flatten(tuples(json.loads(Path(str(base)+'.json').read_text())['tree']))
S.all_sites=lambda:sites
begin=time.time();ctx=contexts(4,True,m)
for module in [G,F]:
 # Remove ROOT from the candidate exclusion without changing symbolic frames.
 src=Path(module.__file__).read_text().split("if __name__=='__main__':")[0]
 src=src.replace('|{0,S.ROOT}','|{0}')
 ns={'__file__':module.__file__};exec(src,ns)
 candidates=ns['candidates'](m,ctx)
 candidates=[(q,p,a,b)for q,p,a,b in candidates if 75 in(q,p)]
 print(module.__name__,variant,'CANDIDATES',candidates,flush=True)
 for q,p,a0,a1 in candidates:
  if p==75:q,p=p,q
  n=m.copy();n[q,0]=a0;n[q,1]=a1;del n[p,0];del n[p,1]
  n={k:(w,d,q if s==p else s)for k,(w,d,s)in n.items()}
  try:totals,_=S.verify(n)
  except Exception as e:print('FAIL',q,p,e,flush=True);continue
  print('SUCCESS',q,p,a0,a1,totals,flush=True)
  Path(__file__).with_name(f'root_{variant}_success.tm').write_text(''.join(f'{qq} {bb} {w} {"R"if d==1 else"L"} {t}\n'for(qq,bb),(w,d,t)in sorted(n.items())))
print('seconds',time.time()-begin)
