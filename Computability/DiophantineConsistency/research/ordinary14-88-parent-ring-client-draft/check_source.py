from pathlib import Path
import hashlib,json,random
p=Path(__file__).resolve().parent;D=p.parents[1]
a=json.loads((D/'research/ordinary14-guarded-fold88-26/candidate.json').read_bytes())
b=json.loads((D/'research/ordinary13-four-square88-30/candidate.json').read_bytes())
def shape(g,t):
 rows={n:(op,x,y) for n,op,x,y in g['source']}
 def go(v):
  if v not in rows:return ('leaf',v)
  op,x,y=rows[v];return (op,go(x),go(y))
 return go(t)
for f in ('A1','Fa','g72'):assert shape(a,f)==shape(b,f),f
assert a['witnesses'][:13]==b['witnesses']
rng=random.Random(1388)
for _ in range(500):
 q3,b0,ell,k,t,s,tau=[rng.randrange(-4,5) for _ in range(7)]
 Y=q3*s;r=k*b0*t+t+tau-ell-k-s
 assert q3*b0*(ell+k+r-k*b0*t)+Y*b0-q3*b0*t==q3*b0*tau
s=(p/'Ring88ToParent.lean').read_text()
for t in ('j.castSucc','theorem first_cut','P88FourSquare.graph p','P88QuotientGuarded.graph p','theorem main_eval','theorem aux_eval','theorem strong_eval'):assert t in s
print(json.dumps({'shared_three_DAGs':True,'signed_fresh_root_controls':500,'lean_run':False,'source_sha256':hashlib.sha256((p/'Ring88ToParent.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
