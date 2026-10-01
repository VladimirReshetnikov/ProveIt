import sympy as s,json
from math import comb
from pathlib import Path
from increment_families import raw,k,N,K,h,L,z
x,y,w=s.symbols('x y w')
def choose(n,j):return comb(n,j) if 0<=j<=n else 0
def audit(b,rows):
 count=0
 for row in rows:
  lam=tuple(row['lambda']);mu=row['mu'];kv=int(row['k']);p=mu.count(2);q=mu.count(1);d=2*kv-2*p-q
  assert d in range(sum(lam))
  subs={k:kv,N:b+2}
  for j in range(-1,4):subs[s.Symbol('b'+str(j).replace('-','m'))]=choose(q,kv-j-p)
  moments={0:s.S.One,1:s.S.One,2:x,3:y,4:w}
  for off,ell in L.items():subs[ell]=moments.get(kv+off,0 if kv+off<0 else s.Symbol('E'+str(kv+off)))
  co=s.expand(raw(lam,d).subs(subs))
  target=s.sympify(row['coefficient'],locals={'x':x,'y':y,'z':z,'w':w})
  assert s.expand(co-target)==0,(b,row,co,target)
  count+=1
 return count
j3=json.loads(Path(__file__).with_name('regression_rank5_orbits.json').read_text())
j4=json.loads(Path(__file__).with_name('regression_rank6_orbits.json').read_text())
r4=[dict(row,k=int(kv)) for kv,rows in j4.items() for row in rows]
out={'rank5_orbits':audit(3,j3),'rank6_orbits':audit(4,r4),'all_exact':True}
Path(__file__).with_name('finite_table_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
