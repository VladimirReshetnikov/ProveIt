import json
from pathlib import Path
p=Path(__file__).resolve().parent/'data/k219/research/encoding'
at=json.loads((p/'atoms.json').read_text());at+=[[['CD',5],['CC',1]],['CB',2],['CB',3],['CC',4]]
M=6;W=M+1
def ev(n,a,b,limit=100):
 if isinstance(n[0],str):
  op,k=n
  if op=='CB':return a,b,k
  if op=='CC':return a,b,8+k
  v=a if k==5 else b
  if op=='CD':return (max(0,a-1),b,0 if v else 1)if k==5 else(a,max(0,b-1),0 if v else 1)
  return(a+1,b,0)if k==5 else(a,b+1,0)
 seen=set()
 for _ in range(limit):
  if(a,b)in seen:raise ValueError('loop')
  seen.add((a,b));a,b,k=ev(n[0],a,b)
  if a>M or b>M:raise ValueError('over')
  if k:return a,b,k-1 if k<8 else k
  a,b,k=ev(n[1],a,b)
  if a>M or b>M:raise ValueError('over')
  if k==9:continue
  return a,b,k-1 if k>9 else k
 raise ValueError('fuel')
rows=[]
for n in at:
 ss=[]
 for a in range(W):
  for b in range(W):
   try:x,y,k=ev(n,a,b);v=(x*W+y)*16+k if x<=M and y<=M else-1
   except ValueError:v=-1
   ss.append(v)
 rows.append(ss)
(Path(__file__).resolve().parent/'eqatoms.json').write_text(json.dumps(at))
(Path(__file__).resolve().parent/'eqatoms.in').write_text(f'{M} {len(at)}\n'+''.join(' '.join(map(str,ss))+'\n'for ss in rows))
s=(p/'eq_superopt.cpp').read_text().replace('trials++;Node n;','if(b>=4&&b<=7)continue;trials++;Node n;').replace('g.size()>800000','g.size()>3000000')
(Path(__file__).resolve().parent/'eq_left.cpp').write_text(s)
