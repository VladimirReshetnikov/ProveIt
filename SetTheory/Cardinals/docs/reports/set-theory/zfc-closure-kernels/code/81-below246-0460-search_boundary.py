from pathlib import Path
import sys,json
src=Path('/workspace/scratch/b65d0f102007/sources/context246/zfc-context246')
sys.path.insert(0,str(src/'code'))
from check_literal_instructions import read_table
T=read_table(src/'machine/zfc_prefix246_old.tm')
states=sorted({q for q,b in T}-{255})
def test(row,kind,y=0):
 tab=T.copy();tab[75,0]=row
 one={-2}|(set(range(1,y+2)) if kind=='zero' else set())
 initial=one.copy();q=75;h=0
 for n in range(3000):
  if n and ((q,h)==(112,-3) if kind=='zero' else (q,h)==(48,-2)):
   if kind=='zero':return one==initial-{-2}|{-1},n
   return any(one=={-2}|set(range(0,k+1)) for k in range(0,16)),n
  if h < -2 or h>24 or q==255:return False,n
  if (q,int(h in one)) not in tab:return False,n
  w,d,q=tab[q,int(h in one)]
  if w:one.add(h)
  else:one.discard(h)
  h+=d
 return False,n
hits=[]
for q in states:
 for w in (0,1):
  for d in (-1,1):
   row=w,d,q
   answers=[test(row,'zero',y) for y in (0,1,3)]
   if all(a for a,n in answers):
    tail=test(row,'tail')
    print('ZERO',row,answers,'TAIL',tail,flush=True)
    if tail[0]:hits.append(row)
print('HITS',hits)
