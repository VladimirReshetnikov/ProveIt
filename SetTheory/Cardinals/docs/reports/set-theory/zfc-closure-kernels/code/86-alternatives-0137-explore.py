from pathlib import Path
import sys
BASE=Path('research_sub246/context_folds/recovered/64/baseline/context246')
sys.path.insert(0,str(BASE/'code'))
from check_literal_instructions import read_table
T=read_table(BASE/'machine/zfc_prefix246_old.tm')

def B(vs):return ''.join('0'+'1'*(v+1) for v in vs)
def run(T,vs=[0,0],r=0,q=73,steps=200):
 s=list(B(vs));s[sum(v+2 for v in vs[:r])+1]='0';one={i for i,b in enumerate(s) if b=='1'};h=0
 for j in range(steps):
  if h<0: return j,q,h,''.join(str(int(i in one)) for i in range(-3,len(s)+10))
  w,d,q=T[q,int(h in one)]
  if w:one.add(h)
  else:one.discard(h)
  h+=d
 return None
if __name__=='__main__':
 for edits in ({},{(75,0):(0,-1,112)},{(75,0):(0,1,63),(48,0):(1,-1,131)}, {(75,0):(1,1,63),(48,0):(1,-1,131)}):
  t=T|edits;print(edits)
  for q in [73,95]:
   for vs in [[0,0],[1,0],[0,1],[0,2],[1,2],[3,2,1],[2,0,3]]:
    print(q,vs,run(t,vs=vs,q=q))
