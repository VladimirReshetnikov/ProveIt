"""Finite JSON-only profile API. No upstream module is imported/executed.
Return H,B,F as length576000 lists of400-bit columns, and Q signed masks.
Bit0 means y50 for H/B, and y=F+50 for footer; Q uses bit0=local y50.
"""
from verify_profiles import H as H_parts,B as B_parts,F as F_parts,S,maps,union,shift,black

def build_profiles():
 def columns(parts):
  ans=[0]*S
  for label,d,dx in parts:
   for (x,y),c in d.items():
    assert 50<=y<450
    if c==1:ans[(x+dx)%S]|=1<<(y-50)
  return ans
 H=columns(H_parts);B=columns(B_parts);F=columns(F_parts)
 base=black(union(maps['DELAY'],shift(maps['DELAY'],600)))
 Q={}
 for kind in ['DUP','MOVE_LEFT','MOVE_RIGHT','NAND']:
  target=black(maps[kind]);cols={}
  for sign,points in [(0,target-base),(1,base-target)]:
   for x,y in points:
    assert 0<=x<1200 and 50<=y<450
    if x not in cols:cols[x]=[0,0]
    cols[x][sign]|=1<<(y-50)
  Q[kind]={x:tuple(v) for x,v in cols.items()}
 return H,B,F,Q
