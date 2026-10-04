"""Own JSON-only finite profile union audit; no upstream modules/schedules used."""
from scan_motifs import maps,shift,union,black,stat,overlap,delta
import json
S=576000;W=960;E=S-600

def clip(d,lo=50,hi=450):return {q:c for q,c in d.items() if lo<=q[1]<hi}
def cut_shift(d,lo,hi,dy):return {(x,y+dy):c for (x,y),c in d.items() if lo<=y<hi}
def ew(x,y,n):return {(x+a,y+b-1):b for a in range(n) for b in [0,1]}
def vertical(ylo,yhi):return {(E+174+b,y):b for y in range(ylo,yhi) for b in [0,1]}
H=[];F=[];B=[]
def add(dest,label,d,dx=0):dest.append((label,d,dx))
N=clip(maps['NOT']);C=clip(shift(maps['COPY'],0,200));D=clip(maps['DELAY']);L=clip(maps['LEFT_TURN']);Lt=cut_shift(maps['LEFT_TURN'],450,477,-400)
for k in range(1,W-1):
 if k!=481:add(H,f'NOT{k}',N,600*k)
 add(H,f'COPY{k}',C,600*k)
 add(B,f'DELAY{k}',D,600*k)
 if k!=921:add(F,f'NOT{k}',N,600*k)
 add(F,f'prior_DELAY_tail{k}',cut_shift(maps['DELAY'],450,460,-400),600*k)
for k in range(W):
 key='LEFT_MARKER' if k==1 else 'RIGHT_MARKER' if k==921 else 'COPY'
 d=maps[key] if key!='COPY' else shift(maps['COPY'],0,200)
 add(H,f'prior_footer{k}',cut_shift(d,450,660,-400),600*k+S//2)
 if k not in [1,921]:add(F,f'COPY{k}',C,600*k)
for dest in [H,B]:
 add(dest,'LEFT_TURN',L,600);add(dest,'RIGHT_TURN',maps['RIGHT_TURN'],E)
for dest in [B,F]:add(dest,'prior_LEFT_TURN_tail',Lt,600)
add(H,'vertical_wire',vertical(80,450));add(B,'vertical_wire',vertical(50,450));add(F,'vertical_wire',vertical(50,70))
add(H,'CORNER_NE',shift(maps['CORNER_NE'],E+174,79));add(H,'top_east_wire',ew(E+180,75,1020))
add(F,'CORNER_EN',shift(maps['CORNER_EN'],E+170,70));add(F,'bottom_east_wire',ew(E,75,170))
add(F,'LEFT_MARKER',clip(maps['LEFT_MARKER']),600);add(F,'RIGHT_MARKER',clip(maps['RIGHT_MARKER']),600*921)

def audit(parts):
 # Bin descriptor references by x, then form one finite600-wide union at a time.
 buckets=[[] for _ in range(W)]
 raw_black=raw_cells=0
 for label,d,dx in parts:
  bins={(x+dx)%S//600 for x,y in d}
  for k in bins:buckets[k].append((label,d,dx))
  raw_black+=len(black(d));raw_cells+=len(d)
 unique_black=unique_cells=conflict_count=0;overlap_patterns={};conflict_samples=[]
 for k,pieces in enumerate(buckets):
  seen={}
  for label,d,dx in pieces:
   for (x,y),c in d.items():
    x=(x+dx)%S
    if x//600!=k:continue
    q=x,y
    if q in seen:
     c0,l0=seen[q]
     kind=(l0.rstrip('0123456789'),label.rstrip('0123456789'),str(c0),str(c))
     overlap_patterns[kind]=overlap_patterns.get(kind,0)+1
     if c0!=c:
      conflict_count+=1
      if len(conflict_samples)<10:conflict_samples.append([q,l0,label,c0,c])
    else:seen[q]=(c,label)
  unique_cells+=len(seen);unique_black+=sum(c==1 for c,l in seen.values())
 return {'raw_cells':raw_cells,'raw_black':raw_black,'unique_cells':unique_cells,'unique_black':unique_black,'conflicts':conflict_count,'conflict_samples':conflict_samples,'overlap_patterns':{'/'.join(k):v for k,v in sorted(overlap_patterns.items())}}
if __name__=='__main__':
 result={'header':audit(H),'bulk':audit(B),'footer':audit(F)}
 print(json.dumps(result,indent=2))
