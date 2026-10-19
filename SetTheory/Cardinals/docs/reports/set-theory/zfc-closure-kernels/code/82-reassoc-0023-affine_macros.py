import sys,json
from functools import cache
from collections import Counter
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent));import rotation_candidate as m
DIM=10
I=tuple(tuple(int(i==j) for j in range(DIM)) for i in range(DIM))
def compose(a,b):
 # B after A
 return tuple(tuple(sum(b[i][k]*a[k][j] for k in range(DIM)) for j in range(DIM)) for i in range(DIM))
def trans(r):
 a=[list(x) for x in I];a[r][9]+=1;return tuple(map(tuple,a))
def translation(a):
 return all(a[i][j]==I[i][j] for i in range(DIM) for j in range(9))
@cache
def summary(e):
 kind,*rr=e.split();r=int(rr[0]) if rr else None
 if kind=='EInc':return trans(r),('N',0)
 if kind=='EBreak':return I,('B',r) if r else ('N',0)
 if kind=='EContinue':return I,('C',r)
 if kind!='ENode':return None
 left,right=m.nodes[r];l=summary(left);s=summary(right)
 if l:
  a,(k,n)=l
  if k=='B':return a,('B',n-1) if n>1 else ('N',0)
  if k in ('C','H'):return l
  if s:
   b,(kk,nn)=s;c=compose(a,b)
   if kk=='C':
    if nn>1:return c,('C',nn-1)
    else:return None
   return c,(kk,nn)
 if left.startswith('EDecnz ') and s:
  r=int(left.split()[1]);a,exit=s
  if exit==('C',1) and translation(a) and a[r][9]==0:
   # decrement selected counter and execute a fixed translation until zero.
   b=[list(row) for row in I]
   for i in range(9):b[i][r]+=a[i][9]
   b[r][r]=0
   return tuple(map(tuple,b)),('N',0)
 return None

def describe(a):
 out=[]
 for i in range(9):
  if a[i]!=I[i]:
   vals=[f'{v}*r{j}' if v!=1 else f'r{j}' for j,v in enumerate(a[i][:9]) if v]
   if a[i][9]:vals.append(str(a[i][9]))
   out.append(f'r{i}='+('+'.join(vals) if vals else '0'))
 return ','.join(out)
if __name__=='__main__':
 qsum={}
 for q,ns in sorted(m.q2nodes.items()):
  ss={summary('ENode '+str(n)) for n in ns}
  if len(ss)==1 and None not in ss:
   a,e=ss.pop()
   if e==('N',0):qsum[q]=a;print(q,describe(a))
 print('NORMAL AFFINE STATES',len(qsum))
 print('COMMUTATIONS');commutations=[]
 for (q,b),(w,d,t) in m.T.items():
  if b:continue
  a=m.T[q,0];b=m.T[q,1]
  if a[:2]==(0,'R') and b[:2]==(1,'R') and a[2] in qsum and b[2] in qsum:
   aa,bb=qsum[a[2]],qsum[b[2]]
   if compose(aa,bb)==compose(bb,aa):
    print(q,a[2],b[2],'COMMUTE');commutations.append([q,a[2],b[2]])
 (m.HERE/'rotation_candidates/affine_macros.json').write_text(json.dumps(dict(scope='syntactic recognizer of exact affine summaries; no claim of completeness',normal_affine_states={str(q):dict(effect=describe(a),matrix=a)for q,a in qsum.items()},commutations=commutations),indent=2)+'\n')
