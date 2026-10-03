import json,math,itertools,hashlib
from pathlib import Path
src=(Path(__file__).resolve().parents[1] / 'data/semigroup.json').read_bytes()
if hashlib.sha256(src).hexdigest()!='506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9':raise RuntimeError('pin')
j=json.loads(src); tiles=[t for t in j['tiles'] if t['g']!='#']
def edges(w):
 out=[]
 def f(p,h,ids):
  if p==len(w):out.append((h,len(ids)+1,tuple(ids)));return
  for t in tiles:
   if w.startswith(t['g'],p):f(p+len(t['g']),h+t['h'],ids+[t['id']])
 f(0,'',[])
 return out

def test(w):
 graph={}; todo=[w]
 while todo:
  v=todo.pop()
  if v in graph:continue
  graph[v]=edges(v)
  if len(graph)>1000:raise RuntimeError('unexpectedlargegraph')
  todo.extend(x for x,_,_ in graph[v] if x not in graph)
 if 'X' not in graph:raise RuntimeError('nonacceptingtest')
 live=[];v=w
 while 'J1' not in v:
  live.append(v);following=[e for e in graph[v] if e[0]!=v]
  if len(following)!=1:raise RuntimeError('live not deterministic')
  v=following[0][0]
 live.append(v);p=v.index('J1');left=v[1:p];right=v[p+2:-1];m=len(left)+len(right)
 C=math.comb(m,len(left)); weights=[len(x)+1 for x in live]+list(range(4,m+5))+[2]
 r0=sum(len(x)-1 for x in live[:-1])+len(live[-1])+sum(range(4,m+4))+2
 end=r0+100
 predicted=[0]*(end+1);predicted[r0]=C
 for L in weights:
  for r in range(L,end+1):predicted[r]+=predicted[r-L]
 order=list(graph); pos={v:i for i,v in enumerate(order)}
 dp=[[0]*len(order) for _ in range(end+1)];dp[0][pos[w]]=1
 for r in range(end+1):
  for v,i in pos.items():
   n=dp[r][i]
   if n:
    for dest,L,_ in graph[v]:
     if r+L<=end:dp[r+L][pos[dest]]+=n
 actual=[row[pos['X']] for row in dp]
 if actual!=predicted:raise RuntimeError((w,'coefficient mismatch'))
 for r,count in enumerate(actual):
  expected=r==r0 or r==r0+2 or r>=r0+4
  if bool(count)!=expected:raise RuntimeError((w,'support'))
 return {'input':w,'states':len(graph),'r0':r0,'C':C,'weights':weights,'coefficients_checked':end+1}
words=[''.join(b) for n in range(4) for b in itertools.product('01',repeat=n)]
rows=[test('[110A0]')]+[test('['+l+'J1'+r+']') for l in words for r in words]
report={'status':'PASS','cases':len(rows),'coefficient_comparisons':sum(x['coefficients_checked'] for x in rows),'actual_tape_example':rows[0],'max_cleanup_paths':max(x['C'] for x in rows),'method':'Literal g-side tile partition enumeration and weighted finite graph DP, independent of matrix compiler and proposed fiber code'}
print(json.dumps(report,indent=2))
