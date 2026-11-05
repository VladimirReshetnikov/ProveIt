import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
 raise SystemExit('requires python3 -I -S -B without optimization')
graph=Path(__file__).resolve().parents[2]/'research/p64-qcube72-free-main-candidate/graph.json'
if hashlib.sha256(graph.read_bytes()).hexdigest()!='875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806':raise RuntimeError('graph pin mismatch')

def pairpow(x,y,d,e):
 a,b=1,0
 while e:
  if e&1:a,b=a*x+d*b*y,a*y+b*x
  e//=2
  if e:x,y=x*x+d*y*y,2*x*y
 return a,b
candidates=[];scale=[];nonpositive_h=[]
for R in (43,47):
 for s in range(1,301):
  Y=27*s; U=Y*Y; p=4*Y; power=1<<R
  for w in range(1,10001):
   X=3*w; a=(X+1)*Y; H=4*a+3
   if U*(power-X)%H: continue
   n=a+2; D=n*n-1;g,c=pairpow(n,1,D,R)
   if U*(g-X-a*c)%H:raise RuntimeError('projection fail')
   h=U*(g-X-a*c)//H
   if h<=0:
    nonpositive_h.append((R,s,w));continue
   candidates.append((R,s,w))
   P=X*U;t,k=1,0
   for j in range(1,R+1):
    t,k=(2*P+1)*t+2*P*(P+1)*k,2*t+(2*P+1)*k
    if Y*k>=c:break
    if c<(Y+1)*k:scale.append((R,s,w,j,(h+k-R-1)%U))
print(json.dumps({'status':'PASS_EXHAUSTIVE_BOUNDED_SCREEN','R':[43,47], 's_range':[1,300], 'w_range':[1,10000], 'first_index_range':[1,'R'], 'projection_count':len(candidates),'projection_candidates':candidates,'nonpositive_h':nonpositive_h,'scale_candidates':scale,'graph_sha256':'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806','scope':'Noncompact bounded m=R carrier and first-norm scale screen only; not full zeros or compact44.',},sort_keys=True))
