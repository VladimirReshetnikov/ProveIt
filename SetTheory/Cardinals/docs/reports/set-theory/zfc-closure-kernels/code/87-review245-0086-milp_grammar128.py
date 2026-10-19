"""Independent mixed-integer bounded grammar search; input files are data only."""
import search_grammar as s
import collections,sys,time,json
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_array
start=time.monotonic();maxlen=int(sys.argv[1]) if len(sys.argv)>1 else 80;secs=float(sys.argv[2])if len(sys.argv)>2 else 180
main=max(s.ROOTS,key=len);freq=collections.Counter(main[i:j]for i in range(len(main))for j in range(i+2,min(len(main),i+maxlen)+1))
words=set(s.R)|set(s.OLD)|set(s.ATOM)|{w for w,n in freq.items()if n>1};words=sorted(words,key=lambda w:(len(w),w));locked={w:(s.R[w]) for w,_,_ in s.locks}
routecons=collections.defaultdict(list)
for q,b,bits,t in s.CON:routecons[s.ROUTES[q,b]].append((bits,t))
prod=[];byword=collections.defaultdict(list);bypair={}
for w in words:
 if len(w)==1:continue
 for k in range(1,len(w)):
  a,b=w[:k],w[k:]
  if a not in words or b not in words:continue
  if w in locked and (a,b)!=locked[w]:continue
  if len(a)==1 and not(s.ALLOWED[a]&1):continue
  if len(b)==1 and not(s.ALLOWED[b]&2):continue
  ok=True
  for bits,t in routecons[w]:
   child=(a,b)[int(bits[0])]
   if len(bits)==1:ok &= child==t
   elif bits[1]=='0':ok &= child.startswith(t) and len(child)>len(t)
   else:ok &= child.endswith(t) and len(child)>len(t)
  if not ok:continue
  z=len(prod);prod.append((w,a,b));byword[w].append(z);bypair[w,a,b]=z
P=len(prod);print('model',len(words),'words',P,'productions',flush=True)
# Fixed AST templates between closed sequence roots. All reached word roots must remain defined.
needed=set();ws=set()
def visit(i):
 if i in needed:return
 needed.add(i);z=s.AST[i]
 if z[0]=='W':ws.add(z[1])
 elif z[0]=='N':visit(int(z[1]));visit(int(z[2]))
for i in s.ATOM.values():visit(i)
visit(s.root)
N=P;L={};D={};LA={};DA={}
for w in words:L[w]=N;N+=1
for i in sorted(needed):LA[i]=N;N+=1
for w in words:D[w]=N;N+=1
for i in sorted(needed):DA[i]=N;N+=1
low=np.zeros(N);high=np.ones(N);high[P:]=6
for v in list(D.values())+list(DA.values()):high[v]=64
obj=np.zeros(N);obj[:P]=1;integer=np.zeros(N);integer[:P]=1
rows=[];cols=[];vals=[];lo=[];hi=[]
def constraint(ts,l=-np.inf,h=np.inf):
 r=len(lo)
 for c,v in ts:rows.append(r);cols.append(c);vals.append(v)
 lo.append(l);hi.append(h)
for w,zs in byword.items():constraint([(z,1)for z in zs],1 if w in s.ROOTS|ws else 0,1)
for w in s.ROOTS|ws:assert byword[w],w
for z,(w,a,b) in enumerate(prod):
 for c in [a,b]:
  if len(c)>1:constraint([(z,1)]+[(v,-1)for v in byword[c]],h=0)
 constraint([(L[w],1),(L[a],-1),(z,7)],h=8)
 constraint([(L[w],1),(L[a],-1),(z,-7)],l=-6)
 for c in [a,b]:constraint([(D[w],1),(D[c],-1),(z,-65)],l=-64)
 for bits,t in routecons[w]:
  if len(bits)==1:continue
  child=(a,b)[int(bits[0])]
  ca,cb=(t,child[len(t):])if bits[1]=='0'else(child[:-len(t)],t)
  q=bypair.get((child,ca,cb))
  if q is None:high[z]=0
  else:constraint([(z,1),(q,-1)],h=0)
for i in sorted(needed):
 z=s.AST[i]
 if z[0]=='L':high[LA[i]]=high[DA[i]]=0
 elif z[0]=='W':
  constraint([(LA[i],1),(L[z[1]],-1)],0,0)
  constraint([(DA[i],1),(D[z[1]],-1)],0,0)
 else:
  a,b=map(int,z[1:]);constraint([(LA[i],1),(LA[a],-1)],1,1)
  constraint([(DA[i],1),(DA[a],-1)],l=1);constraint([(DA[i],1),(DA[b],-1)],l=1)
for a,i in s.ATOM.items():constraint([(L[a],1),(LA[i],-1)],0,0);constraint([(D[a],1),(DA[i],-1)],0,0)
constraint([(z,1)for z in range(P)],h=128)
A=coo_array((np.array(vals,float),(np.array(rows,np.int32),np.array(cols,np.int32))),shape=(len(lo),N)).tocsc()
print('constraints',len(lo),'variables',N,'build_seconds',time.monotonic()-start,flush=True)
res=milp(obj,integrality=integer,bounds=Bounds(low,high),constraints=LinearConstraint(A,np.array(lo),np.array(hi)),options={'time_limit':secs,'presolve':True,'disp':True,'mip_rel_gap':0})
print('RESULT',res,flush=True)
report={'status':int(res.status),'message':res.message,'mip_node_count':getattr(res,'mip_node_count',None),'mip_dual_bound':getattr(res,'mip_dual_bound',None),'fun':res.fun,'word_count':len(words),'productions':P,'constraints':len(lo),'variables':N,'maximum_repeated_substring_length':maxlen,'seconds':time.monotonic()-start}
if res.x is not None:
 rr={w:(a,b)for z,(w,a,b)in enumerate(prod)if res.x[z]>0.5};print('candidate',len(rr),'props',s.validate(rr),flush=True);s.save(rr,f'milp-{maxlen}-{len(rr)}');report['candidate_rules']=len(rr)
(s.OUT/f'milp-{maxlen}-result.json').write_text(json.dumps(report,indent=2)+'\n')
