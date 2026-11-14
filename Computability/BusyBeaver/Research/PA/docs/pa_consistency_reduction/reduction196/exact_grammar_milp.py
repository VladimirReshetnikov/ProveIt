"""Exact minimum binary SLP via n-ary rule partition flows on repeated strings."""
from pathlib import Path
import sys,time,json,collections,numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
sys.path[:0]=[str(Path(__file__).resolve().parents[1]/'math_reduction/grammar')]
import search_grammar as SG

def solve(word,seconds=180,upper=68,out='exact_grammar',free_double=False,feasible=False,zero_bound=None):
 start=time.time();word=tuple(word);ss=collections.defaultdict(list)
 for i in range(len(word)):
  for j in range(i+2,len(word)+1):ss[word[i:j]].append(i)
 strings=sorted([s for s,ps in ss.items()if len(ps)>1],key=lambda q:(len(q),q))+[word]
 idx={s:i for i,s in enumerate(strings)};N=len(strings);arcs=[]
 for si,s in enumerate(strings):
  for i in range(len(s)):
   for j in range(i+1,len(s)+1):
    if i==0 and j==len(s):continue
    z=s[i:j]
    if len(z)==1 or z in idx:arcs.append((si,i,j,None if len(z)==1 else idx[z]))
 n=N+len(arcs);cost=np.array([-1.0]*N+[1.0]*len(arcs))
 if free_double and ('i','i')in idx:cost[idx['i','i']]=-2.0
 rows=[];cols=[];vals=[];low=[];high=[]
 flowindex={}
 for si,s in enumerate(strings):
  for pos in range(len(s)+1):
   r=len(low);low.append(0.0);high.append(0.0);flowindex[si,pos]=r
   if pos==0:rows.append(r);cols.append(si);vals.append(-1.0)
   if pos==len(s):rows.append(r);cols.append(si);vals.append(1.0)
 for k,(si,i,j,child)in enumerate(arcs):
  y=N+k
  rows.extend([flowindex[si,i],flowindex[si,j]]);cols.extend([y,y]);vals.extend([1.0,-1.0])
  if child is not None:
   r=len(low);low.append(-np.inf);high.append(0.0)
   rows.extend([r,r]);cols.extend([y,child]);vals.extend([1.0,-1.0])
 r=len(low);low.append(-np.inf);high.append(float(upper))
 for k,v in enumerate(cost):rows.append(r);cols.append(k);vals.append(v)
 if zero_bound is not None:
  sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
  import optimize_bounded as B
  levelbase=n;n+=N;cost=np.r_[cost,np.zeros(N)];big=zero_bound+1
  for k,(si,i,j,child)in enumerate(arcs):
   y=N+k
   if i==0:
    r=len(low);low.append(-np.inf)
    rows.extend([r,r]);cols.extend([y,levelbase+si]);vals.extend([float(big),-1.0])
    if child is not None:
     rows.append(r);cols.append(levelbase+child);vals.append(1.0);high.append(float(big-1))
    else:high.append(float(big-1-B.LEADING[strings[si][i]]))
   if j<len(strings[si])and child is not None:
    r=len(low);low.append(-np.inf);high.append(float(big+zero_bound-1))
    rows.extend([r,r]);cols.extend([y,levelbase+child]);vals.extend([float(big),1.0])
 mat=coo_matrix((vals,(rows,cols)),shape=(len(low),n)).tocsc()
 lb=np.zeros(n);ub=np.ones(n);lb[N-1]=1
 if zero_bound is not None:ub[levelbase:]=zero_bound
 print('MODEL',N,'phrases',len(arcs),'arcs',len(low),'constraints','nonzeros',len(vals),flush=True)
 result=milp(np.zeros(n)if feasible else cost,integrality=np.ones(n),bounds=Bounds(lb,ub),constraints=LinearConstraint(mat,low,high),options={'time_limit':seconds,'mip_rel_gap':0.0,'disp':True})
 print('RESULT',result.message,'cost',float(cost@result.x)if result.x is not None else None,'bound',getattr(result,'mip_dual_bound',None),'seconds',time.time()-start,flush=True)
 if result.x is None:return
 rules={};chosen=result.x>.5
 for si,s in enumerate(strings):
  if not chosen[si]:continue
  outgoing={i:(j,child)for k,(q,i,j,child)in enumerate(arcs)if q==si and chosen[N+k]}
  pieces=[];p=0
  while p<len(s):
   j,ch=outgoing[p];pieces.append(s[p]if ch is None else f'n{ch}');p=j
  rules[f'n{si}']=pieces
 data={'cost':int(round(cost@result.x)),'feasibility_only':feasible,'zero_bound':zero_bound,'dual_bound':float(result.mip_dual_bound),'root':f'n{N-1}','rules':rules,'word':list(word),'tokens':SG.TOKENS,'seconds':time.time()-start}
 Path(__file__).with_name(out+'.json').write_text(json.dumps(data,indent=2))

if __name__=='__main__':solve(SG.WORD,int(sys.argv[1])if len(sys.argv)>1 else 180,int(sys.argv[2])if len(sys.argv)>2 else 68)
