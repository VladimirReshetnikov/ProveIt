"""One-hot SAT synthesis of a tape-restoring eight-zero detector.
Known input window [-k,2] for short k=0..7, [-7,2] long; outside unread.
Terminal short=(state n,head-k-1), long=(state n+1,head in[-7,1]).
The long contract uses the existing caller invariant cell -8=0.
"""
import argparse,itertools,json,time,pathlib,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'vendor'))
from pysat.formula import IDPool,CNF
from pysat.solvers import Solver
p=argparse.ArgumentParser();p.add_argument('--states',type=int,default=7);p.add_argument('--steps',type=int,default=24);p.add_argument('--solver',default='cadical195');p.add_argument('--fix-one',action='store_true');p.add_argument('--no-write',action='store_true');p.add_argument('--first-write',type=int);p.add_argument('--output',required=True);p.add_argument('--force-baseline',action='store_true');p.add_argument('--write-cnf');a=p.parse_args()
n=a.states;S=n;L=n+1;ids=IDPool();cnf=CNF()
def v(*key):return ids.id(key)
def add(*lits):cnf.append(list(lits))
def exactly(xs):
 add(*xs)
 for x,y in itertools.combinations(xs,2):add(-x,-y)
def eq_if(conds,x,y):add(*[-c for c in conds],-x,y);add(*[-c for c in conds],x,-y)
for q in range(n):
 for b in range(2):
  exactly([v('N',q,b,r) for r in range(n+2)])
  if a.no_write:add(v('W',q,b) if b else -v('W',q,b))
  for r in range(1,n):
   # Earliest occurrence of label r must be preceded by label r-1.
   prefix=[v('N',j//2,j%2,r-1) for j in range(2*q+b)]
   if r>1:add(-v('N',q,b,r),*prefix)
  if a.force_baseline:
   assert n==8
   add(v('N',q,b,S if b else (q+1 if q<7 else L)))
   add(-v('D',q,b));add(v('W',q,b) if b else -v('W',q,b))
if a.fix_one:add(v('W',0,1));add(-v('D',0,1));add(v('N',0,1,S))
if a.first_write is not None:add(v('W',0,0) if a.first_write else -v('W',0,0))
for k in range(9):
 lo=-k if k<8 else -8
 poss=list(range(lo-1,4));cells=list(range(lo,3)); terminal=S if k<8 else L
 for t in range(a.steps+1):
  exactly([v(k,t,'Q',q) for q in range(n+2)])
  exactly([v(k,t,'H',j) for j in poss])
  add(-v(k,t,'Q',L if k<8 else S))
  for j in [lo-1,3]:
   add(-v(k,t,'H',j),v(k,t,'Q',terminal))
 for q in range(n+2):add(v(k,0,'Q',q) if q==0 else -v(k,0,'Q',q))
 for j in poss:add(v(k,0,'H',j) if j==0 else -v(k,0,'H',j))
 for j in cells:
  b=j==2 or (k<8 and j==-k)
  add(v(k,0,'B',j) if b else -v(k,0,'B',j));add(v(k,a.steps,'B',j) if b else -v(k,a.steps,'B',j))
 add(v(k,a.steps,'Q',terminal))
 if k<8:add(v(k,a.steps,'H',-k-1))
 else:
  add(*[v(k,a.steps,'H',j) for j in range(-8,2)])
 for t in range(a.steps):
  end=v(k,t,'Q',terminal);r=v(k,t,'R');w=v(k,t,'W');d=v(k,t,'D')
  add(-end,v(k,t+1,'Q',terminal))
  for j in poss:
   eq_if([end],v(k,t,'H',j),v(k,t+1,'H',j))
  for j in cells:
   h=v(k,t,'H',j);bt=v(k,t,'B',j);bn=v(k,t+1,'B',j)
   eq_if([h],r,bt)
   eq_if([h,-end],w,bn)
   eq_if([-h],bt,bn);eq_if([end],bt,bn)
   add(end,-h,-d,v(k,t+1,'H',j+1))
   add(end,-h,d,v(k,t+1,'H',j-1))
  for q in range(n):
   for b in range(2):
    cond=[v(k,t,'Q',q),r if b else -r]
    eq_if(cond,w,v('W',q,b));eq_if(cond,d,v('D',q,b))
    for dest in range(n+2):
     add(*[-c for c in cond],-v('N',q,b,dest),v(k,t+1,'Q',dest))
print('CNF',ids.top,len(cnf.clauses),'solve',a.solver,flush=True)
if a.write_cnf:cnf.to_file(a.write_cnf)
t0=time.monotonic()
with Solver(name=a.solver,bootstrap_with=cnf) as sol:
 answer=sol.solve();out={'sat':answer,'states':n,'steps':a.steps,'solver':a.solver,'seconds':time.monotonic()-t0,'clauses':len(cnf.clauses),'variables':ids.top,'options':vars(a),'stats':sol.accum_stats() if a.solver!='kissat404' else None}
 if answer:
  m=set(sol.get_model());rows=[]
  for q in range(n):
   for b in range(2):rows.append([q,b,int(v('W',q,b) in m),'R' if v('D',q,b) in m else 'L',next(r for r in range(n+2) if v('N',q,b,r) in m)])
  out['table']=rows
pathlib.Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
