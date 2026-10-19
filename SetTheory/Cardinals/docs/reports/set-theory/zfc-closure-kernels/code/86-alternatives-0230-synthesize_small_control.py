"""Synthesize seven free scanner states, with fixed existing helpers.
A SAT model is only a discovery certificate until independent literal replay,
all instruction contracts, and a fresh blank initialization pass.
"""
import argparse,itertools,json,time,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
from pysat.formula import IDPool,CNF
from pysat.solvers import Solver
p=argparse.ArgumentParser();p.add_argument('--threshold',type=int,default=8);p.add_argument('--states',type=int,default=7);p.add_argument('--steps',type=int,default=24);p.add_argument('--solver',default='cadical300');p.add_argument('--helpers',default='4');p.add_argument('--borrow-right',type=int,default=0);p.add_argument('--borrow-left',type=int,default=0);p.add_argument('--prefix',type=int,default=0);p.add_argument('--output',required=True);p.add_argument('--write-cnf');a=p.parse_args()
assert 1<=a.states<=8 and 0<=a.borrow_left<=1 and 0<=a.borrow_right<=2
n=a.states;labels=[6,9,13,19,29,41,58,74][:n];helpers=list(map(int,a.helpers.split(',')));assert 4 in helpers and len(set(helpers))==len(helpers) and not(set(helpers)&set(labels))
labels+=helpers;L=len(labels);QCOUNT=L+1;ACTIVE=list(range(L));mapping={old:new for new,old in enumerate(labels)}|{84:L};S=mapping[4]
table={}
for line in (ROOT/'recovered/63/machine/zfc_prefix246_old.tm').read_text().splitlines():
 if line.startswith('#'):continue
 q,b,w,d,s=line.split();table[int(q),int(b)]=(int(w),d,int(s))
ids=IDPool();cnf=CNF()
def v(*key):return ids.id(key)
def add(*lits):cnf.append(list(lits))
def exactly(xs):
 add(*xs)
 for x,y in itertools.combinations(xs,2):add(-x,-y)
def eq_if(conds,x,y):
 add(*[-c for c in conds],-x,y);add(*[-c for c in conds],x,-y)
for q in ACTIVE:
 for b in (0,1):
  exactly([v('N',q,b,r)for r in range(QCOUNT)])
  if q<n:
   for r in range(2,n):add(-v('N',q,b,r),*[v('N',j//2,j%2,r-1)for j in range(2*q+b)])
  else:
   w,d,t=table[labels[q],b];assert t in mapping,(labels[q],b,t)
   add(v('W',q,b)if w else-v('W',q,b));add(v('D',q,b)if d=='R'else-v('D',q,b));add(v('N',q,b,mapping[t]))
# Preserve the selector-induction support at old6/read1.
add(v('W',0,1));add(-v('D',0,1));add(v('N',0,1,S))
for q in range(a.prefix):
 add(-v('W',q,0));add(-v('D',q,0));add(v('N',q,0,q+1));add(v('W',q,1));add(-v('D',q,1));add(v('N',q,1,S))
cases=[]
for k in range(a.threshold+1):
 lo=(-k if k<a.threshold else-(a.threshold-1))-a.borrow_left;hi=2+a.borrow_right
 unknown=list(range(3,hi+1))+(list(range(-k-a.borrow_left,-k))if k<a.threshold else[])
 for bits in itertools.product((0,1),repeat=len(unknown)):
  ones={2}|({-k}if k<a.threshold else set())|{j for j,b in zip(unknown,bits)if b}
  cases.append({'k':k,'lo':lo,'hi':hi,'ones':sorted(ones),'unknown':unknown,'assignment':list(bits)})
for c,case in enumerate(cases):
 k=case['k'];lo=case['lo'];hi=case['hi'];ones=set(case['ones']);poss=list(range(lo-1,hi+2));cells=list(range(lo,hi+1));terminal=S if k<a.threshold else L
 for t in range(a.steps+1):
  end=v(c,t,'END');exactly([v(c,t,'Q',q)for q in range(QCOUNT)]);exactly([v(c,t,'H',j)for j in poss])
  if k<a.threshold:
   add(-v(c,t,'Q',L));add(-end,v(c,t,'Q',S));add(-end,v(c,t,'H',-k-1));add(-v(c,t,'Q',S),-v(c,t,'H',-k-1),end)
  else:eq_if([],end,v(c,t,'Q',L))
  for j in [lo-1,hi+1]:add(-v(c,t,'H',j),end)
  for j in poss:
   if abs(j)>t:add(-v(c,t,'H',j))
   elif (j-t)%2:add(-v(c,t,'H',j),end)
 add(v(c,0,'Q',0));add(v(c,0,'H',0))
 for j in cells:
  add(v(c,0,'B',j)if j in ones else-v(c,0,'B',j));add(v(c,a.steps,'B',j)if j in ones else-v(c,a.steps,'B',j))
 add(v(c,a.steps,'END'))
 if k==a.threshold:add(*[v(c,a.steps,'H',j)for j in range(-a.threshold,2)])
 for t in range(a.steps):
  end=v(c,t,'END');r=v(c,t,'R');w=v(c,t,'W');d=v(c,t,'D')
  add(-end,v(c,t+1,'Q',terminal))
  for j in poss:eq_if([end],v(c,t,'H',j),v(c,t+1,'H',j))
  for j in cells:
   h=v(c,t,'H',j);bt=v(c,t,'B',j);bn=v(c,t+1,'B',j)
   eq_if([h],r,bt);eq_if([h,-end],w,bn);eq_if([-h],bt,bn);eq_if([end],bt,bn)
   add(end,-h,-d,v(c,t+1,'H',j+1));add(end,-h,d,v(c,t+1,'H',j-1))
  for q in ACTIVE:
   for b in (0,1):
    cond=[v(c,t,'Q',q),r if b else-r,-end];eq_if(cond,w,v('W',q,b));eq_if(cond,d,v('D',q,b))
    for dest in range(QCOUNT):add(*[-x for x in cond],-v('N',q,b,dest),v(c,t+1,'Q',dest))
print('CNF',ids.top,len(cnf.clauses),'cases',len(cases),'solve',a.solver,flush=True)
if a.write_cnf:cnf.to_file(a.write_cnf)
t0=time.monotonic()
with Solver(name=a.solver,bootstrap_with=cnf)as sol:
 answer=sol.solve();out={'sat':answer,'states':n,'steps':a.steps,'solver':a.solver,'seconds':time.monotonic()-t0,'clauses':len(cnf.clauses),'variables':ids.top,'options':vars(a),'stats':sol.accum_stats() if a.solver!='kissat404' else None,'labels':labels+[84],'cases':cases}
 if answer:
  m=set(sol.get_model());out['table']=[[q,b,int(v('W',q,b)in m),'R'if v('D',q,b)in m else'L',next(r for r in range(QCOUNT)if v('N',q,b,r)in m)]for q in ACTIVE for b in(0,1)]
pathlib.Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='cases'},indent=2),flush=True)
