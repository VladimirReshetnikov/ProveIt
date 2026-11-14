from pathlib import Path
import json,sys,itertools,time
from functools import lru_cache
from collections import defaultdict
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'support'))
import compiler as c,symbolic_runtime as sr,build194 as b,source_language as s
K=5
@lru_cache(maxsize=100000)
def boxpref(kind,r,k,reg=0):
 if not k:return ((),)
 if reg>=10:return tuple(itertools.product((0,1),repeat=k))
 out=set()
 for v in range(k+1):
  block=(0,0)+(1,)*v if kind=='mark' and reg==r else (0,)+(1,)*(v+1)
  if len(block)>=k:out.add(block[:k])
  else:
   for p in boxpref(kind,r,k-len(block),reg+1):out.add(block+p)
 return tuple(out)
@lru_cache(maxsize=200000)
def prefixes(seg,k):
 if k==0:return ((),)
 if not seg:return ((0,)*k,)
 x,*tail=seg;tail=tuple(tail)
 if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
 if x[0]=='x':
  assert not tail
  return boxpref(x[1],x[2],k)
 if x[0]=='r':
  _,bit,a,d=x;assert a>=0 and d>=0
  if a==0:
   if d>=k:return ((bit,)*k,)
   return tuple((bit,)*d+p for p in prefixes(tail,k-d))
  ans=set()
  for n in range(k+1):
   leng=a*n+d
   if leng>=k:ans.add((bit,)*k);break
   for p in prefixes(tail,k-leng):ans.add((bit,)*leng+p)
  return tuple(ans)
 raise ValueError(x)

def process(path):
 sites=json.loads((path/'sites.json').read_text());graph=s.graph_intervals(sites);assert graph==s.graph_arithmetic(sites)[0]
 rows={}
 for l in (path/'machine.native.tm').read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,r,w,d,n=l.split();rows[int(q),int(r)]=(int(w),d=='R',int(n))
 frozen_box=json.loads((HERE/'inputs/arithmetic_box_rows.json').read_text())
 assert all(rows[q,bit]==tuple(action) for q,bit,action in frozen_box), 'Arithmetic box rows changed'
 cs=[]
 for i,((pat,op,arg),(eff,ts)) in enumerate(zip(sites,graph)):
  p=tuple(map(int,pat));st=c.frame(p)
  f=lambda j,extra=0,effect=c.PLAIN:c.canonical(c.frame(tuple(map(int,sites[j][0])),extra,effect))
  if eff[0]=='increment':cs.append((i,None,st,f(ts[0],0,('x','inc',c.PHYSICAL[arg]))))
  elif eff[0]=='decrement':
   cs.append((i,(c.PHYSICAL[arg],True),st,f(ts[0])))
   cs.append((i,(c.PHYSICAL[arg],False),st,f(ts[1],1,('x','dec',c.PHYSICAL[arg]))))
  elif eff[0]=='identity':cs.append((i,None,st,f(ts[0])))
  else:cs.append((i,None,st,None))
 patterns=defaultdict(set);seen=set();observations=0
 def observe(st,interiors=True):
  nonlocal observations
  q,onl,l,r=st
  if q in c.BOXSTATES:return
  if interiors:
   seg=l if onl else r
   if seg and seg[0][0]=='r':
    x=seg[0];act=rows.get((q,x[1]))
    if act and act[1]!=(onl) and act[2]==q:
     if onl:observe((q,True,(('r',x[1],1,0),)+l[1:],(('r',act[0],1,0),)+r),False)
     else:observe((q,False,(('r',act[0],1,0),)+l,(('r',x[1],1,0),)+r[1:]),False)
  lp=prefixes(l,K+1 if onl else K);rp=prefixes(r,K if onl else K+1)
  key=(q,onl,lp,rp)
  if key in seen:return
  seen.add(key);observations+=1
  for aa,bb in itertools.product(lp,rp):
   tape=tuple(reversed(aa[1:]))+(aa[0],)+bb if onl else tuple(reversed(aa))+bb
   assert len(tape)==2*K+1
   patterns[q].add(sum(v<<j for j,v in enumerate(tape)))

 valid=c.validate(rows,cs,observe=observe)
 out=OUTPUT/path.name;out.mkdir(parents=True,exist_ok=True)
 rec={'name':path.name,'radius':K,'validation':valid,'observations':observations,'source_outcomes':len(cs),'arithmetic_box_rows_unchanged':True,'self_loop_interiors_included':True,'register_file_prefixes':'superset of sepsR/sepsM for at least10 registers'}
 if valid['ok']:
  try:seed=b.startup(rows,tuple(map(int,sites[25][0])));rec['startup']=seed
  except Exception as e:rec['startup_error']=str(e);print('STARTFAIL',path.name,str(e),flush=True);seed=None
  if seed:
   tape=set();head=0;q=74
   for step in range(seed['steps']):
    if q not in c.BOXSTATES:patterns[q].add(sum(int(head+i-K in tape)<<i for i in range(2*K+1)))
    w,d,q=rows[q,int(head in tape)];(tape.add if w else tape.discard)(head);head+=1 if d else -1
   ids={74:0};order=[74]
   for q in order:
    for bit in (0,1):
     n=rows[q,bit][2]
     if (n,0)in rows and n not in ids:ids[n]=len(ids);order.append(n)
   (out/'patterns.txt').write_text(''.join(f'{ids[q]} {p}\n'for q in sorted(patterns)for p in sorted(patterns[q])))
   (out/'labels.json').write_text(json.dumps(order))
   rec['pattern_count']=sum(map(len,patterns.values()));rec['control_count']=len(patterns)
 (out/'receipt.json').write_text(json.dumps(rec,indent=2));print('CHECKED',path.name,valid,'patterns',rec.get('pattern_count'),flush=True)
 return rec
if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser(description='Regenerate universal-source local windows with unary-file prefixes and self-loop interiors.');ap.add_argument('--case',default='PA194');ap.add_argument('--radius',type=int,default=8);ap.add_argument('--output',type=Path,default=HERE/'generated_contexts');args=ap.parse_args()
 K=args.radius;OUTPUT=args.output
 process(HERE/'inputs/source_programs'/args.case)
