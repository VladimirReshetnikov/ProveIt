"""Owned transcription of inspected Lean symbolic definitions; no downloaded code runs.
Counts are empirical checks, not Lean-kernel certificates. BoxLemmas remain assumptions.
"""
from pathlib import Path
import sys,json,collections,hashlib,time,zlib
D=Path(__file__).parent;R=D
from check_decoder import table
from types import SimpleNamespace
def inc(pc):
 n=len(pc);v=(int(pc,2)if pc else 0)+1
 return (format(v%(2**n),'0'+str(n)+'b')if n else ''),int(v==2**n)
def strip(pc,bit,count):
 if count==0:return pc
 for i in range(len(pc)-1,-1,-1):
  if pc[i]==bit:
   count-=1
   if count==0:return pc[:i]
 return ''
I=SimpleNamespace(table=table,inc=inc,strip=strip,PHY=(6,2,0,4,3,7,8,5,1))
B=lambda b:('b',int(b))
U=lambda b,a,c:('r',int(b),a,c)
X=lambda kind='none',r=0:('x',kind,r)
SK=[51,36,25,48,32,33,22,55,60]
def norm(seq,left=False):
 out=[]
 for t in seq:
  if t[0]=='b':t=U(t[1],0,1)
  if t[0]=='r' and t[2:]==(0,0):continue
  if out and t[0]=='r' and out[-1][0:2]==t[0:2]:
   b=out.pop();t=U(t[1],t[2]+b[2],t[3]+b[3])
  out.append(t)
 if left and out and out[-1][0:2]==('r',0):out.pop()
 return tuple(out)
def key(s):q,on,l,r=s;return q,on,norm(l,True),norm(r)
def step(T,br,s):
 q,on,l,r=s;l=list(l);r=list(r)
 if on:
  if not l:return (q,False,(),(B(0),)+tuple(r)),False,'reorient'
  a=l.pop(0)
  if a[0]=='b':return (q,False,tuple(l),(a,)+tuple(r)),False,'reorient'
  assert a[0]=='r'
  _,b,c,n=a;w,d,z=T[q,b]
  if d==-1 and z==q:return (q,True,tuple(l),(U(w,c,n),)+tuple(r)),False,'scan'
  assert n>0 or c==0
  return (q,True,((B(b),U(b,c,n-1)) if n else ())+tuple(l),tuple(r)),False,'peel'
 assert r
 a=r.pop(0)
 if a[0]=='b':
  w,d,z=T[q,a[1]]
  return ((z,False,(B(w),)+tuple(l),tuple(r)) if d==1 else (z,True,tuple(l),(B(w),)+tuple(r))),True,'literal'
 if a[0]=='r':
  _,b,c,n=a;w,d,z=T[q,b]
  if d==1 and z==q:return (q,False,(U(w,c,n),)+tuple(l),tuple(r)),False,'scan'
  assert n>0 or c==0
  return (q,False,tuple(l),((B(b),U(b,c,n-1)) if n else ())+tuple(r)),False,'peel'
 assert not r
 _,kind,i=a;ans=None
 if kind=='none' and q in SK:
  j=SK.index(q);ans=(1 if j==0 else 3,X('mark',j),False)
 elif kind=='mark' and i<9:
  if q==64:ans=(40,X('inc',i),False)
  elif q==0 and br is not None and br[0]==i:ans=(97,X(),False) if br[1] else (40,X('dec',i),True)
 if ans:
  z,x,e=ans;return (z,True,((B(1),) if e else ())+tuple(l),(x,)),False,'oracle'
 assert T[q,0][0:2]==(0,-1)
 return (T[q,0][2],True,tuple(l),(a,)),True,'boxedge'
def run(T,site,pos):
 pc,op,arg=site;br=None;effect=X();delta=ov=0
 if op=='CI':succ,ov=I.inc(pc);effect=X('inc',I.PHY[arg])
 elif op=='CD' and pos:succ,ov=I.inc(pc);effect=X('dec',I.PHY[arg]);delta=1;br=(I.PHY[arg],False)
 elif op in('CD','CB'):
  succ,ov=I.inc(I.strip(pc,'0',arg if op=='CB' else 1));br=(I.PHY[arg],True) if op=='CD' else None
 elif op=='CC':succ=I.strip(pc,'1',arg)
 else:succ=''
 s=(84,False,(B(1),),tuple(map(lambda b:B(int(b)),pc))+(U(0,1,64-len(pc)),B(1),X()))
 e=(84,False,(B(1),),tuple(map(lambda b:B(int(b)),succ))+(U(0,1,64+delta+ov-len(succ)),B(1),effect));ek=key(e)
 moved=False;trace=[];states=[];target_calls=norm_calls=0
 for n in range(4000):
  if moved:
   target_calls+=1
   if s[0]==84 and s[1]==False:norm_calls+=1
   if (op=='CH' and s[0]==254) or (op!='CH' and s[0]==84 and not s[1] and key(s)==ek):return trace,states,target_calls,norm_calls
  states.append((br,s))
  ns,m,kind=step(T,br,s);trace.append((kind,s[0],s[1],ns[0],ns[1]));s=ns;moved|=m
 raise AssertionError('cap')
def main(name,tp,sp):
 T=I.table(R/tp);sites=json.load(open(R/sp));counts=collections.Counter();records=[];suffix={};prefix={};unique_states=set();fail=[];beg=time.time()
 for i,site in enumerate(sites):
  if i%500==0:print(name,i,len(unique_states),flush=True)
  for pos in ([False,True]if site[1]=='CD'else[False]):
   try:tr,states,c,n=run(T,site,pos)
   except Exception as e:fail.append([i,site,pos,repr(e)]);continue
   counts.update(guards=1,steps=len(tr),target_calls=c,normalization_calls=n)
   for st in states:unique_states.add(zlib.compress(repr(st).encode(),1))
   tail=0
   for ev in reversed(tr):tail=suffix.setdefault((ev,tail),len(suffix)+1)
   head=0
   for ev in tr:head=prefix.setdefault((head,ev),len(prefix)+1)
   records.append(dict(index=i,site=site,positive=pos,steps=len(tr),trace_id=tail))
 out=dict(name=name,counts=dict(counts),unique_full_symbolic_states=len(unique_states),event_suffix_dag_nodes=len(suffix),event_prefix_dag_nodes=len(prefix),unique_complete_event_traces=len({r['trace_id']for r in records}),failures=fail,seconds=time.time()-beg,table_sha256=hashlib.sha256((R/tp).read_bytes()).hexdigest(),source_sha256=hashlib.sha256((R/sp).read_bytes()).hexdigest(),scope='Owned transcription of Lean sstep with BoxLemmas assumed; counts are not kernel certificates. Event sharing alone does not justify reusing a contextual theorem.')
 (D/(name+'.json')).write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main(*sys.argv[1:])
