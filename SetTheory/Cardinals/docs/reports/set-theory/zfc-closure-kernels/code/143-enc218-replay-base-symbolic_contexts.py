#!/usr/bin/env python3
"""New standalone symbolic context auditor; imports only standard library.
Tokens denote affine unary runs and an arbitrary finite tail of register blocks.
Every acceleration is justified by a literal self-loop or checked block schema.
"""
import argparse,collections,hashlib,json,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
N=13;ZERO=(0,)*N

def add(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def constant(n):return (n,)+(0,)*(N-1)
def variable(n):return tuple(int(i==n) for i in range(N))
def subone(a):return (a[0]-1,)+a[1:]
def atom(b,n=1):return ('r',b,constant(n) if isinstance(n,int) else n)
B=('blank',)
def block(n,fam='B'):
 return [atom(0),atom(1,add(n,constant(1)))] if fam=='B' else [atom(1),atom(0),atom(1,n)]
def reverse(xs):return [('l',a[1],not a[2]) if a[0]=='l' else a for a in xs[::-1]]
def norm(xs):
 out=[]
 for a in xs:
  if a[0]=='r':
   assert all(v>=0 for v in a[2])
   if a[2]==ZERO:continue
   if out and out[-1][:2]==a[:2]:a=atom(a[1],add(out.pop()[2],a[2]))
  out.append(a)
 if len(out)>1 and out[-1]==B and out[-2][:2]==('r',0):out.pop(-2)
 # For every finite listV: C(V)1 = 1B(V), by cons induction.
 for i in range(len(out)-1):
  a,b=out[i:i+2]
  if a==('l','C',False) and b[:2]==('r',1) and b[2][0]>0:
   return norm(out[:i]+[atom(1),('l','B',False),atom(1,subone(b[2]))]+out[i+2:])
  if a[:2]==('r',1) and a[2][0]>0 and b==('l','C',True):
   return norm(out[:i]+[atom(1,subone(a[2])),('l','B',True),atom(1)]+out[i+2:])
 return out
class Tape:
 def __init__(self,q,left,right,d=1):self.q=q;self.L=left;self.R=right;self.d=d;self.time=ZERO;self.motion=ZERO
 def key(self):
  self.L=norm(self.L);self.R=norm(self.R)
  return self.q,self.d,self.L,self.R
 def advance(self,tm,schemata):
  self.key();src,dst=(self.R,self.L) if self.d==1 else (self.L,self.R)
  if src[0]==B:src.insert(0,atom(0))
  a=src[0]
  if a[0]=='l':
   key=self.q,self.d,a[1],a[2];assert key in schemata,key
   src.pop(0);dst.insert(0,('l',schemata[key],not a[2]));duration=variable(12)
   self.time=add(self.time,duration);self.motion=add(self.motion,duration if self.d==1 else neg(duration))
   return ('list',key)
  assert a[0]=='r',a
  w,d,q=tm[self.q,a[1]];row=(self.q,a[1],w,d,q)
  if q==self.q and d==self.d:
   src.pop(0);dst.insert(0,atom(w,a[2]));duration=a[2];event=('scan',row,duration)
  else:
   assert a[2][0]>0,('potentially empty first run',row,a)
   src[0]=atom(a[1],subone(a[2]));duration=constant(1)
   if d==self.d:dst.insert(0,atom(w))
   else:src.insert(0,atom(w));self.d=d
   self.q=q;event=('step',row)
  self.time=add(self.time,duration);self.motion=add(self.motion,duration if d==1 else neg(duration))
  return event

def readtm(path):
 tm={}
 for line in path.read_text().splitlines():
  line=line.split('#')[0].strip()
  if line:
   q,b,w,d,n=line.split();tm[int(q),int(b)]=int(w),1 if d=='R' else -1,int(n)
 return tm

def prove_schemata(tm):
 ans={};reports=[]
 for q,d,before,after in [(64,1,'B','B'),(0,1,'B','C'),(40,-1,'B','B'),(97,-1,'C','B')]:
  v=variable(2);left=('opaque','left');right=('opaque','right')
  if d==1:
   t=Tape(q,[left],block(v,before)+[right]);goal=Tape(q,reverse(block(v,after))+[left],[right])
  else:
   t=Tape(q,reverse(block(v,before))+[left],[right],-1);goal=Tape(q,[left],block(v,after)+[right],-1)
  k=goal.key();trace=[]
  for _ in range(20):
   if t.key()==k:break
   trace.append(t.advance(tm,{}))
  else:raise ValueError('block did not close')
  assert t.time==add(v,constant(2))
  assert t.motion==(t.time if d==1 else neg(t.time))
  ans[q,d,before,d==-1]=after;reports.append([q,d,before,after,trace])
 return ans,reports

PHY=[6,2,0,4,3,7,8,5,1]
def fileword(values,extra=False):
 out=[]
 for v in values:out+=block(v)
 out+=block(variable(11))+[('l','B',False)]
 if extra:out+=block(constant(1))
 return out+[B]
def code_inc(pc):
 if not pc:return '',1
 n=int(pc,2)+1
 return format(n%(1<<len(pc)),'0%db'%len(pc)),int(n==(1<<len(pc)))
def code_strip(pc,bit,n):
 for i in range(len(pc)-1,-1,-1):
  if pc[i]==bit:
   n-=1
   if n==0:return pc[:i]
 return ''
def case(tm,schemata,site,pos,contexts):
 pc,op,arg=site;values=[variable(i+2) for i in range(9)]
 if op=='CD':values[arg]=add(constant(1),values[arg]) if pos else ZERO
 physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=values[i]
 result=physical.copy();extra=False;delta=overflow=0
 if op=='CI':result[PHY[arg]]=add(result[PHY[arg]],constant(1));nxt,overflow=code_inc(pc);extra=True
 elif op=='CD' and pos:result[PHY[arg]]=subone(result[PHY[arg]]);nxt,overflow=code_inc(pc);delta=1
 elif op in ['CD','CB']:nxt,overflow=code_inc(code_strip(pc,'0',1 if op=='CD' else arg))
 elif op=='CC':nxt=code_strip(pc,'1',arg)
 elif op=='CH':nxt=''
 else:raise ValueError(op)
 t=Tape(84,[atom(1),B],[atom(int(b)) for b in pc]+[atom(0,add(variable(1),constant(64-len(pc)))),atom(1)]+fileword(physical))
 target=Tape(84,[atom(1),B],[atom(int(b)) for b in nxt]+[atom(0,add(variable(1),constant(64+delta+overflow-len(nxt)))),atom(1)]+fileword(result,extra));goal=target.key()
 count=0;hits=collections.Counter();previous=None
 while count<4000:
  key=t.key()
  if count and ((op=='CH' and t.q==254) or (op!='CH' and key==goal)):
   assert t.time[0]>0 and all(a>=0 for a in t.time)
   if op!='CH':assert t.motion==constant(-overflow)
   return count,hits
  if t.q in {103,113,198,302}:
   # Keep enough symbolic word around the exact cursor for return synthesis.
   snapshot=(t.q,t.d,json.dumps([t.L[:8],t.R[:8]],separators=(',',':')))
   rec=contexts.setdefault(snapshot,{'count':0,'examples':[],'previous':set(),'operations':collections.Counter()})
   rec['count']+=1;rec['previous'].add(previous);rec['operations'][op]+=1
   if len(rec['examples'])<3:rec['examples'].append([pc,op,arg,pos])
   hits[t.q]+=1
  event=t.advance(tm,schemata)
  previous=(event[1][0],event[1][1]) if event[0]!='list' else ('list',event[1][0])
  count+=1
 raise ValueError(('case limit',site,pos,t.key()))

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);args=ap.parse_args()
 path=ROOT/'latest219_baseline/candidate-k219';tm=readtm(path/'k219.native.tm');sites=json.loads((path/'sites219.json').read_text())
 schemas,proofs=prove_schemata(tm);contexts={};cases=0;rules=0;hits=collections.Counter();start=time.monotonic()
 for i,site in enumerate(sites):
  for pos in [False,True] if site[1]=='CD' else [False]:
   n,h=case(tm,schemas,site,pos,contexts);rules+=n;cases+=1;hits.update(h)
   if cases%500==0:print(cases,round(time.monotonic()-start,2),flush=True)
   if args.limit and cases>=args.limit:break
  if args.limit and cases>=args.limit:break
 rows=[]
 for (q,d,words),rec in contexts.items():
  rec['previous']=sorted(rec['previous'],key=str);rec['operations']=dict(rec['operations'])
  rows.append({'state':q,'direction':d,'left_right_tokens':json.loads(words),**rec})
 report={'status':'ALL_PRIMITIVE_INTERFACES_PASS' if cases==6167 else 'PARTIAL_PASS','cases':cases,'symbolic_rules':rules,'seconds':time.monotonic()-start,'context_count':len(rows),'state_visit_groups':dict(hits),'scope':'Independent arbitrary natural registers,gap,firstspare,and finite sparetail; spareone append; complete frame return and positive duration. Mathematical symbolic check,not proofassistant.','block_schema_proofs':proofs,'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((path/'sites219.json').read_bytes()).hexdigest(),'native_sha256':hashlib.sha256((path/'k219.native.tm').read_bytes()).hexdigest()}
 (OUT/'SYMBOLIC_CONTEXT_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n');(OUT/'SYMBOLIC_CONTEXTS.json').write_text(json.dumps(rows,indent=2)+'\n')
 print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
