#!/usr/bin/env python3
"""Independent audit of LNPQMVQPW -> LMPW at clean constructor boundaries.

Finite AST execution is a regression check. The all-natural-number theorem
is proved in negation_peephole_proof.tex. Symbolic whole-AX replay checks the
zero-scratch premise at every literal replacement and the exact final state.
"""
from pathlib import Path
from functools import cache
import hashlib,itertools,json,argparse,random
HERE=Path(__file__).resolve().parent
PATTERN='LNPQMVQPW';REPLACEMENT='LMPW'
TOKENS=json.loads((HERE/'negation_ast.json').read_text())['tokens']

def leaves(t,p=''):
 if t[0]=='L':return {p:tuple(t[1])}
 return leaves(t[1],p+'0')|leaves(t[2],p+'1')
def bounds(t):
 if t[0]=='L':
  op,*a=t[1]
  return (1,0) if op=='dec' else (a[0],0) if op=='brk' else (0,a[0]) if op=='cont' else (0,0)
 x,y=bounds(t[1]),bounds(t[2])
 return max(x[0]-1,y[0],0),max(x[1],y[1]-1,0)
for t in TOKENS.values():assert bounds(t)==(0,0)
def inc(s):return format((int(s,2)+1)%(1<<len(s)),f'0{len(s)}b') if s else ''
def chop(s,bit,n):
 pos=[i for i,b in enumerate(s) if b==bit]
 return s if n==0 else s[:pos[-n]] if len(pos)>=n else ''
class Machine:
 def __init__(self,t):
  self.ops=leaves(['N',t,['L',['halt']]])
  self.max=max(map(len,self.ops))
  self.next={}
  def decode(p):
   for l in range(1,self.max+1):
    q=(p+'0'*self.max)[:l]
    if q in self.ops:return q
   raise AssertionError('non-total tree')
  self.start=decode('')
  for p,(op,*a) in self.ops.items():
   if op=='inc':self.next[p]=decode(inc(p))
   elif op=='dec':self.next[p]=(decode(inc(chop(p,'0',1))),decode(inc(p)))
   elif op=='brk':self.next[p]=decode(inc(chop(p,'0',a[0])))
   elif op=='cont':self.next[p]=decode(chop(p,'1',a[0]))
 def run(self,r,limit=10000000):
  r=list(r);p=self.start;steps=0
  while self.ops[p][0]!='halt':
   assert steps<limit,'finite diagnostic fuel exhausted, never a refutation'
   op,*a=self.ops[p];steps+=1
   if op=='inc':r[a[0]]+=1;p=self.next[p]
   elif op=='dec':
    positive=r[a[0]]>0
    if positive:r[a[0]]-=1
    p=self.next[p][positive]
   else:p=self.next[p]
  return r,steps
MACHINES={c:Machine(t) for c,t in TOKENS.items()}
def run(word,r):
 steps=0
 for c in word:r,n=MACHINES[c].run(r);steps+=n
 return r,steps
def pair(a,b):return (a+b)*(a+b+1)//2+b

class Pool:
 def __init__(self):self.rows=[('constant',0)];self.ids={self.rows[0]:0}
 def make(self,*row):
  row=tuple(row)
  if row not in self.ids:self.ids[row]=len(self.rows);self.rows.append(row)
  return self.ids[row]
 def one(self):return self.make('constant',1)
 def add(self,x,y):return y if x==0 else x if y==0 else self.make('add',*sorted((x,y)))
 def pair(self,x,y):return 0 if x==y==0 else self.make('pair',x,y)
 def split(self,x):
  if x==0:return 0,0
  t=self.rows[x]
  return (t[1],t[2]) if t[0]=='pair' else (self.make('left',x),self.make('right',x))
 def scale(self,x):return 0 if x==0 else self.make('four',x)
 def step(self,c,r):
  r=list(r)
  if c in 'LNOKUQIJ':
   src,dst={'L':(1,6),'N':(2,1),'O':(6,1),'K':(6,4),'U':(6,5),'Q':(7,2),'I':(7,8),'J':(6,3)}[c]
   r[dst]=self.add(r[dst],r[src]);r[src]=0
  elif c=='M':r[1]=self.add(r[1],self.one())
  elif c in 'RSX':
   src={'R':4,'S':5,'X':3}[c]
   r[1]=self.add(r[1],r[src]);r[6]=self.add(r[6],r[src]);r[src]=0
  elif c=='P':r[7]=self.add(r[7],self.pair(r[6],r[1]));r[1]=r[6]=0
  elif c=='W':r[1]=self.add(r[1],self.scale(r[7]));r[7]=0
  elif c in 'VH':
   assert r[6]==r[7]==0,('unpair precondition',c,r[6],r[7])
   src=2 if c=='V' else 8
   r[6],r[7]=self.split(r[src]);r[src]=0
  else:raise AssertionError(c)
  return r
 def replay(self,word,r):
  trace=[r]
  for c in word:trace.append(self.step(c,trace[-1]))
  return trace

def audit_word(word,label):
 assert word.endswith('YZGaZ')
 body=word[:-5];p=Pool();r=[p.make('variable',i) for i in range(9)];r[6]=r[7]=0
 old=p.replay(body,r);offsets=[];i=0
 while True:
  i=body.find(PATTERN,i)
  if i<0:break
  assert old[i][6]==old[i][7]==0,(label,i,'unclean replacement')
  # This is a symbolic identity on the exact state at this occurrence.
  assert p.replay(REPLACEMENT,old[i])[-1]==old[i+len(PATTERN)]
  offsets.append(i);i+=len(PATTERN)
 changed=body.replace(PATTERN,REPLACEMENT)
 after=p.replay(changed,r)[-1]
 assert after==old[-1] and after[6]==after[7]==0
 return dict(label=label,replacements=len(offsets),offsets=offsets,old_length=len(word),new_length=len(changed)+5,new_word=changed+'YZGaZ',same_nine_register_outputs=True,all_sites_clean=True,scratch_zero_after_body=True,expression_dag_nodes=len(p.rows),old_sha256=hashlib.sha256(word.encode()).hexdigest(),new_sha256=hashlib.sha256((changed+'YZGaZ').encode()).hexdigest())

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--words',type=Path);args=ap.parse_args()
 rng=random.Random(731);
 checks={'pair_general':0,'unpair_clean':0,'negation_clean':0};steps=0
 for t,u,v in itertools.product(range(12),range(12),range(3)):
  r=[rng.randrange(40) for _ in range(9)];r[1]=t;r[6]=u;r[7]=v
  got,k=run('P',r);expect=r.copy();expect[1]=expect[6]=0;expect[7]=v+pair(u,t)
  assert got==expect;checks['pair_general']+=1;steps+=k
 for n in range(512):
  r=[rng.randrange(40) for _ in range(9)];r[2]=n;r[6]=r[7]=0
  got,k=run('V',r);assert got[2]==0 and pair(got[6],got[7])==n
  assert all(got[i]==r[i] for i in (0,1,3,4,5,8))
  checks['unpair_clean']+=1;steps+=k
 for t,stack in itertools.product(range(16),range(16)):
  r=[rng.randrange(40) for _ in range(9)];r[1]=t;r[2]=stack;r[6]=r[7]=0
  a,k=run(PATTERN,r);b,l=run(REPLACEMENT,r);want=r.copy();want[1]=4*pair(t,1)
  assert a==b==want;checks['negation_clean']+=1;steps+=k+l
 negative=[]
 for r6,r7 in [(1,0),(0,1),(1,1)]:
  r=[0]*9;r[1]=2;r[2]=3;r[6]=r6;r[7]=r7
  a,_=run(PATTERN,r);b,_=run(REPLACEMENT,r)
  negative.append(dict(scratch=[r6,r7],equivalent=a==b,original=a,replacement=b))
 assert any(not x['equivalent'] for x in negative),'cleanliness necessity diagnostic'
 vocab=json.loads((HERE/'fine_source_ast.json').read_text())
 reports=[audit_word(vocab['root76'],'routed245_original_AX')]
 if args.words:
  for label,item in json.loads(args.words.read_text()).items():reports.append(audit_word(item['word'],label))
 result=dict(status='PASS_ALL_VALUE_PROOF_IN_ADJACENT_TEX',finite_checks=checks,primitive_operations=steps,dirty_scratch_negative_controls=negative,words=reports,AST_source=json.loads((HERE/'negation_ast.json').read_text())['source_sha256'],scope='Exact register peephole at proved clean sites; no standalone literal TM endpoint asserted')
 (HERE/'negation_audit.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='words'},indent=2))
 print('Audited words',len(reports),'original replacements',reports[0]['replacements'],'original new length',reports[0]['new_length'])
if __name__=='__main__':main()
