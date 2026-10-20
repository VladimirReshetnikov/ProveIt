"""Read pinned Coq only as text; audit remaining rho8 bounds after proved basis fragments."""
import re,json
from pathlib import Path
S=(Path(__file__).resolve().parents[2]/'evidence/logic/CD230.v').read_text()
D=Path(__file__).parent

def parse(s):
 ts=re.findall(r'cd_\d+|T_mp|wim|v\d+|\d+|_|[()]',s);i=0
 def one():
  nonlocal i
  t=ts[i];i+=1
  if t!='(':return t
  z=[]
  while ts[i]!=')':z.append(one())
  i+=1;return tuple(z)
 out=[]
 while i<len(ts):out.append(one())
 return tuple(out)
lem={}
for m in re.finditer(r'Lemma cd_(\d+) \((.*?) : nat\).*?Proof\. exact \((.*?)\)\. Qed\.',S,re.S):
 lem[int(m[1])]=(m[2].split(),parse(m[3]))
assert len(lem)==107

def I(a,b):return (a,b)
def fmt(t):return '('+fmt(t[0])+'>'+fmt(t[1])+')' if isinstance(t,tuple) else t
def contains(a,b):return a==b or isinstance(a,tuple) and any(contains(x,b)for x in a)
base={2,3,6,8,9,12,13,15,16,17,25,39,40,59}

for goal in [91]:
 seen=set();bad=[];good=0;stopped=False
 def prove(n,args,path):
  global good,stopped
  if stopped:return
  key=(n,args)
  if key in seen:return
  if len(seen)>=5000:stopped=True;return
  seen.add(key)
  if n in base:return
  if n==0:
   c,u,a,b=args
   if u=='T' or contains(a,u):good+=1
   else:
    bad.append({'U':fmt(u),'A':fmt(a),'path':path,'reverse_strict_subterm':u!=a and contains(u,a)})
    if len(bad)>=20:stopped=True
   return
  vs,body=lem[n];env=dict(zip(vs,args));env['0']='T'
  def term(t):
   if isinstance(t,str):return env[t]
   assert t[0]=='wim';return I(term(t[1]),term(t[2]))
  def walk(t):
   if t[0]=='T_mp':walk(t[-2]);walk(t[-1])
   else:
    assert t[0].startswith('cd_')
    k=int(t[0][3:]);prove(k,tuple(term(x)for x in t[1:]),path+[k])
  walk(body)
 prove(goal,tuple('V'+str(i)for i in range(3)),[goal])
 out={'goal':goal,'base_replacements':sorted(base),'visited':len(seen),'good_leaf_instances':good,'bad':bad,'stopped_at_cap':stopped}
 (D/f'conditional_cd59_replay_cd{goal}.json').write_text(json.dumps(out,indent=2))
 print(json.dumps(out,indent=2))
