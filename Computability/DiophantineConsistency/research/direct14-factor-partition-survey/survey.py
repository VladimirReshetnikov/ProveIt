#!/usr/bin/env python3
"""Bounded search over partitions of the four existing 13-variable factors."""
import hashlib,itertools,json,math,subprocess,sys
from collections import Counter
from functools import lru_cache
from pathlib import Path
if not __debug__:raise RuntimeError('assertions required')
D=Path(__file__).resolve().parent
P=D.parent/'adaptive-square-sums/candidate.json'
P86=D.parent/'adaptive-direct-ordinate86/candidate.json'
assert hashlib.sha256(P.read_bytes()).hexdigest()=='11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828'
assert hashlib.sha256(P86.read_bytes()).hexdigest()=='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f'
c=json.loads(P.read_text());assert c['operations']==87 and len(c['witnesses'])==13
parent=json.loads(P86.read_text());assert c['parent_sha256']==hashlib.sha256(P86.read_bytes()).hexdigest()
table={r[0]:r for r in parent['source']}
for row in [['F0','+',1,'A0'],['F1','+',1,'A1'],['Fs','+',1,'g72'],['g86','*','F0','F1'],
            ['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]:
 assert table[row[0]]==row
assert parent['output']=='P13'
cert=subprocess.run([sys.executable,str(D.parent/'adaptive-square-sums/verify.py')],capture_output=True,text=True,timeout=180)
assert cert.returncode==0 and 'exact degree 36' in cert.stdout
cert86=subprocess.run([sys.executable,str(D.parent/'adaptive-direct-ordinate86/verify_degree86.py')],capture_output=True,text=True,timeout=180)
assert cert86.returncode==0 and 'factor degrees 15,13,18,10' in cert86.stdout
prefix=c['source'][:-7];assert prefix[-1][0]=='auxResidual' and c['source'][-1][0]=='sumSquares'
labels=('first','main','aux','strong');residuals=('A0','A1','auxResidual','g72');degrees=(15,13,18,10)
def partitions(items):
 if not items:
  yield ();return
 first=items[0]
 for tail in partitions(items[1:]):
  yield ((first,),)+tail
  for i in range(len(tail)):
   yield tail[:i]+((first,)+tail[i],)+tail[i+1:]
@lru_cache(None)
def plans(group):
 if len(group)==1:return (('atom',group[0]),)
 result=[('raw',group)]
 for n in range(1,len(group)):
  for left in itertools.combinations(group,n):
   right=tuple(x for x in group if x not in left)
   if left[0]!=group[0]:continue
   result += [('combine',a,b) for a in plans(left) for b in plans(right)]
 return tuple(result)
def make(partition,chosen):
 rows=[list(x) for x in prefix];known=set(c['witnesses']+c['fixed_numerals'])|{r[0] for r in rows}
 counter=itertools.count();memo={}
 for n,op,a,b in rows:
  key=(op,a,b) if op=='-' or str(a)<=str(b) else (op,b,a)
  memo.setdefault(key,n)
 def node(op,a,b):
  key=(op,a,b) if op=='-' or str(a)<=str(b) else (op,b,a)
  if key in memo:return memo[key]
  n='partitionGate'+str(next(counter));assert n not in known;known.add(n);rows.append([n,op,a,b]);memo[key]=n;return n
 def build(plan):
  if plan[0]=='atom':return residuals[plan[1]]
  if plan[0]=='raw':
   factors=[('Fa' if x==2 else node('+',1,residuals[x])) for x in plan[1]]
   result=factors[0]
   for f in factors[1:]:result=node('*',result,f)
   return node('-',result,1)
  a,b=build(plan[1]),build(plan[2]);return node('+',node('+',a,b),node('*',a,b))
 result=[build(plan) for plan in chosen]
 if len(result)==1:output=result[0]
 else:
  squared=[node('*',r,r) for r in result];output=squared[0]
  for r in squared[1:]:output=node('+',output,r)
 table={r[0]:r for r in rows};live={output};todo=[output]
 while todo:
  n=todo.pop()
  if n in table:
   for dep in table[n][2:]:
    if isinstance(dep,str) and dep not in live:live.add(dep);todo.append(dep)
 kept=[r for r in rows if r[0] in live]
 assert set(c['witnesses']+c['fixed_numerals']) <= live
 return kept,output
def evalplan(plan,values,sign=1):
 if plan[0]=='atom':return values[plan[1]]
 if plan[0]=='raw':return math.prod(1+values[i] for i in plan[1])-1
 a,b=evalplan(plan[1],values,sign),evalplan(plan[2],values,sign)
 return a+b+sign*a*b
def check_identity(group,plan,sign=1):
 for values in itertools.product((-2,0,1),repeat=4):
  assert evalplan(plan,values,sign)==math.prod(1+values[i] for i in group)-1
parts=list(partitions(tuple(range(4))));assert len(parts)==15 and len(set(parts))==15
records=[];best_graphs={}
for partition in parts:
 choices=[plans(group) for group in partition];best=None
 for choice in itertools.product(*choices):
  for group,plan in zip(partition,choice):
   check_identity(group,plan)
  rows,output=make(partition,choice);score=(len(rows),repr(choice))
  if best is None or score<best[0]:best=(score,rows,output,choice)
 _,rows,output,choice=best
 deg=max(sum(degrees[i] for i in group) for group in partition)
 if len(partition)>1:deg*=2
 name='|'.join('+'.join(labels[i] for i in group) for group in partition)
 item={'partition':name,'degree':deg,'operations':len(rows),'breakdown':dict(sorted(Counter(r[1] for r in rows).items())),
       'plans':[repr(p) for p in choice]}
 records.append(item);best_graphs[name]=(rows,output)
frontier=[r for r in records if not any(s['degree']<=r['degree'] and s['operations']<=r['operations'] and
          (s['degree']<r['degree'] or s['operations']<r['operations']) for s in records)]
assert min(x['operations'] for x in records)>=86
try:check_identity((0,1),('combine',('atom',0),('atom',1)),-1)
except AssertionError:pass
else:raise AssertionError('wrong-sign plan survived identity checks')
result={'status':'PASS_BOUNDED_FACTOR_PARTITION_SURVEY','parent_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),
        'factor_parent_sha256':hashlib.sha256(P86.read_bytes()).hexdigest(),'prior_degree_checker_exit':cert.returncode,
        'four_factor_degree_checker_exit':cert86.returncode,
        'identity_grid':'all {-2,0,1}^4 assignments for each enumerated plan; exact identity also follows by induction',
        'partitions_checked':len(parts),'family':'All set partitions of four factor-unit constraints; direct factor products and recursively combined residual plans; operation minima only inside enumerated syntax.',
        'factor_residual_degrees':dict(zip(labels,degrees)),'records':records,'frontier':frontier,
        'scope':'Finite graph-cost enumeration and degree inference from the existing exact residual certificates. Zero equivalence uses the existing factor-unit theorem and ordinary sum-of-squares reasoning; no new Lean proof or global minimum.'}
out=D/'results.json'
if out.exists() and out.read_text()!=json.dumps(result,indent=2,sort_keys=True)+'\n':raise ValueError('refusing to overwrite changed results')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('PASS_BOUNDED_FACTOR_PARTITION_SURVEY',len(parts),'frontier',[(r['degree'],r['operations']) for r in frontier],hashlib.sha256(out.read_bytes()).hexdigest())
