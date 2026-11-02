#!/usr/bin/env python3
"""Independent brute-force toy cross-check and pinned screen reproduction."""
import copy,hashlib,importlib.util,json,operator,random,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('independent review requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/frontier13-local-rewrite-screen';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs=[Path(__file__),TASK/'screen.py',TASK/'run.py',TASK/'receipt.json',TASK/'terminal-observation.json',BASE/'research/adaptive-square-sums/candidate.json',BASE/'research/adaptive-direct-ordinate86/candidate.json']
before={str(p.resolve()):H(p) for p in inputs}
assert H(TASK/'screen.py')=='c84efc4610afeea00b847becf4991b519ade4939dcc09ae117d8f4ae478cf090'
for f in inputs[1:]:
 rel=str(f.relative_to(ROOT));b=subprocess.check_output(['git','show','15db63be67:'+rel],cwd=ROOT);assert hashlib.sha256(b).hexdigest()==H(f)
p=subprocess.run([sys.executable,str(TASK/'screen.py')],capture_output=True,text=True,timeout=120);assert p.returncode==0,(p.stdout,p.stderr)
result=json.loads(p.stdout);record=json.loads((TASK/'receipt.json').read_text());assert record['status']=='PASS_BOUNDED_SCREEN' and result==record['normal']['result']
assert result['modulus']==2305843009213693951 and result['samples']==3 and result['seed']==773845 and result['literal_set']==[0,1,2,3,4]
expected=[(87,0,87,0,1326,0,81,0),(86,0,86,0,1505,0,57,0)]
keys=('rows','alias_sample_matches','one_gate_sample_matches','one_gate_strict_candidates','two_gate_sample_matches','two_gate_strict_candidates','self_gate_sample_matches','self_gate_strict_candidates')
assert [tuple(row[k] for k in keys) for row in result['graphs']]==expected
assert result['positive_control']['one_gate_strict_candidates']>0 and result['positive_control']['two_gate_strict_candidates']>0
assert result['self_gate_positive_control']['self_gate_strict_candidates']>0
opt=subprocess.run([sys.executable,'-O',str(TASK/'screen.py')],capture_output=True,text=True,timeout=30);assert opt.returncode!=0 and 'this certificate requires Python assertions enabled' in opt.stderr
spec=importlib.util.spec_from_file_location('screen_under_review',TASK/'screen.py');screen=importlib.util.module_from_spec(spec);spec.loader.exec_module(screen)
# Independently enumerate all concrete operation syntax on small graphs. This
# deliberately computes products directly instead of using division lookups.
def brute(graph):
 modulus=screen.MODULUS; rng=random.Random(screen.SEED);val={x:tuple(rng.randrange(2,modulus-1) for _ in range(screen.SAMPLES)) for x in graph['witnesses']+graph['fixed_numerals']}
 for x in screen.LITERALS:val[str(x)]=(x,)*screen.SAMPLES
 available=list(val); rows=graph['source'];counts={k:0 for k in ('alias_sample_matches','one_gate_sample_matches','one_gate_strict_candidates','two_gate_sample_matches','two_gate_strict_candidates','self_gate_sample_matches','self_gate_strict_candidates')}
 def calc(op,a,b):return tuple(({'+':operator.add,'-':operator.sub,'*':operator.mul}[op](x,y))%modulus for x,y in zip(a,b))
 def count_live(repl):
  table={row[0]:row for row in rows}
  for row in repl:table[row[0]]=row
  seen=set()
  def visit(n):
   if not isinstance(n,str) or n in seen:return
   seen.add(n)
   if n in table:
    visit(table[n][2]);visit(table[n][3])
  visit(graph['output']);return sum(n in seen for n in table)
 for target,kind,left,right in rows:
  wanted=calc(kind,val[str(left)],val[str(right)]); assert wanted!=(0,)*screen.SAMPLES
  counts['alias_sample_matches']+=sum(val[z]==wanted for z in available)
  expr=[]
  for j,right in enumerate(available):
   for left in available[:j+1]:
    for op,a,b in (('+',left,right),('*',left,right),('-',left,right),('-',right,left)):
     expr.append((op,a,b,calc(op,val[a],val[b])))
  for op,a,b,sig in expr:
   if sig==wanted:
    counts['one_gate_sample_matches']+=1
    if count_live([[target,op,a,b]])<len(rows):counts['one_gate_strict_candidates']+=1
   for z in available:
    for final,aa,bb,vs in (('+','SCREEN_TEMP',z,calc('+',sig,val[z])),('-', 'SCREEN_TEMP',z,calc('-',sig,val[z])),('-',z,'SCREEN_TEMP',calc('-',val[z],sig)),('*','SCREEN_TEMP',z,calc('*',sig,val[z]))):
     if vs==wanted:
      counts['two_gate_sample_matches']+=1
      if count_live([['SCREEN_TEMP',op,a,b],[target,final,aa,bb]])<len(rows):counts['two_gate_strict_candidates']+=1
   for final in ('+','*'):
    if calc(final,sig,sig)==wanted:
     counts['self_gate_sample_matches']+=1
     if count_live([['SCREEN_TEMP',op,a,b],[target,final,'SCREEN_TEMP','SCREEN_TEMP']])<len(rows):counts['self_gate_strict_candidates']+=1
  val[target]=wanted;available.append(target)
 return counts
controls=[{'witnesses':['x','y','z','w'],'fixed_numerals':[],'source':[['a','+','x','y'],['b','*','a','z'],['c','*','x','z'],['d','-','b','c'],['out','*','d','w']],'output':'out'},
 {'witnesses':['x','y','z','w'],'fixed_numerals':[],'source':[['a','+','x','y'],['b','+','a','z'],['c','*','b','b'],['d','+','c','w'],['out','-','d','w']],'output':'out'}]
for i,g in enumerate(controls):
 got=brute(g);assert got==screen.scan(g)==result['positive_control' if i==0 else 'self_gate_positive_control']
# A universally zero sampled target must stop the screen rather than pass.
try:screen.scan({'witnesses':['x'],'fixed_numerals':[],'source':[['out','-','x','x']],'output':'out'})
except AssertionError as e:assert 'zero target sample' in str(e)
else:raise AssertionError('zero sampled target was silently accepted')
# Product z=3 is noninvertible in Z/15Z even though it is nonzero; inversion
# must raise instead of discarding potential product candidates.
oldmod=screen.MODULUS;screen.MODULUS=15
try:
 try:screen.scan({'witnesses':['x','y'],'fixed_numerals':[],'source':[['out','+','x','y']],'output':'out'})
 except (AssertionError,ValueError) as e:assert 'invertible' in str(e) or 'zero divisor' in str(e)
 else:raise AssertionError('nonunit divisor was silently accepted')
finally:screen.MODULUS=oldmod
# A prior node with a zero in only one sampled coordinate is not a unit in
# the product ring. Construct it while the target signature is not all zero.
oldrandom=screen.random.Random
class Fake:
 def __init__(self,*args):self.seq=iter((2,3,4,5,6,7))
 def randrange(self,*args):return next(self.seq)
screen.random.Random=Fake
try:
 try:screen.scan({'witnesses':['x','y'],'fixed_numerals':[],'source':[['a','-','x',2],['out','+','a','y']],'output':'out'})
 except AssertionError as e:assert 'zero divisor sample' in str(e)
 else:raise AssertionError('partly zero earlier signature was silently accepted')
finally:screen.random.Random=oldrandom
assert before=={str(p.resolve()):H(p) for p in inputs}
out={'status':'PASS_INDEPENDENT_BOUNDED_REWRITE_SCREEN_REVIEW','inputs_sha256':before,'screen_normal_exit':p.returncode,'screen_normal_result':result,'screen_optimized_exit':opt.returncode,'brute_toy_controls':2,'fail_closed_controls':['zero sampled target','noninvertible nonzero divisor','partly zero earlier signature'],'scope':'Finite sampled rejection of exact universal-port local target identities only; no fixed-port-only, graph-wide, zero-set, global minimality or Lean claim.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
