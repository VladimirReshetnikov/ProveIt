#!/usr/bin/env python3
"""Reproduce pinned screen and directly enumerate all three small controls."""
import copy,hashlib,importlib.util,json,operator,random,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('independent review requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/frontier13-shared-gate-screen';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs=[Path(__file__),TASK/'screen.py',TASK/'run.py',TASK/'receipt.json',TASK/'terminal-observation.json',BASE/'research/adaptive-square-sums/candidate.json',BASE/'research/adaptive-direct-ordinate86/candidate.json']
before={str(p.resolve()):H(p) for p in inputs};assert H(TASK/'screen.py')=='d83bb85014740275ba28b32891cd62c2665597094f80fc36327ea4f6617e790c'
for f in inputs[1:]:
 rel=str(f.relative_to(ROOT));b=subprocess.check_output(['git','show','8dd6f3d11f:'+rel],cwd=ROOT);assert hashlib.sha256(b).hexdigest()==H(f)
p=subprocess.run([sys.executable,str(TASK/'screen.py')],capture_output=True,text=True,timeout=120);assert p.returncode==0,(p.stdout,p.stderr)
result=json.loads(p.stdout);record=json.loads((TASK/'receipt.json').read_text());assert record['status']=='PASS_BOUNDED_SHARED_GATE_SCREEN' and result==record['normal']['result']
assert result['modulus']==2305843009213693951 and result['samples']==3 and result['seed']==459893 and result['literals']==[0,1,2,3,4]
assert [(x['original']['gates'],x['original']['multiplications'],x['original']['sampled_programs'],x['normalized']['gates'],x['normalized']['multiplications'],x['normalized']['sampled_programs']) for x in result['graphs']]==[(87,48,1208,87,47,1270),(86,47,1626,86,46,1688)]
assert (result['positive_control_findings'],result['alias_control_findings'],result['self_control_findings'])==(1,51,40)
opt=subprocess.run([sys.executable,'-O',str(TASK/'screen.py')],capture_output=True,text=True,timeout=30);assert opt.returncode!=0 and 'this certificate requires Python assertions enabled' in opt.stderr
spec=importlib.util.spec_from_file_location('screen_under_review',TASK/'screen.py');screen=importlib.util.module_from_spec(spec);spec.loader.exec_module(screen)
# Independent exact sparse integer polynomial identities in Z[q,F,alpha].
z=(0,0,0)
def const(n):return {} if not n else {z:n}
def var(i):e=[0,0,0];e[i]=1;return {tuple(e):1}
def add(a,b,sign=1):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,0)+sign*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d={}
 for x,v in a.items():
  for y,w in b.items():
   m=tuple(i+j for i,j in zip(x,y));d[m]=d.get(m,0)+v*w
 return {k:v for k,v in d.items() if v}
q,f,alpha=[var(i) for i in range(3)];qf=add(q,f,-1);C=add(qf,alpha,-1);q2=mul(q,q);fq=mul(f,q);old44=mul(qf,add(q,const(1),-1));oldG=add(alpha,old44);shared=mul(q,qf);shared2=add(q2,fq,-1)
assert add(q2,shared,-1)==fq and add(shared,C,-1)==oldG
assert add(shared2,qf,-1)==old44 and add(shared2,C,-1)==oldG
assert add(shared,C)!=oldG
# Evaluate graph liveness independently by DFS for every reported exact form.
def cost(rows,output,changes):
 table={x[0]:x for x in rows}
 for row in changes:table[row[0]]=row
 live=set()
 def visit(n):
  if not isinstance(n,str) or n in live:return
  live.add(n)
  if n in table:visit(table[n][2]);visit(table[n][3])
 visit(output);return (sum(x in live for x in table),sum(row[1]=='*' for n,row in table.items() if n in live)),live
for graph_path,entry in zip(inputs[-2:],result['graphs']):
 graph=json.loads(graph_path.read_text());rows=graph['source'];table={r[0]:r for r in rows}
 assert len(table)==len(rows) and [x[0] for x in rows if 'g44' in x[2:]]==['G']
 for required in (['q','+',1,'qm'],['qF','-','q','F'],['C','-','qF','alpha'],['g28','*','F','q'],['g44','*','qF','qm'],['G','+','alpha','g44']):assert table[required[0]]==required
 base,base_live=cost(rows,graph['output'],[]);assert base==(entry['original']['gates'],entry['original']['multiplications'])
 interface=set(graph['witnesses']+graph['fixed_numerals']);assert len(interface)==17 and interface<=base_live
 assert len(entry['original']['findings'])==2 and not entry['normalized']['findings']
 for found in entry['original']['findings']:
  actual,live=cost(rows,graph['output'],found['changes']);assert actual==(base[0],base[1]-1) and interface<=live
 normalized=screen.normalize(graph);changed=[(a,b) for a,b in zip(rows,normalized['source']) if a!=b]
 assert changed==[(['g44','*','qF','qm'],['g44','-','q2','g28']),(['G','+','alpha','g44'],['G','-','g44','C'])]
 actual,live=cost(normalized['source'],graph['output'],[]);assert actual==(base[0],base[1]-1) and interface<=live
# Directly enumerate all concrete shared programs in each toy, without
# division/inverse lookup or signature-index intersection.
def brute(g):
 rows=g['source'];M=screen.P;rng=random.Random(screen.SEED)
 vals={n:tuple(rng.randrange(2,M-1) for _ in range(3)) for n in g['witnesses']+g['fixed_numerals']};vals.update({str(n):(n,n,n) for n in screen.LITERALS})
 def calc(op,a,b):return tuple({'+' :operator.add,'-':operator.sub,'*':operator.mul}[op](x,y)%M for x,y in zip(a,b))
 prefixes=[];wanted=[]
 for name,op,a,b in rows:
  prefixes.append(list(vals));v=calc(op,vals[str(a)],vals[str(b)]);assert v!=(0,0,0);wanted.append(v);vals[name]=v
 baseline,_=cost(rows,g['output'],[]);findings=[];number=0
 def choices(t,available,target):
  out=[]
  for z0 in available:
   for op,a,b,rev in (('+',t,vals[z0],False),('-',t,vals[z0],False),('-',vals[z0],t,True),('*',t,vals[z0],False)):
    if calc(op,a,b)==target:out.append((op,z0,rev))
  for op in ('+','*'):
   if calc(op,t,t)==target:out.append((op,None,False))
  return out
 for i in range(len(rows)):
  available=prefixes[i];shared=[]
  for n in available:shared.append((None,n,vals[n]))
  for j,n in enumerate(available):
   for e in available[:j+1]:
    for op,a,b in (('+',e,n),('*',e,n),('-',e,n),('-',n,e)):shared.append((['CROSS_TEMP',op,a,b],'CROSS_TEMP',calc(op,vals[a],vals[b])))
  for j in range(i+1,len(rows)):
   for temp,n,t in shared:
    ci=choices(t,available,wanted[i]);cj=choices(t,prefixes[j],wanted[j])
    for oi,zi,ri in ci:
     ai,bi=(n,n) if zi is None else ((zi,n) if ri else (n,zi))
     for oj,zj,rj in cj:
      aj,bj=(n,n) if zj is None else ((zj,n) if rj else (n,zj));changes=[[rows[i][0],oi,ai,bi],[rows[j][0],oj,aj,bj]]
      if temp is not None:changes.insert(0,temp)
      number+=1;actual,_=cost(rows,g['output'],changes)
      if actual[0]<baseline[0] or (actual[0]==baseline[0] and actual[1]<baseline[1]):findings.append({'first':rows[i][0],'second':rows[j][0],'changes':changes,'gates':actual[0],'multiplications':actual[1]})
 findings.sort(key=lambda x:json.dumps(x,sort_keys=True))
 return {'gates':baseline[0],'multiplications':baseline[1],'sampled_programs':number,'findings':findings}
controls=[{'witnesses':['x','y','z','w'],'fixed_numerals':[],'source':[['a','*','x','z'],['b','*','y','z'],['i','+','a','b'],['c','*','x','w'],['d','*','y','w'],['j','+','c','d'],['out','+','i','j']],'output':'out'},
 {'witnesses':['x','y','z','w'],'fixed_numerals':[],'source':[['t','+','x','y'],['a','*','x','z'],['b','*','y','z'],['i','+','a','b'],['c','*','x','w'],['d','*','y','w'],['j','+','c','d'],['h','+','i','j'],['out','+','h','t']],'output':'out'},
 {'witnesses':['x','y'],'fixed_numerals':[],'source':[['x2','*','x','x'],['xy','*','x','y'],['y2','*','y','y'],['twoxy','*',2,'xy'],['s','+','x2','twoxy'],['i','+','s','y2'],['twox','*',2,'x'],['twoy','*',2,'y'],['j','+','twox','twoy'],['out','+','i','j']],'output':'out'}]
for i,g in enumerate(controls):
 direct=brute(g);indexed=screen.scan(g);assert direct==indexed,(i,direct,indexed)
 assert len(direct['findings'])==[1,51,40][i]
# Fail closed on zero target, nonunit divisor, and partially zero signature.
try:screen.scan({'witnesses':['x'],'fixed_numerals':[],'source':[['out','-','x','x']],'output':'out'})
except AssertionError as e:assert 'zero target sample' in str(e)
else:raise AssertionError('zero target accepted')
oldp=screen.P;oldrandom=screen.random.Random
class FixedTwo:
 def __init__(self,*a):pass
 def randrange(self,*a):return 2
screen.P=15;screen.random.Random=FixedTwo
try:
 try:screen.scan({'witnesses':['x','y'],'fixed_numerals':[],'source':[['out','+','x','y']],'output':'out'})
 except ValueError as e:assert 'invertible' in str(e)
 else:raise AssertionError('nonunit divisor accepted')
finally:screen.P=oldp;screen.random.Random=oldrandom
class Fake:
 def __init__(self,*a):self.seq=iter((2,3,4,5,6,7))
 def randrange(self,*a):return next(self.seq)
screen.random.Random=Fake
try:
 try:screen.scan({'witnesses':['x','y'],'fixed_numerals':[],'source':[['a','-','x',2],['out','+','a','y']],'output':'out'})
 except AssertionError as e:assert 'zero divisor sample' in str(e)
 else:raise AssertionError('partly zero earlier signature accepted')
finally:screen.random.Random=oldrandom
assert before=={str(p.resolve()):H(p) for p in inputs}
out={'status':'PASS_INDEPENDENT_SHARED_GATE_SCREEN_REVIEW','inputs_sha256':before,'screen_normal_exit':p.returncode,'screen_result':result,'screen_optimized_exit':opt.returncode,'direct_toy_controls':3,'fail_closed_controls':['zero target','noninvertible nonzero divisor','partly zero earlier signature'],'scope':'Finite same-target universal-port shared-gate family; no fixed-port-only, graph-wide, zero-set, global-minimality or Lean claim.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
