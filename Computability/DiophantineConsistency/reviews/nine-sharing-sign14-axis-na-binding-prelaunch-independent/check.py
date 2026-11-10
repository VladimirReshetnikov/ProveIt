#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-axis-na-binding-check';base=root/'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='82befa93b86a47947627f8b04724cb1d0e09aa23d052ee9337e7b3993e6651b0' and sha(p/'source-manifest.json')=='9c0c38fe901892d92741a239443b98857e6f1477935393ef15466ac7bb1a63dc' and sha(p/'provider-survey.py')=='8e8d27b9176a1a08f0f6c0c4a139ce6ee24243af1668744071ca670cbb0d6e06'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14AxisNaBinding';src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign14AxisInnerBinding','DiophantineConsistency.Sign14AxisGenericNaDegree'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
assert 'theorem row03_axis (p : Fin 4 → ℤ)' in s and 'theorem row03_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0)' in s and '.natDegree = 62' in s
# Sparse integer polynomials in (axis t, port0, port1, port2, port3), expanded independently.
zero=(0,0,0,0,0)
def const(x):return {zero:x} if x else {}
def var(i):k=[0]*5;k[i]=1;return {tuple(k):1}
def add(a,b,sign=1):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(x+y for x,y in zip(ka,kb));c[k]=c.get(k,0)+va*vb
 return {k:v for k,v in c.items() if v}
lex=re.compile(r'\s*(Expr\.constant|Expr\.var|shared[0-9]{2}|[0-9]+|p|ℤ|[()+*:\-])');env={}
def evaluate(line):
 toks=[];pos=0
 while pos<len(line):m=lex.match(line,pos);assert m,(pos,line[pos:pos+30]);toks.append(m[1]);pos=m.end()
 i=0
 def take(x=None):
  nonlocal i
  t=toks[i];i+=1
  if x is not None:assert t==x
  return t
 def expr():
  take('(');t=toks[i]
  if t.startswith('shared'):name=take();take('p');take(')');return env[name]
  if t=='Expr.var':take();j=int(take());take(')');assert 1<=j<=14;return var(0)
  if t=='Expr.constant':
   take();take('(');v=take()
   if v=='p':j=int(take());assert j in range(4);a=var(j+1)
   else:a=const(int(v));take(':');take('ℤ')
   take(')');take(')');return a
  a=expr();op=take();b=expr();take(')');assert op in ('+','-','*');return mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 value=expr();assert i==len(toks);return value
for i in range(44):
 name=f'shared{i:02}';s=(base/f'SharingSeed14Shared{i//5:02}.lean').read_text();m=re.search(r'^def '+name+r' \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.*)$',s,re.M);assert m;env[name]=evaluate(m[1])
t=var(0);z=var(1);one=const(1);shift=add(t,one);affine=add(mul(z,shift),one);cube=mul(mul(affine,affine),affine);y=mul(shift,cube);e=mul(mul(shift,affine),y);u=add(mul(mul(const(2),shift),y),shift);low=add(mul(t,affine),mul(z,shift));dominant=mul(add(e,y),u);middle=mul(shift,add(mul(const(4),add(e,y)),const(3)));rt=add(add(low,dominant),middle);scale=mul(mul(shift,rt),add(rt,const(2)))

correction=env['shared14'];rank=env['shared27'];inner=add(mul(mul(shift,shift),add(add(mul(shift,u),correction),rank,-1)),u,-1)
rowfile=(base/'SharingSeed14Row03.lean').read_text();m=re.search(r'^def row03 \(p : Fin 4 → ℤ\) : Expr \(Fin 15\) :=\n  (.*)$',rowfile,re.M);assert m
expected=add(add(mul(shift,shift),mul(mul(scale,scale),add(mul(shift,shift),mul(inner,inner),-1)),-1),const(1),-1);assert evaluate(m[1])==expected
for c,h in [('reviews/nine-sharing-sign14-axis-na-generic-terminal-independent/check.py','21eb0e1270ed0a64f189269263cff1fb6829c3b54d0d62d3e9cbc054d2bca224'),('reviews/nine-sharing-sign14-axis-inner-binding-terminal-independent/check.py','917c8bd532c54e405251df00036596f3300e41997cc40759ccdcb0c853f5c539')]:q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);d=json.loads(z.stdout);assert d['status']=='PASS' and d['overlap_count']==1097 and len(d['extra'])==0
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'actual row03 axis degree62 under p0 nonzero; seed lower and external binding separate'},indent=2))
