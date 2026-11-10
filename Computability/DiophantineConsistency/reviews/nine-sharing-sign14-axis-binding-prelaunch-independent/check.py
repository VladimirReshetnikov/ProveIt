#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-axis-binding-check';base=root/'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='1243c4a1bb04e08e88ffa8d40e1864c0c761901d58f0998bc2f3fa76d97c4b37' and sha(p/'source-manifest.json')=='bb3a2e5ed3720d9377b805891ae75f52bdbd9b2bf301a2a83cdd7dda019d2d86' and sha(p/'provider-survey.py')=='b60d482d45817013636c7d70cf0e3388ca62f0f1f05ab16a5a1bdbc8596de469'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==3;names=['Sign14AxisBindingBase','Sign14AxisBindingFactors','Sign14AxisBindingRoot'];assert [e['module'].split('.')[-1] for e in rows]==names
for i,e in enumerate(rows):
 src=p/'src/DiophantineConsistency'/(names[i]+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
 assert e['imports']==(['DiophantineConsistency.Sign14AxisGenericDegree','DiophantineConsistency.Sign14DegreeCompose'] if i==0 else ['DiophantineConsistency.'+names[i-1]])
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
for name,expected in [('shared07',low),('shared31',dominant),('shared28',middle),('shared38',rt),('shared42',scale)]:assert env[name]==expected;assert f'theorem {name}_axis' in ''.join((p/'src/DiophantineConsistency'/(n+'.lean')).read_text() for n in names)
s=(p/'src/DiophantineConsistency/Sign14AxisBindingBase.lean').read_text();assert 'def axis (i : Fin 15) : P := if i = 0 then 1 else Polynomial.X' in s
for c,h in [('reviews/nine-sharing-sign14-axis-degree-generic-terminal-independent/check.py','d8e7df010a2d5f921a22ed77c6d2d67bb89908ddae4796215dff4ac339ad3996'),('reviews/nine-sharing-sign14-degree-upper-terminal-independent/check.py','330de382413acab3ef7687f6e62ffdcf5b49ba22a77d79cbd227a6c9386e12b3')]:q=root/c;assert sha(q)==h;subprocess.run([sys.executable,'-I','-S','-B',str(q)],capture_output=True,check=True,timeout=120)
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);d=json.loads(z.stdout);assert d['status']=='PASS' and d['overlap_count']==1058 and len(d['extra'])==38
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':3,'overlaps':1058,'extras':38,'scope':'proposed staged root/scale axis identities; no lower or external binding'},indent=2))
