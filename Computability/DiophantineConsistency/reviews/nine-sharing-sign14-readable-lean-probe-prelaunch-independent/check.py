#!/usr/bin/env python3
import contextlib,hashlib,io,json,re,runpy,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-readable-lean-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='c55a15c78cc13c7eb3fc21b29dc2945b2e2478f14c6b332f47735c3a6d59924c' and sha(p/'source-manifest.json')=='e98add1911cb6ec8e61bcc087ef3736968852b9f744df2a3afe8409761d705b0'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==2;srcs=[]
for i,e in enumerate(rows):
 n=e['module'].split('.')[-1];q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s);srcs.append(s)
assert rows[0]['imports']==['DiophantineConsistency.SharingSeed14Degree124'] and rows[1]['imports']==['DiophantineConsistency.Sign14Readable']
s,low=srcs;assert 'def positive (i : Fin 15) : E := Expr.var i + 1' in s
names=['judge','bound','slack','divisor','factor','index','clock','height','width','count','left','right','target','extra']
for i,n in enumerate(names,1):assert f'def {n} : E := positive {i}' in s
b=io.StringIO()
with contextlib.redirect_stdout(b):check=runpy.run_path(str(root/'reviews/nine-sharing-sign14-readable-equation-independent/check.py'))
assert json.loads(b.getvalue())['status']=='PASS_EXTERNAL_PRESENTATION_AUDIT';calc=check['calc'];expected=check['expected'];inner=check['g'];env=check['env']
def leanexpr(x):
 x=re.sub(r'Expr\.constant \(p ([0-3])\)',lambda m:['β','K','μ','ω'][int(m.group(1))],x);x=re.sub(r'\b([a-z]+) p\b',r'\1',x);return calc(' '.join(x.split()))
defs=dict(re.findall(r'^def (\w+)(?: \(p : Fin 4 → ℤ\))? : E :=\s*(.*?)(?=\ndef |\nend )',s,re.M|re.S));assert set(expected)|{'first','second','third','fourth','fifth','seed'}<=set(defs)
for n,v in expected.items():assert leanexpr(defs[n])==v,n
for i,n in enumerate(('first','second','third','fourth','fifth')):inner['assert_equal']('Lean '+n,leanexpr(defs[n]),inner['expected'][i])
want=inner['as_p'](0)
for n in ('first','second','third','fourth','fifth'):want=want+env[n]*env[n]
assert leanexpr(defs['seed'])==want
for t in ('theorem low_eval {R : Type*} [CommRing R] (v : Fin 15 → R) (p : Fin 4 → ℤ)','(SharingSeed14Degree124.shared07 p).evalRing v = (horizontal p).evalRing v - 1','#print axioms DiophantineConsistency.Sign14Readable.low_eval'):assert t in low
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign14-staged-syntax-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','positive_variables':14,'aliases':len(expected),'residuals':5,'scope':'readable formal syntax and generic low identity only; other identities/JSON/PDF unproved'},indent=2))
