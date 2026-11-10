#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-93gate-bridge-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='798e47c812a4a95041b2e7afac5f8a7a64d557059548d74909c1bbd1bbe10be3' and sha(p/'provider-survey.py')=='dc369ab10ac5fa654bd922b38cff81bd5abbfafa047b3340f7e8af410af203ed' and sha(p/'source-manifest.json')=='7bdb212e28b7df0e57e6c170a8848d696a1db9fbf755104ff1294c4fc703fdc3'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized93Bridge.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized93Bridge' and e['imports']==['DiophantineConsistency.Sign14Optimized93Model','DiophantineConsistency.GenericPolynomialBridgeTransport','DiophantineConsistency.Sign14Optimized94Bridge'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge','Sign14Optimized93Expression.expression CurrentWindowCarry2011.ports','GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign14Optimized94IPRA.polynomialBridge','Sign14Optimized93Model.zero_exists_iff (V := V) CurrentWindowCarry2011.ports'):assert t in s
for f in ('nine-sharing-sign14-93gate-model-terminal-independent','nine-sharing-sign14-94gate-bridge-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS' and v['overlap_count']==1120 and len(v['extra'])==630
base=Path('/tmp/nine-sharing-sign14-93gate-model-check-20261110/lib');states=['nine-sharing-sign14-94gate-bridge-check','nine-sharing-sign14-95gate-bridge-retry01-check','nine-sharing-sign14-concrete-polynomial-bridge-check','nine-sharing-sign15-concrete-polynomial-bridge-check','nine-sharing-sign14-expression-equivalence-check','nine-sharing-sign14-current-iff-check','nine-sharing-sign14-expression-eval-check','nine-sharing-sign14-95gate-model-check','nine-sharing-sign14-95gate-expression-check','nine-sharing-sign14-95gate-lean-retry01-check'];checked=[]
for stem in states:
 st=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert st['status']=='PASS'
 for row in st['rows']:
  for mod,d in row['dependencies'].items():
   if mod=='Init':continue
   rel=mod.replace('.','/')+'.olean';found=v['extra'].get(rel)
   if found is None:
    z=base/rel;assert z.is_file(),(row['module'],mod,'missing base/extra');found={'realpath':str(z.resolve()),'sha256':sha(z)}
   assert found['realpath']==d['realpath'] and found['sha256']==d['sha256'],(row['module'],mod);checked.append((row['module'],mod))
assert len(checked)>=20 and any(a=='Sign14DirectPolynomialBridge' and b.endswith('Sign15DirectPolynomialBridge') for a,b in checked)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','captured_direct_edges':len(checked),'overlaps':1120,'extra':630,'scope':'93-gate optimized symbolic all-model polynomial bridge conditional on Lean; no complete trace/file/JSON/PDF theorem'},indent=2))
