#!/usr/bin/env python3
"""Review main-root lift and provider routes, including independent lift AST."""
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign18-coordinate-check';draft=research/'nine-sharing-sign18-staged-syntax-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();src=p/'src/DiophantineConsistency/Sign18Coordinate.lean';e,=json.loads((p/'source-manifest.json').read_text())['rows'];s=src.read_text()
assert e['module']=='DiophantineConsistency.Sign18Coordinate' and sha(src)==sha(draft/'Sign18Coordinate.lean')==e['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.SharingSign18Squares','DiophantineConsistency.SharingSign19Squares']
lift=s.split('def lift ',1)[1].split('![',1)[1].split(']',1)[0];drop=s.split('def drop ',1)[1].split('![',1)[1].split(']',1)[0];lc=[x.strip() for x in lift.split(',')];dc=[x.strip() for x in drop.split(',')];assert lc[:15]==[f'v {i}' for i in range(15)] and lc[15]=='rootValue beta v' and lc[16:]==[f'v {i}' for i in range(15,19)];assert dc==[f'v {i}' for i in range(15)]+[f'v {i}' for i in range(16,20)]
line=s.split('def rootValue ',1)[1].split(':=\n  ',1)[1].splitlines()[0];line=re.sub(r'\(v (\d+)\)',r'v[\1]',line);tree=ast.parse(line,mode='eval').body
def convert(t):
 if isinstance(t,ast.BinOp):
  op={ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}.get(type(t.op));assert op;return [op,convert(t.left),convert(t.right)]
 if isinstance(t,ast.Name):assert t.id=='beta';return ['port','beta']
 if isinstance(t,ast.Constant):assert isinstance(t.value,int);return ['num',t.value]
 if isinstance(t,ast.Subscript):assert isinstance(t.value,ast.Name) and t.value.id=='v' and isinstance(t.slice,ast.Constant);return ['var',t.slice.value]
 raise AssertionError(ast.dump(t))
candidate=research/'nine-sharing-sign18-degree94-root-candidate/seed.json';assert sha(candidate)=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb';assert convert(tree)==json.loads(candidate.read_text())['lift_expression']
assert all('theorem '+n in s for n in ('root_identity','root_zero','root_coordinate','lift_drop')) and s.count('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)')==3 and 'add_right_cancel he\'' in s
runner=p/'run.py';assert sha(runner)=='b27fb8c7ccb8e56b989896fdb0435a8a90b17aeef7e7ff517de1be08d723f068';r=runner.read_text();assert "if local=='SharingSign18Squares':" in r and "elif local in observed['observed']:" in r and "for name,rec in observed['observed'].items():" in r and "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
for review in ('nine-sharing-sign18-staged-syntax-terminal-independent','nine-sharing-sign19-staged-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'lift_ast_matches_external':True,'scope':'source and provider review only, no Lean coordinate theorem or bridge'},indent=2,sort_keys=True))
