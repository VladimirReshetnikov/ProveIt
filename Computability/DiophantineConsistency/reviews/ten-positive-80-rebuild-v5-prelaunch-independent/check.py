#!/usr/bin/env python3
"""Independently mutation-check the actual pure v5 predicate; no rebuild."""
from pathlib import Path
from hashlib import sha256
import ast,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-coherent-rebuild';S=P/'run-v5.py';WR=P/'run-v5-outer.py';B1=P/'warning-baseline-pigeonhole/baseline.txt';B2=P/'warning-baseline-modelarithmetic/baseline.txt';H1=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/receipts/008.json';H2=D/'reviews/nine-variable-ipra-stages-3-5-author-audit/author/receipts/004.json';PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
assert sha(S)=='67f287a75d095fc45abde2d14acc732110956e3e248c154e817f92b14eb43558' and sha(WR)=='0d1b7d50fdf856c2e5f3f61e8a5f91004f4c5ef19a2295e148885bd7052e0d89'
assert sha(B1)=='1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92' and sha(B2)=='6af6ec8ca3ec1f14663f214b53f728a9a88b7b415ea8e68b769b27b197e44f0d'
assert sha(H1)=='86cea8817e9e52731cc61a6b3b983a0635d96cc8dba13ea1743ae6bb82133d94' and sha(H2)=='68e92da770d4ac5ff175531dfe6c334822a0a6d91e9af59f1e8f2ca56f2676e7'
tree=ast.parse(S.read_text());keys={'WARNING_MODULE','WARNING_SOURCE','MODEL_WARNING_MODULE','MODEL_WARNING_SOURCE'};names={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in keys};assert set(names)==keys
fns=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='diagnostics_allowed'];assert len(fns)==1
env={'re':re,**names};exec(compile(ast.Module(body=fns,type_ignores=[]),str(S),'exec'),env);f=env['diagnostics_allowed'];p,m=B1.read_text(),B2.read_text();plan=j(PLAN);logs=[]
for idx,(module,source,receipt,baseline,attempt,stage) in enumerate([(names['WARNING_MODULE'],names['WARNING_SOURCE'],H1,p,'attempt02',3),(names['MODEL_WARNING_MODULE'],names['MODEL_WARNING_SOURCE'],H2,m,'attempt02',5)]):
 h=j(receipt);r=j(P/'observations'/attempt/'result.json');t=r['stages'][stage-1];path=next(x for x in t['command'] if x.endswith('.lean'));log=(P/'observations'/attempt/f'stage-{stage:03}.stdout').read_text()+(P/'observations'/attempt/f'stage-{stage:03}.stderr').read_text()
 assert h['status']=='PASS' and h['module']==module and h['source_sha256']==source==t['source_sha256']==plan['sources'][module]['sha256'] and h['warning_policy']['baseline_sha256']==sha(B1 if idx==0 else B2)
 assert baseline.count('warning:')==3 and not re.search(r'\b(?:error|sorryAx)\b',baseline) and log.replace(path,'<SOURCE>')==baseline
 assert f(module,source,log,path,p,m);logs.append((module,source,log,path))
for module,source,log,path in logs:
 for altered in [log+'warning(lean.extra): x\n',log+'error(lean.foo): x\n',log+'sorryAx\n',log.replace('deprecated','changed',1),'\n'.join(log.splitlines()[1:])]:assert not f(module,source,altered,path,p,m)
 assert not f('Wrong',source,log,path,p,m) and not f(module,'0'*64,log,path,p,m)
for jdx in (0,1):
 module,source,_,_=logs[jdx];_,_,other,path=logs[1-jdx];assert not f(module,source,other,path,p,m)
assert f('Other','x','clean', '/tmp/source',p,m) and not f('Other','x','warning: x','/tmp/source',p,m)
wrapper=WR.read_text();assert "observations/outer-attempt03" in wrapper and "observations/attempt03" in wrapper and "sys.exit(p.returncode)" in wrapper and sha(S) in wrapper
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ten-positive-80-rebuild-v4-prelaunch-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS v5 actual two-baseline predicate, both historic receipt/source/log/plan pins, cross-baseline and all strict mutation tests')
print('fresh attempt03 outer wrapper pin/exit capture; inherited v4/v3 static guards; no Lean/rebuild launch')
