#!/usr/bin/env python3
"""Independently mutate actual pure v6 warning predicate; no rebuild."""
from pathlib import Path
from hashlib import sha256
import ast,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-coherent-rebuild';S=P/'run-v6.py';W=P/'run-v6-outer.py';PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
assert sha(S)=='1956a0831c4dc93c5f30ff578ec6e7731c7d56f4be695d3ee8a7c4681a982298' and sha(W)=='8f159ccb6850fd8012900dcfd20d8fce0b037b764295ad3e1e6b279b64b47fed'
tree=ast.parse(S.read_text());keys={p+s for p in ('WARNING','MODEL_WARNING','RATIO_WARNING') for s in ('_MODULE','_SOURCE')};names={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in keys};assert set(names)==keys
fn=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='diagnostics_allowed'];assert len(fn)==1;env={'re':re,**names};exec(compile(ast.Module(body=fn,type_ignores=[]),str(S),'exec'),env);f=env['diagnostics_allowed']
items=[('WARNING','warning-baseline-pigeonhole','nine-variable-ipra-stages-6-9-author-observation','008','1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92',3),('MODEL_WARNING','warning-baseline-modelarithmetic','nine-variable-ipra-stages-3-5-author-audit','004','6af6ec8ca3ec1f14663f214b53f728a9a88b7b415ea8e68b769b27b197e44f0d',5),('RATIO_WARNING','warning-baseline-ratiobounds','nine-variable-ipra-stages-6-9-author-observation','006','442a964429a3898a6110137b53268c9b370c60bb7de38899565d2885dd865c1b',13)]
plan=j(PLAN);result=j(P/'observations/attempt03/result.json');baselines=[];tests=[]
for label,folder,review,num,digest,idx in items:
 baseline=P/folder/'baseline.txt';receipt=D/'reviews'/review/'author/receipts'/(num+'.json');h=j(receipt);stage=result['stages'][idx-1];module=names[label+'_MODULE'];source=names[label+'_SOURCE'];path=next(a for a in stage['command'] if a.endswith('.lean'));obs=P/'observations/attempt03';log=(obs/f'stage-{idx:03}.stdout').read_text()+(obs/f'stage-{idx:03}.stderr').read_text();raw=baseline.read_text()
 assert sha(baseline)==digest and h['status']=='PASS' and h['module']==module and h['source_sha256']==source==stage['source_sha256']==plan['sources'][module]['sha256'] and h['warning_policy']['baseline_sha256']==digest
 assert log.replace(path,'<SOURCE>')==raw and raw.count('warning:')==(4 if idx==13 else 3) and not re.search(r'\b(?:error|sorryAx)\b',raw)
 baselines.append(raw);tests.append((module,source,log,path))
for i,(mod,src,log,path) in enumerate(tests):
 assert f(mod,src,log,path,*baselines)
 for msg in [log+'warning(lean.x): x\n',log+'error(lean.x): x\n',log+'sorryAx\n',log.replace('warning:','warning(x):',1),'\n'.join(log.splitlines()[1:])]:assert not f(mod,src,msg,path,*baselines)
 assert not f('Other',src,log,path,*baselines) and not f(mod,'0'*64,log,path,*baselines)
 for j,(_,_,other,otherpath) in enumerate(tests):
  if i!=j:assert not f(mod,src,other,otherpath,*baselines)
assert f('Other','x','clean','/tmp/source',*baselines) and not f('Other','x','warning: x','/tmp/source',*baselines)
code=S.read_text();assert all(('sha('+x+')==EXPECTED_'+x) in code for x in ('WARNING_RECEIPT','WARNING_BASE','MODEL_WARNING_RECEIPT','MODEL_WARNING_BASE','RATIO_WARNING_RECEIPT','RATIO_WARNING_BASE'))
wrapper=W.read_text();assert 'observations/outer-attempt04' in wrapper and 'observations/attempt04' in wrapper and 'sys.exit(p.returncode)' in wrapper and sha(S) in wrapper
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ten-positive-80-rebuild-v5-prelaunch-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS v6 three exact historical module/source/full-log policies; 6 cross-swaps and diagnostic/log/hash mutations rejected')
print('attempt04 wrapper pinned, 127 plan and inherited v5/v4/v3 guards verified; no Lean or rebuild invocation')
