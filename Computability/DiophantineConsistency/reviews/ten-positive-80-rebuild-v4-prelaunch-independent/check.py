#!/usr/bin/env python3
"""Execute only the extracted pure warning predicate and independent preflight checks."""
from pathlib import Path
from hashlib import sha256
import ast,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=D/'research/ten-positive-80-coherent-rebuild';S=P/'run-v4.py';BASE=P/'warning-baseline-pigeonhole/baseline.txt';REC=D/'reviews/nine-variable-ipra-stages-6-9-author-observation/author/receipts/008.json';ATT=P/'observations/attempt01';PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(S)=='6065f48448b7956355ad277e481047ec88cfea7ba09d9de99fb6542513398ca9' and sha(BASE)=='1848875f336080bc59033d40b66a69d97cc9d1e90904d4f0d559b998fff7de92' and sha(REC)=='86cea8817e9e52731cc61a6b3b983a0635d96cc8dba13ea1743ae6bb82133d94'
tree=ast.parse(S.read_text());names={n.targets[0].id:ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in ('WARNING_MODULE','WARNING_SOURCE')}
assert names=={'WARNING_MODULE':'DiophantineConsistency.ArithmeticPellPigeonhole','WARNING_SOURCE':'ebdbc22e239754f8f686be6971742d1b02560c9ffa35d464d2aecc323370765c'}
fns=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='diagnostics_allowed'];assert len(fns)==1
env={'re':re,**names};exec(compile(ast.Module(body=fns,type_ignores=[]),str(S),'exec'),env);fn=env['diagnostics_allowed'];module=names['WARNING_MODULE'];source=names['WARNING_SOURCE'];baseline=BASE.read_text();assert baseline.count('warning:')==3 and not re.search(r'\b(?:error|sorryAx)\b',baseline)
r=json.loads((ATT/'result.json').read_text());stage=r['stages'][2];path=next(x for x in stage['command'] if x.endswith('.lean'));log=(ATT/'stage-003.stdout').read_text()+(ATT/'stage-003.stderr').read_text();assert log.replace(path,'<SOURCE>')==baseline
hist=json.loads(REC.read_text());plan=json.loads(PLAN.read_text());assert hist['status']=='PASS' and hist['module']==module and hist['source_sha256']==hist['warning_policy']['source_sha256']==source and hist['warning_policy']['baseline_sha256']==sha(BASE) and plan['sources'][module]['sha256']==source
assert fn(module,source,log,path,baseline) and fn('anything','hash','proof complete',path,baseline)
mutants=[('wrong module','X',source,log),('wrong source',module,'0'*64,log),('extra warning',module,source,log+'warning(lean.extra): x\n'),('error',module,source,log+'error: x\n'),('sorry',module,source,log+'sorryAx\n'),('changed byte',module,source,log.replace('deprecated','changed',1)),('missing line',module,source,'\n'.join(log.splitlines()[1:])),('non-target diagnostic','X','0'*64,'warning: x')]
for label,n,h,msg in mutants:assert not fn(n,h,msg,path,baseline),label
code=S.read_text();assert "sha(WARNING_RECEIPT)==EXPECTED_WARNING_RECEIPT and sha(WARNING_BASE)==EXPECTED_WARNING_BASE" in code and "text=so.read_text()+se.read_text()" in code and "'warning_exception'" in code
subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ten-positive-80-rebuild-v3-prelaunch-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
print('PASS exact actual policy: retained attempt01 log accepted; 8 independent wrong-source/module/log/diagnostic mutations rejected')
print('baseline and receipt hashes pinned; policy, source, plan agree; prior v3 guard/127 plan check passes')
print('No Lean/rebuild invocation. Stage status, outer exit, full closure and external binding boundaries remain.')
