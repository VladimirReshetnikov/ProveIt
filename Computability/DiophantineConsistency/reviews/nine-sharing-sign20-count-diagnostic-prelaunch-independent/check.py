#!/usr/bin/env python3
"""Review explicit failed-parent partial reuse for count diagnostic without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign20-count-diagnostic-check';draft=research/'nine-sharing-sign20-count-diagnostic-draft';parent=research/'nine-sharing-sign20-full-coeff-retry03-check/attempt01';sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
manifest=p/'source-manifest.json';assert sha(manifest)=='a55184b482074c83419cb51f044b00796e1d5e90d56601c098b99f68e07b7179';e,=json.loads(manifest.read_text())['rows'];assert e['module']=='DiophantineConsistency.Sign20CountDiagnostic' and e['imports']==['DiophantineConsistency.Sign20AxisCoeffLemmas']
src=p/'src/DiophantineConsistency/Sign20CountDiagnostic.lean';s=src.read_text();assert sha(src)==sha(draft/'Sign20CountDiagnostic.lean')==e['source_sha256'];assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'];assert s.count('List.count_cons, beq_iff_eq')==2 and s.count('set_option maxHeartbeats 4000000 in')==2
assert '(SharingSeed20Degree20.remainingResiduals p).count (n0 p) = 1' in s and '(SharingSeed20Degree20.remainingResiduals p).count (dc2 p) = 1' in s and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
o=json.loads((parent/'outer-result.json').read_text());base=json.loads((parent/'state.json').read_text());assert o['outer_session']==43491 and o['outer_exit_code']==1 and base['status']=='FAILED' and len(base['rows'])==6 and base['rows'][5]['compile']['exit']==1 and all(x['compile']['exit']==0 for x in base['rows'][:5])
runner=p/'run.py';assert sha(runner)=='0854fc80845b9aff925fa977b85029ecfde51ca0a7377e1397c125becb92c531';r=runner.read_text();assert "base['status']=='FAILED' and len(base['rows'])==6" in r and "['outer_exit_code']==1" in r and r.count("for row in base['rows'][:5]:")==2
assert "if local=='Sign20AxisCoeffLemmas':expected_hash=base['rows'][4]['object_sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "need(not OUT.exists(),'output exists')" in r
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-full-coeff-retry03-failure-independent/check.py')],check=True,capture_output=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'parent_outer_exit':1,'reused_successful_children':5,'scope':'count diagnostic source and failed-parent partial provider only; no Lean result or lower theorem'},indent=2,sort_keys=True))
