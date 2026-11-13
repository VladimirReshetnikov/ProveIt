#!/usr/bin/env python3
"""Prepare a value-only guard using two successful children of a failed run."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
check = here.parent / 'current14-carrier65-dag-value-retry-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65DAGValue.lean'
shutil.copyfile(here / 'Current14Carrier65DAGValue.lean', src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65DAGValue',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
prior = here.parent / 'current14-carrier65-dag-check'
state = prior / 'attempt01/state.json'
outer = prior / 'attempt01/outer-result.json'
audit = d / 'reviews/current14-carrier65-dag-failure-independent/check.py'
provider = Path('/tmp/current14-carrier65-dag-check-20261110')
old = (prior / 'run.py').read_text()
old = old.replace('/tmp/nine-sharing-sign17-readable-current14-endpoint-20261110', str(provider))
old = old.replace("OUT=Path('/tmp/current14-carrier65-dag-check-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-dag-value-retry-20261110')", 1)
start = old.index("STATE=D/'research/nine-sharing-sign17-readable-current14-endpoint-check/attempt01/state.json'")
end = old.index('\nroots=', start)
old = old[:start] + ("STATE=D/'research/current14-carrier65-dag-check/attempt01/state.json';"
                     "OUTER=STATE.parent/'outer-result.json';"
                     "AUDIT=D/'reviews/current14-carrier65-dag-failure-independent/check.py'") + old[end:]
start = old.index('need(sha(STATE)==')
end = old.index('for row in base[\'rows\']:', start)
old = old[:start] + f'''need(sha(STATE)=='{sha(state)}','failed parent state pin')
need(sha(OUTER)=='{sha(outer)}' and json.loads(OUTER.read_text())['outer_exit_code']==1,'failed outer pin')
need(sha(AUDIT)=='{sha(audit)}','independent failure audit pin')
base=json.loads(STATE.read_text());need(base['status']=='FAILED' and len(base['rows'])==3,'failed parent status')
failed=base['rows'][-1]
need(failed['module']=='Current14Carrier65DAGValue' and failed['compile']['exit']==1,'failed final child')
need(not (BASE/'lib/DiophantineConsistency/Current14Carrier65DAGValue.olean').exists(),'failed final object absent')
need(sha(BASE/'Current14Carrier65DAGValue-compile.txt')==failed['compile']['log_sha256'],'failure log pin')
base['rows']=base['rows'][:2]
need([r['module'] for r in base['rows']]==['ArithmeticDAG','Current14Carrier65DAGCore'],'successful children only')
provider_init=base['rows'][0]['dependencies']['Init'];need(all(r['dependencies'].get('Init')==provider_init for r in base['rows']),'provider Init consistency')
need(provider_init['realpath']==str((TOOL/'Init.olean').resolve()) and provider_init['sha256']=='d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e','provider Init pin')
''' + old[end:]
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("need(len(entries)==3,'stage count')", "need(len(entries)==1,'stage count')")
start = old.index("draft=D/'research/current14-carrier65-dag-draft/Current14Carrier65DAG.lean'")
end = old.index('provider_names={r[\'module\']:r for r in base[\'rows\']}', start)
carrier = provider / 'lib/DiophantineConsistency/Carrier65.olean'
old = old[:start] + f'''draft=D/'research/current14-carrier65-dag-value-retry-draft/Current14Carrier65DAGValue.lean'
need(sha(draft)=='{sha(here / 'Current14Carrier65DAGValue.lean')}','retry source pin')
need(sha(P/'src/DiophantineConsistency/Current14Carrier65DAGValue.lean')==sha(draft),'retry source copy')
carrier_pin={{'realpath':{str(carrier.resolve())!r},'sha256':{sha(carrier)!r}}}
carrier=BASE/'lib/DiophantineConsistency/Carrier65.olean'
need(carrier.is_file() and str(carrier.resolve())==carrier_pin['realpath'] and sha(carrier)==carrier_pin['sha256'],'carrier direct pin')
''' + old[end:]
old = old.replace("m in package_pins or m=='DiophantineConsistency.Carrier65' or m.split('.')[-1] in names[:names.index(n)]",
                  "m=='DiophantineConsistency.Carrier65' or m.split('.')[-1] in provider_names or m.split('.')[-1] in names[:names.index(n)]")
old = old.replace("if mod in package_pins:\n    expected=package_pins[mod]['sha256'];path=Path(package_pins[mod]['realpath'])\n   elif mod=='DiophantineConsistency.Carrier65':",
                  "if mod=='DiophantineConsistency.Carrier65':")
old = old.replace("else:\n    prior=[x for x in state['rows'][:-1] if x['module']==depname];need(len(prior)==1,'local producer '+depname);expected=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(depname+'.olean')",
                  "elif depname in provider_names:\n    expected=provider_names[depname]['object_sha256'];path=BASE/'lib/DiophantineConsistency'/(depname+'.olean')\n   else:\n    prior=[x for x in state['rows'][:-1] if x['module']==depname];need(len(prior)==1,'local producer '+depname);expected=prior[0]['object_sha256'];path=OUT/'lib/DiophantineConsistency'/(depname+'.olean')")
old = old.replace('PASS current14 Carrier65 circuit and semantic bridge', 'PASS current14 Carrier65 semantic bridge using successful children of failed parent')
(check / 'run.py').write_text(old)
print('Prepared retry guard; no Lean invoked.')
