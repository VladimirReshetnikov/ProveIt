#!/usr/bin/env python3
"""Prepare staged actual-Q degree replay/assembly without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-q-fields-check'
check = here.parent / 'current14-carrier65-q-actual-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
sources = [here.parent / 'current14-carrier65-q-cancel-draft/Current14Carrier65QCancel.lean',
           here.parent / 'current14-carrier65-q-degree-retry02-draft/Current14Carrier65QDegree.lean',
           here / 'Current14Carrier65QActual.lean']
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = []
for source in sources:
    src = srcdir / source.name
    shutil.copyfile(source, src)
    rows.append({'module': 'DiophantineConsistency.' + src.stem,
                 'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
                 'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)})
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
provider = Path('/tmp/current14-carrier65-q-fields-20261110')
state = previous / 'attempt01/state.json'
outer = state.parent / 'outer-result.json'
audit = d / 'reviews/current14-carrier65-q-fields-terminal-independent/check.py'
old = (previous / 'run.py').read_text()
old = old.replace("BASE=Path('/tmp/current14-carrier65-q-inputs-retry-20261110')", f"BASE=Path({str(provider)!r})")
old = old.replace("OUT=Path('/tmp/current14-carrier65-q-fields-20261110')", "OUT=Path('/tmp/current14-carrier65-q-actual-20261110')")
start = old.index("STATE=D/'research/current14-carrier65-q-inputs-retry-check/attempt01/state.json'")
end = old.index('\nroots=', start)
old = old[:start] + ("STATE=D/'research/current14-carrier65-q-fields-check/attempt01/state.json';"
                     "OUTER=STATE.parent/'outer-result.json';"
                     "AUDIT=D/'reviews/current14-carrier65-q-fields-terminal-independent/check.py'") + old[end:]
old = re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'", f"need(sha(STATE)=='{sha(state)}'", old)
old = re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'", f"need(sha(OUTER)=='{sha(outer)}'", old)
old = re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'", f"need(sha(AUDIT)=='{sha(audit)}'", old)
old = old.replace("base['rows'][-1]['module']=='Current14Carrier65QInputs'", "base['rows'][-1]['module']=='Current14Carrier65QFields'")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("need(len(entries)==1,'stage count')", "need(len(entries)==3,'stage count')")
start = old.index("draft=D/'research/current14-carrier65-q-fields-draft/Current14Carrier65QFields.lean'")
end = old.index('provider_names={r[\'module\']:r for r in base[\'rows\']}', start)
weighted = provider / 'lib/DiophantineConsistency/WeightedExpressionDegree.olean'
pkg = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
vec = pkg / 'Mathlib/Data/Fin/VecNotation.olean'
fincases = pkg / 'Mathlib/Tactic/FinCases.olean'
carrier = provider / 'lib/DiophantineConsistency/Carrier65.olean'
pins = {name: {'realpath': str(path.resolve()), 'sha256': sha(path)} for name,path in [
    ('DiophantineConsistency.WeightedExpressionDegree',weighted),
    ('DiophantineConsistency.Carrier65',carrier),
    ('Mathlib.Data.Fin.VecNotation',vec),('Mathlib.Tactic.FinCases',fincases)]}
cancelstate = here.parent / 'current14-carrier65-q-cancel-check/attempt01/state.json'
cancelouter = cancelstate.parent / 'outer-result.json'
cancelaudit = d / 'reviews/current14-carrier65-q-cancel-terminal-independent/check.py'
degreestate = here.parent / 'current14-carrier65-q-degree-retry02-check/attempt01/state.json'
degreeouter = degreestate.parent / 'outer-result.json'
degreeaudit = d / 'reviews/current14-carrier65-q-degree-retry02-terminal-independent/check.py'
extra = f'''replay_sources={[(str(s), sha(s)) for s in sources]!r}
for i,(path,digest) in enumerate(replay_sources):
 need(sha(path)==digest and sha(P/'src/DiophantineConsistency'/Path(path).name)==digest,'replay source '+str(i))
for i,(state_path,outer_path,audit_path,state_hash,outer_hash,audit_hash) in enumerate({[(str(cancelstate),str(cancelouter),str(cancelaudit),sha(cancelstate),sha(cancelouter),sha(cancelaudit)),(str(degreestate),str(degreeouter),str(degreeaudit),sha(degreestate),sha(degreeouter),sha(degreeaudit))]!r}):
 replay=json.loads(Path(state_path).read_text())
 need(sha(state_path)==state_hash and replay['status']=='PASS','replay provider state')
 need(len(replay['rows'])==1 and replay['rows'][0]['source_sha256']==replay_sources[i][1] and replay['rows'][0]['compile']['exit']==0,'audited replay source '+str(i))
 need(sha(outer_path)==outer_hash and json.loads(Path(outer_path).read_text())['outer_exit_code']==0,'replay provider outer')
 need(sha(audit_path)==audit_hash,'replay terminal audit')
extra_pins={pins!r}
for mod,rec in extra_pins.items():
 candidates=[r/(mod.replace('.','/')+'.olean') for r in [BASE/'lib',SPHERE,MODEL,PKG,TOOL] if (r/(mod.replace('.','/')+'.olean')).is_file()]
 need(candidates and str(candidates[0].resolve())==rec['realpath'] and sha(candidates[0])==rec['sha256'],'ingredient point '+mod)
'''
old = old[:start] + extra + old[end:]
old = old.replace("m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or", "m in extra_pins or")
start = old.index("if mod=='DiophantineConsistency.CurrentEquationSyntax2011':")
end = old.index("   elif depname in provider_names:", start)
old = old[:start] + "if mod in extra_pins:expected=extra_pins[mod]['sha256'];path=Path(extra_pins[mod]['realpath'])\n" + old[end:]
old = old.replace('PASS current14 Q field bindings and input bounds', 'PASS current14 actual Q degree upper bound')
(check / 'run.py').write_text(old)
print('Prepared actual Q degree replay/assembly; no Lean invoked.')
