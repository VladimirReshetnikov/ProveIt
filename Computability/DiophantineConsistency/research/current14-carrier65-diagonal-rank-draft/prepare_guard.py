#!/usr/bin/env python3
"""Prepare diagonal rank field-binding stages without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-q-fields-check'
check = here.parent / 'current14-carrier65-diagonal-rank-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
sources = [here.parent / 'current14-carrier65-diagonal-degree-retry02-draft/Current14Carrier65DiagonalDegree.lean',
           here / 'Current14Carrier65DiagonalRank.lean']
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
provider = Path('/tmp/current14-carrier65-other-fields-20261110')
state = here.parent / 'current14-carrier65-other-fields-check/attempt01/state.json'
outer = state.parent / 'outer-result.json'
audit = d / 'reviews/current14-carrier65-other-fields-terminal-independent/check.py'
old = (previous / 'run.py').read_text()
old = old.replace("BASE=Path('/tmp/current14-carrier65-q-inputs-retry-20261110')", f"BASE=Path({str(provider)!r})")
old = old.replace("OUT=Path('/tmp/current14-carrier65-q-fields-20261110')", "OUT=Path('/tmp/current14-carrier65-diagonal-rank-20261110')")
start = old.index("STATE=D/'research/current14-carrier65-q-inputs-retry-check/attempt01/state.json'")
end = old.index('\nroots=', start)
old = old[:start] + ("STATE=D/'research/current14-carrier65-other-fields-check/attempt01/state.json';"
                     "OUTER=STATE.parent/'outer-result.json';"
                     "AUDIT=D/'reviews/current14-carrier65-other-fields-terminal-independent/check.py'") + old[end:]
old = re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'", f"need(sha(STATE)=='{sha(state)}'", old)
old = re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'", f"need(sha(OUTER)=='{sha(outer)}'", old)
old = re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'", f"need(sha(AUDIT)=='{sha(audit)}'", old)
old = old.replace("base['rows'][-1]['module']=='Current14Carrier65QInputs'", "base['rows'][-1]['module']=='Current14Carrier65OtherFields'")
old = old.replace("len(base['rows'])==1 and base['rows'][-1]['module']=='Current14Carrier65OtherFields'",
                  "len(base['rows'])==2 and base['rows'][-1]['module']=='Current14Carrier65OtherFields'")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("need(len(entries)==1,'stage count')", "need(len(entries)==2,'stage count')")
start = old.index("draft=D/'research/current14-carrier65-q-fields-draft/Current14Carrier65QFields.lean'")
end = old.index('provider_names={r[\'module\']:r for r in base[\'rows\']}', start)
qinputs = provider / 'lib/DiophantineConsistency/Sign17UnivariateDegreeProbe.olean'
carrier = provider / 'lib/DiophantineConsistency/Carrier65.olean'
pins = {name: {'realpath': str(path.resolve()), 'sha256': sha(path)} for name,path in [
    ('DiophantineConsistency.Sign17UnivariateDegreeProbe',qinputs),('DiophantineConsistency.Carrier65',carrier)]}
replay = here.parent / 'current14-carrier65-diagonal-degree-retry02-check/attempt01/state.json'
replay_outer = replay.parent / 'outer-result.json'
replay_audit = d / 'reviews/current14-carrier65-diagonal-degree-retry02-terminal-independent/check.py'
extra = f'''replay_source=Path({str(sources[0])!r})
need(sha(replay_source)=='{sha(sources[0])}' and sha(P/'src/DiophantineConsistency/Current14Carrier65DiagonalDegree.lean')==sha(replay_source),'audited Q-fields replay source')
need(sha(Path({str(replay)!r}))=='{sha(replay)}','Q-fields replay state')
replay=json.loads(Path({str(replay)!r}).read_text())
need(replay['status']=='PASS' and len(replay['rows'])==1 and replay['rows'][0]['source_sha256']==sha(replay_source) and replay['rows'][0]['compile']['exit']==0,'Q-fields replay source and stage')
need(sha(Path({str(replay_outer)!r}))=='{sha(replay_outer)}' and json.loads(Path({str(replay_outer)!r}).read_text())['outer_exit_code']==0,'Q-fields replay outer')
need(sha(Path({str(replay_audit)!r}))=='{sha(replay_audit)}','Q-fields replay audit')
draft=Path({str(sources[1])!r})
need(sha(draft)=='{sha(sources[1])}' and sha(P/'src/DiophantineConsistency/Current14Carrier65DiagonalRank.lean')==sha(draft),'other fields source')
extra_pins={pins!r}
for mod,rec in extra_pins.items():
 path=BASE/'lib'/(mod.replace('.','/')+'.olean')
 need(path.is_file() and str(path.resolve())==rec['realpath'] and sha(path)==rec['sha256'],'ingredient point '+mod)
'''
old = old[:start] + extra + old[end:]
old = old.replace("m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or", "m in extra_pins or")
start = old.index("if mod=='DiophantineConsistency.CurrentEquationSyntax2011':")
end = old.index("   elif depname in provider_names:", start)
old = old[:start] + "if mod in extra_pins:expected=extra_pins[mod]['sha256'];path=Path(extra_pins[mod]['realpath'])\n" + old[end:]
old = old.replace('PASS current14 Q field bindings and input bounds', 'PASS current14 actual diagonal rank upper bound')
(check / 'run.py').write_text(old)
print('Prepared actual diagonal rank upper bound; no Lean invoked.')
