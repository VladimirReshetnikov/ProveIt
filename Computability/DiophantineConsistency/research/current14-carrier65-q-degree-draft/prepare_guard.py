#!/usr/bin/env python3
"""Prepare generic Q degree ingredient guard without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-q-cancel-check'
check = here.parent / 'current14-carrier65-q-degree-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65QDegree.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65QDegree',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-q-cancel-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-q-degree-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-q-cancel-draft/Current14Carrier65QCancel.lean'",
                  "draft=D/'research/current14-carrier65-q-degree-draft/Current14Carrier65QDegree.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
old = old.replace("P/'src/DiophantineConsistency/Current14Carrier65QCancel.lean'", "P/'src/DiophantineConsistency/Current14Carrier65QDegree.lean'")
provider = Path('/tmp/current14-carrier65-dag-value-congr-diagnostic-20261110/lib')
weighted = provider / 'DiophantineConsistency/WeightedExpressionDegree.olean'
vec = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Data/Fin/VecNotation.olean')
pins = {'DiophantineConsistency.WeightedExpressionDegree': {'realpath': str(weighted.resolve()), 'sha256': sha(weighted)},
        'Mathlib.Data.Fin.VecNotation': {'realpath': str(vec.resolve()), 'sha256': sha(vec)}}
needle = "provider_names={r['module']:r for r in base['rows']}"
extra = f'''extra_pins={pins!r}
for mod,rec in extra_pins.items():
 candidates=[r/(mod.replace('.','/')+'.olean') for r in [BASE/'lib',SPHERE,MODEL,PKG,TOOL] if (r/(mod.replace('.','/')+'.olean')).is_file()]
 need(candidates and str(candidates[0].resolve())==rec['realpath'] and sha(candidates[0])==rec['sha256'],'ingredient point '+mod)
'''
assert needle in old
old = old.replace(needle, extra + needle)
old = old.replace("m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or",
                  "m in extra_pins or m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or")
needle = "if mod=='DiophantineConsistency.CurrentEquationSyntax2011':expected=syntax_pin['sha256'];path=Path(syntax_pin['realpath'])"
assert needle in old
old = old.replace(needle, "if mod in extra_pins:expected=extra_pins[mod]['sha256'];path=Path(extra_pins[mod]['realpath'])\n   el" + needle)
old = old.replace('PASS current14 Q cancellation ingredient', 'PASS generic current14 Q degree ingredient')
(check / 'run.py').write_text(old)
print('Prepared Q degree ingredient; no Lean invoked.')
