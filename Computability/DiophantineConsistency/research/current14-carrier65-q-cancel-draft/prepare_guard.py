#!/usr/bin/env python3
"""Prepare the small cancellation ingredient guard without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-dag-expression-check'
check = here.parent / 'current14-carrier65-q-cancel-check'
srcdir = check / 'src/DiophantineConsistency'
srcdir.mkdir(parents=True, exist_ok=True)
src = srcdir / 'Current14Carrier65QCancel.lean'
shutil.copyfile(here / src.name, src)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows = [{'module': 'DiophantineConsistency.Current14Carrier65QCancel',
         'source': str(src.relative_to(repo)), 'source_sha256': sha(src),
         'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', src.read_text(), re.M)}]
manifest = check / 'source-manifest.json'
manifest.write_text(json.dumps({'rows': rows}, indent=2) + '\n')
old = (previous / 'run.py').read_text()
old = old.replace("OUT=Path('/tmp/current14-carrier65-dag-expression-20261110')",
                  "OUT=Path('/tmp/current14-carrier65-q-cancel-20261110')")
old = re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'", f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'", old)
old = old.replace("draft=D/'research/current14-carrier65-dag-expression-draft/Current14Carrier65DAGExpression.lean'",
                  "draft=D/'research/current14-carrier65-q-cancel-draft/Current14Carrier65QCancel.lean'")
old = re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'", f"need(sha(draft)=='{sha(here / src.name)}'", old)
old = old.replace("P/'src/DiophantineConsistency/Current14Carrier65DAGExpression.lean'", "P/'src/DiophantineConsistency/Current14Carrier65QCancel.lean'")
carrier = Path('/tmp/current14-carrier65-dag-value-congr-diagnostic-20261110/lib/DiophantineConsistency/Carrier65.olean')
pin = {'realpath': str(carrier.resolve()), 'sha256': sha(carrier)}
needle = "provider_names={r['module']:r for r in base['rows']}"
extra = f'''carrier_pin={pin!r}
carrier=BASE/'lib/DiophantineConsistency/Carrier65.olean'
need(carrier.is_file() and str(carrier.resolve())==carrier_pin['realpath'] and sha(carrier)==carrier_pin['sha256'],'carrier point pin')
'''
assert needle in old
old = old.replace(needle, extra + needle)
old = old.replace("m=='DiophantineConsistency.CurrentEquationSyntax2011' or", "m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or")
needle = "if mod=='DiophantineConsistency.CurrentEquationSyntax2011':expected=syntax_pin['sha256'];path=Path(syntax_pin['realpath'])"
assert needle in old
old = old.replace(needle, needle + "\n   elif mod=='DiophantineConsistency.Carrier65':expected=carrier_pin['sha256'];path=Path(carrier_pin['realpath'])")
old = old.replace('PASS current14 65-gate circuit expression composition', 'PASS current14 Q cancellation ingredient')
old = old.replace('Audited semantic provider and expression point object; no Lean theorem or complete transitive import trace.',
                  'Point-pinned Carrier65 ingredient; no Lean theorem or complete transitive import trace.')
(check / 'run.py').write_text(old)
print('Prepared Q cancellation ingredient; no Lean invoked.')
