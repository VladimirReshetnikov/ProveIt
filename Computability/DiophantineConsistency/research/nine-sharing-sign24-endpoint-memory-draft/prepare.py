#!/usr/bin/env python3
"""Adapt the audited sign25 endpoint guard to the checked sign24 bridge."""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
draft = Path(__file__).resolve().parent
research = draft.parent
old = research/'nine-sharing-sign25-endpoint-memory-retry-check'
check = research/'nine-sharing-sign24-endpoint-memory-check'
assert not check.exists(), 'refusing to overwrite endpoint packet'
check.mkdir()
(check/'src/DiophantineConsistency').mkdir(parents=True)
names = ['Sign24DirectNoAliasNative', 'Sign24DirectNoAliasStandard', 'Sign24DirectNoAliasTranslated']
rows = []
for name in names:
    src = draft/(name+'.lean')
    shutil.copyfile(src, check/'src/DiophantineConsistency'/src.name)
    data = src.read_bytes()
    rows.append({'module':'DiophantineConsistency.'+name,
                 'source':str(src.relative_to(research.parents[2])),
                 'source_sha256':hashlib.sha256(data).hexdigest(),
                 'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)})
manifest=(json.dumps({'rows':rows},indent=2)+'\n').encode()
(check/'source-manifest.json').write_bytes(manifest)
old_base='/tmp/nine-sharing-sign25-concrete-polynomial-bridge-check-20261106'
new_base='/tmp/nine-sharing-sign24-concrete-bridge-memory-retry-20261109'
survey=(old/'framework-survey.py').read_text()
assert survey.count(old_base)==1
survey=survey.replace(old_base,new_base)
(check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def replace_once(a,b):
    global runner
    assert runner.count(a)==1, ('replacement count',a)
    runner=runner.replace(a,b)
replace_once(old_base,new_base)
replace_once('/tmp/nine-sharing-sign25-endpoint-memory-retry-20261109',
             '/tmp/nine-sharing-sign24-endpoint-memory-20261109')
replace_once('research/nine-sharing-sign25-concrete-polynomial-bridge-check/attempt01/state.json',
             'research/nine-sharing-sign24-concrete-bridge-memory-retry-check/attempt01/state.json')
replace_once('56e28709b696263dae760913e55db17a216776a2c21ca4f43fe5685c45183094',
             'cabef9b9e1fb3291b298cd4f46ad820ecadf3918eb3d35253b8dbe048c36cddc')
replace_once('1903addd6116b80b8b92e2ac04730e8abae76db7d5dea82b397695e456539f65',
             hashlib.sha256(manifest).hexdigest())
replace_once('5f2e6e8b70dc55c3ddca7825a3f2e4f265e416b6d009b60594279914dce0390c',
             hashlib.sha256(survey.encode()).hexdigest())
assert runner.count('Sign25DirectNoAlias') > 0 and runner.count('Sign25DirectPolynomialBridge') > 0
runner=runner.replace('Sign25DirectNoAlias','Sign24DirectNoAlias')
runner=runner.replace('Sign25DirectPolynomialBridge','Sign24DirectPolynomialBridge')
runner=runner.replace('Bounded sign25 memory-limit endpoint retry', 'Bounded sign24 memory-limit endpoint attempt')
runner=runner.replace('PASS sign25 memory-limit endpoint retry', 'PASS sign24 memory-limit endpoint attempt')
anchor="need(sha(P/'source-manifest.json')=="
assert runner.count(anchor)==1
extra="""need(sha(D/'research/nine-sharing-sign24-concrete-bridge-memory-retry-check/attempt01/outer-result.json')=='8cd9eac76f5a3b196511327079ba1e3a2b2d8ec23769b242cd693fc867c106d8','bridge outer record')
need(sha(D/'reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py')=='c8854f8e0ebf1e998192738f75119fbc1796b114a4f7fab96279d88686a04d87','bridge terminal audit checker')
need(json.loads((D/'research/nine-sharing-sign24-concrete-bridge-memory-retry-check/attempt01/outer-result.json').read_text())['outer_exit_code']==0,'bridge outer status')
"""
runner=runner.replace(anchor,extra+anchor)
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign24 direct iPRA endpoint guarded candidate\n\nThree source-only stages adapt the checked sign25 no-alias native, standard\nand translated endpoints to the audited sign24 concrete bridge. The guard\nchecks the sign24 bridge state, source, object, logs, direct guards, overlays\nand numeric outer-exit record; its independent terminal audit checker is\npinned. Lean uses the scoped `-M3600` limit with unchanged 4 GiB sampled RSS,\n10 GiB host-memory floor, 120-second timeout and disk guards. No endpoint is\nclaimed until the bounded run and independent terminal audit pass.\n''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                  'framework_survey_sha256':hashlib.sha256(survey.encode()).hexdigest()},sort_keys=True))
