#!/usr/bin/env python3
"""Generate a guard using the audited successful child of a failed run."""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
draft = Path(__file__).resolve().parent
research = draft.parent
check = research / 'nine-sharing-sign25-endpoint-wrappers-check'
original = research / 'nine-sharing-sign25-endpoint-check'
assert not check.exists(), 'refusing to overwrite wrapper packet'
check.mkdir()
(check / 'src/DiophantineConsistency').mkdir(parents=True)
shutil.copyfile(original / 'framework-survey.py', check / 'framework-survey.py')
names = ['Sign25DirectNoAliasStandard', 'Sign25DirectNoAliasTranslated']
rows = []
for name in names:
    src = draft / (name + '.lean')
    shutil.copyfile(src, check / 'src/DiophantineConsistency' / src.name)
    data = src.read_bytes()
    rows.append({'module': 'DiophantineConsistency.' + name,
                 'source': str(src.relative_to(research.parents[2])),
                 'source_sha256': hashlib.sha256(data).hexdigest(),
                 'imports': re.findall(r'^import ([A-Za-z0-9_.]+)$', data.decode(), re.M)})
manifest = (json.dumps({'rows': rows}, indent=2) + '\n').encode()
(check / 'source-manifest.json').write_bytes(manifest)
runner = (original / 'run.py').read_text()
def replace_once(old, new):
    global runner
    assert runner.count(old) == 1, ('replacement count', old)
    runner = runner.replace(old, new)
replace_once('c5de8b265cfbb4fbc75bd903f67e411dff8798d8144fd4d5fdfbafff79e10dd8',
             hashlib.sha256(manifest).hexdigest())
replace_once('/tmp/nine-sharing-sign25-concrete-polynomial-bridge-check-20261106',
             '/tmp/nine-sharing-sign25-endpoint-no-alias-20261109')
replace_once('/tmp/nine-sharing-sign25-endpoint-check-20261106',
             '/tmp/nine-sharing-sign25-endpoint-wrappers-20261109')
replace_once('research/nine-sharing-sign25-concrete-polynomial-bridge-check/attempt01/state.json',
             'research/nine-sharing-sign25-endpoint-no-alias-check/attempt01/state.json')
replace_once('56e28709b696263dae760913e55db17a216776a2c21ca4f43fe5685c45183094',
             '0e775b75519c40e1d4410cc8fea42d003c9733c4233a81e35b90b3bcb2384361')
replace_once("base['status']=='PASS' and len(base['rows'])==1",
             "base['status']=='FAILED' and len(base['rows'])==2 and base['rows'][0]['module']=='Sign25DirectNoAliasNative' and base['rows'][1]['module']=='Sign25DirectNoAliasStandard' and base['rows'][1]['compile']['exit']==-6")
assert runner.count("for row in base['rows']:") == 2
runner = runner.replace("for row in base['rows']:", "for row in base['rows'][:1]:")
replace_once("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard','Sign25DirectTranslated'",
             ','.join(repr(n) for n in names))
replace_once("'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard'",
             repr(names[0]))
replace_once("if local=='Sign25DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign25DirectPolynomialBridge.olean'",
             "if local=='Sign25DirectNoAliasNative':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign25DirectNoAliasNative.olean'")
anchor = "need(sha(P/'source-manifest.json')=="
assert runner.count(anchor) == 1
extra = """need(sha(D/'research/nine-sharing-sign25-endpoint-no-alias-check/attempt01/outer-result.json')=='f77517020174b6c9235806be18fb814532e5ccacc3622b211b212e2721e05bd0','partial outer record')
need(sha(D/'reviews/nine-sharing-sign25-endpoint-no-alias-terminal-independent/check.py')=='3efa7f2442a8855d6f5b9df2ada203bd05b35de0eb162609bcbf4e80d268f6ac','partial audit checker')
need(json.loads((D/'research/nine-sharing-sign25-endpoint-no-alias-check/attempt01/outer-result.json').read_text())['outer_exit_code']==1,'partial outer status')
"""
runner = runner.replace(anchor, extra + anchor)
runner = runner.replace('Bounded sign26 direct endpoint diagnostic', 'Bounded sign25 wrappers over an audited partial native producer')
runner = runner.replace('PASS sign25 direct endpoint diagnostic', 'PASS sign25 wrappers over an audited partial native producer')
(check / 'run.py').write_text(runner)
(check / 'README.md').write_text('''# Sign25 wrappers over an audited partial native producer\n\nTwo candidate wrapper stages use the native object from a previously failed\nouter run whose native child compiled and was independently audited. The runner\nrechecks that exact partial producer, its source, direct guards, logs, object\nand overlays, with same resource limits and fresh output. No successful full\nproducer postflight is claimed. No-Lean preflight and independent review are\nrequired; Lean may run only on an assigned slot.\n''')
print(json.dumps({'manifest_sha256': hashlib.sha256(manifest).hexdigest(),
                  'runner_sha256': hashlib.sha256(runner.encode()).hexdigest(),
                  'stages': names}, sort_keys=True))
