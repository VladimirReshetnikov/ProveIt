#!/usr/bin/env python3
"""Prepare the sign22 degree client with an audited expression provider."""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
draft=Path(__file__).resolve().parent
research=draft.parent
old=research/'nine-sharing-sign22-endpoint-check'
check=research/'nine-sharing-sign22-full-coeff-check'
assert not check.exists(), 'refusing to overwrite degree packet'
check.mkdir()
(check/'src/DiophantineConsistency').mkdir(parents=True)
for name in ('framework-survey.py',): shutil.copyfile(old/name,check/name)
shutil.copyfile(draft/'expression-survey.py',check/'expression-survey.py')
names=['Sign22LeadingRows','Sign22DiagonalDegree','Sign22AxisResidualDegree','Sign22SquareCoeffs','Sign22AxisCoeffLemmas','Sign22SeedCoefficient','Sign22DegreeLower']
rows=[]
for name in names:
    src=draft/(name+'.lean'); data=src.read_bytes()
    shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
    rows.append({'module':'DiophantineConsistency.'+name,
                 'source':str(src.relative_to(research.parents[2])),
                 'source_sha256':hashlib.sha256(data).hexdigest(),
                 'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)})
manifest=(json.dumps({'rows':rows},indent=2)+'\n').encode()
(check/'source-manifest.json').write_bytes(manifest)
runner=(old/'run.py').read_text()
def replace_once(a,b):
    global runner
    assert runner.count(a)==1, ('replacement count',a)
    runner=runner.replace(a,b)
replace_once('/tmp/nine-sharing-sign22-endpoint-check-20261109',
             '/tmp/nine-sharing-sign22-full-coeff-20261109')
replace_once('309dcb72ff0d767e0be2521ed5a7d88e58ce137449e603f15dca1a06f56e5200',
             hashlib.sha256(manifest).hexdigest())
replace_once("'Sign22DirectNoAliasNative','Sign22DirectNoAliasStandard','Sign22DirectNoAliasTranslated'",
             ','.join(repr(n) for n in names))
replace_once("'Sign22DirectNoAliasNative','Sign22DirectNoAliasStandard'",
             ','.join(repr(n) for n in names[:-1]))
runner=runner.replace('Bounded sign22 no-alias endpoint attempt','Bounded sign22 full coefficient lower-bound attempt')
runner=runner.replace('PASS sign22 no-alias endpoint attempt','PASS sign22 full coefficient lower-bound attempt')
runner=runner.replace('endpoint outcome depends on stage results', 'degree outcome depends on stage results')
survey_pin=hashlib.sha256((check/'expression-survey.py').read_bytes()).hexdigest()
anchor="check_external_syntax()\nneed(sha(D/"
assert runner.count(anchor)==1
survey="""def check_expression():
 need(sha(P/'expression-survey.py')=='SURVEY_PIN','expression survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'expression-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'expression survey');data=json.loads(r.stdout);need(data['status']=='PASS','expression status');return data
expression_data=check_expression()
""".replace('SURVEY_PIN',survey_pin)
runner=runner.replace(anchor,'check_external_syntax()\n'+survey+'need(sha(D/')
anchor="   elif local in framework['observed']:\n"
assert runner.count(anchor)==1
runner=runner.replace(anchor,"   elif local=='Sign22CurrentExpressionDef':\n    expected_hash=expression_data['object_sha256'];path=Path(expression_data['realpath'])\n"+anchor)
anchor=" check_external_syntax()\n state['status']='PASS'"
assert runner.count(anchor)==1
runner=runner.replace(anchor," check_external_syntax()\n need(check_expression()==expression_data,'expression final drift')\n state['status']='PASS'")
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign22 full coefficient lower-bound candidate\n\nSeven source-only stages replay four checked ingredients and propose\ntwo-row count composition, seed coefficient 272 and direct lower bound. The runner\nbinds the current expression definition to its audited producer, and uses the\nreviewed sign22 bridge environment as base. It retains `-M3600`, 4 GiB sampled\nRSS, 10 GiB host floor, timeout and disk guards. No theorem is claimed before\nLean and independent terminal audit; this is not an exact lower bound or a\nJSON/PDF binding.\n''')
print(json.dumps({'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                  'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'survey_sha256':survey_pin},sort_keys=True))
