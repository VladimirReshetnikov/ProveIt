#!/usr/bin/env python3
"""Derive a separate-output diagnostic guard from the reviewed endpoint guard."""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
draft = Path(__file__).resolve().parent
research = draft.parent
check = research / 'nine-sharing-sign25-specialization-diagnostic-check'
original = research / 'nine-sharing-sign25-endpoint-check'
assert not check.exists(), 'refusing to overwrite diagnostic packet'
check.mkdir()
(check / 'src/DiophantineConsistency').mkdir(parents=True)
shutil.copyfile(original / 'framework-survey.py', check / 'framework-survey.py')
shutil.copyfile(draft / 'expression-survey.py', check / 'expression-survey.py')
names = ['Sign25GenericStandard', 'Sign25TypedSentence', 'Sign25TypedImports', 'Sign25TypedCheckFormula', 'Sign25TypedCheckProof']
rows = []
for name in names:
    src = draft / (name + '.lean')
    dest = check / 'src/DiophantineConsistency' / src.name
    shutil.copyfile(src, dest)
    data = src.read_bytes()
    imports = re.findall(r'^import ([A-Za-z0-9_.]+)$', data.decode(), re.M)
    rows.append({'module': 'DiophantineConsistency.' + name,
                 'source': str(src.relative_to(research.parents[2])),
                 'source_sha256': hashlib.sha256(data).hexdigest(),
                 'imports': imports})
manifest = (json.dumps({'rows': rows}, indent=2) + '\n').encode()
(check / 'source-manifest.json').write_bytes(manifest)
runner = (original / 'run.py').read_text()
old_pin = 'c5de8b265cfbb4fbc75bd903f67e411dff8798d8144fd4d5fdfbafff79e10dd8'
assert runner.count(old_pin) == 1
runner = runner.replace(old_pin, hashlib.sha256(manifest).hexdigest())
old_out = '/tmp/nine-sharing-sign25-endpoint-check-20261106'
assert runner.count(old_out) == 1
runner = runner.replace(old_out, '/tmp/nine-sharing-sign25-specialization-diagnostic-20261109')
old_names = "'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard','Sign25DirectTranslated'"
assert runner.count(old_names) == 1
runner = runner.replace(old_names, ','.join(repr(n) for n in names))
old_previous = "'Sign25NativeExpression','Sign25DirectNative','Sign25DirectStandard'"
assert runner.count(old_previous) == 1
runner = runner.replace(old_previous, ','.join(repr(n) for n in names[:-1]))
runner = runner.replace('Bounded sign26 direct endpoint diagnostic', 'Bounded sign25 typed-specialization diagnostic')
runner = runner.replace('PASS sign25 direct endpoint diagnostic', 'PASS sign25 typed-specialization diagnostic')
survey_pin = hashlib.sha256((check / 'expression-survey.py').read_bytes()).hexdigest()
anchor = "check_external_syntax()\nneed(sha(D/"
assert runner.count(anchor) == 1
survey = """def check_expression():
 need(sha(P/'expression-survey.py')=='SURVEY_PIN','expression survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'expression-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'expression survey');data=json.loads(r.stdout);need(data['status']=='PASS','expression status');return data
expression_data=check_expression()
""".replace('SURVEY_PIN',survey_pin)
runner = runner.replace(anchor, 'check_external_syntax()\n'+survey+'need(sha(D/')
anchor = "   elif local in framework['observed']:\n"
assert runner.count(anchor) == 1
runner = runner.replace(anchor, "   elif local=='Sign25CurrentExpressionDef':\n    expected_hash=expression_data['object_sha256'];path=Path(expression_data['realpath'])\n"+anchor)
anchor = " check_external_syntax()\n state['status']='PASS'"
assert runner.count(anchor) == 1
runner = runner.replace(anchor, " check_external_syntax()\n need(check_expression()==expression_data,'expression final drift')\n state['status']='PASS'")
(check / 'run.py').write_text(runner)
(check / 'README.md').write_text('''# Sign25 typed-specialization diagnostic guarded client\n\nFive source-only stages compile generic and typed-sentence declarations then\ntest the heavy imports, the assertion and the specialized proof term.\nThe runner is adapted from the pinned endpoint runner with the same resource\nlimits and independent output directory; the diagnostic changes import\nboundaries and therefore does not by itself isolate the exact original cause.\nNo endpoint is claimed. Author no-Lean preflight and independent review are\nrequired, and Lean may run only on an assigned slot.\n''')
print(json.dumps({'manifest_sha256': hashlib.sha256(manifest).hexdigest(),
                  'runner_sha256': hashlib.sha256(runner.encode()).hexdigest(),
                  'stages': names}, sort_keys=True))
