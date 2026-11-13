#!/usr/bin/env python3
"""Prepare a guarded exact-degree client on audited lower and upper providers."""
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
draft=Path(__file__).resolve().parent; research=draft.parent
old=research/'nine-sharing-sign22-endpoint-check'
check=research/'nine-sharing-sign22-exact-degree-check'
assert not check.exists(), 'refusing to overwrite exact-degree packet'
check.mkdir(); (check/'src/DiophantineConsistency').mkdir(parents=True)
src=draft/'Sign22ExactDegree.lean'; data=src.read_bytes()
shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
shutil.copyfile(draft/'upper-survey.py',check/'upper-survey.py')
manifest=(json.dumps({'rows':[{'module':'DiophantineConsistency.Sign22ExactDegree',
    'source':str(src.relative_to(research.parents[2])),
    'source_sha256':hashlib.sha256(data).hexdigest(),
    'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)}]},indent=2)+'\n').encode()
(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign22-concrete-polynomial-bridge-check-20261109'
newbase='/tmp/nine-sharing-sign22-full-coeff-20261109'
survey=(old/'framework-survey.py').read_text(); assert survey.count(oldbase)==1
survey=survey.replace(oldbase,newbase); (check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def replace_once(a,b):
    global runner
    assert runner.count(a)==1, ('replacement count',a)
    runner=runner.replace(a,b)
replace_once(oldbase,newbase)
replace_once('/tmp/nine-sharing-sign22-endpoint-check-20261109', '/tmp/nine-sharing-sign22-exact-degree-20261109')
replace_once('research/nine-sharing-sign22-concrete-polynomial-bridge-check/attempt01/state.json',
             'research/nine-sharing-sign22-full-coeff-check/attempt01/state.json')
replace_once('770f69455087df0f8f8aecef793e5edb67ace70806ba2e6227fa936a37e76bff',
             '216d07cfe7d7e8d500c95e7cd0d557359de703ab5061f5dd54d61b7f5ede7451')
replace_once("base['status']=='PASS' and len(base['rows'])==1",
             "base['status']=='PASS' and len(base['rows'])==7 and base['rows'][6]['module']=='Sign22DegreeLower'")
replace_once("['author_observed_numeric_outer_exit']", "['outer_exit_code']")
old_outer='research/nine-sharing-sign22-concrete-polynomial-bridge-check/attempt01/outer-result.json'
assert runner.count(old_outer)==2
runner=runner.replace(old_outer,'research/nine-sharing-sign22-full-coeff-check/attempt01/outer-result.json')
replace_once('0998d6d47a9f6c08a87b4cbc2bed224568a9f3debe0ba71578c2de3c651b4482',
             'ed322e9afefb79ddea732229f18a496ad5d319425a32fae2ae062bffc089f397')
replace_once('reviews/nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent/check.py',
             'reviews/nine-sharing-sign22-full-coeff-terminal-independent/check.py')
replace_once('fb534290e96ce030b25f62fbb67fbf0b03381431372543bb6748fecaa638c682',
             'ca477c01d769f4b51e0acc19a08e6f5ed82af1dece6828ab6e385589395eb170')
replace_once('309dcb72ff0d767e0be2521ed5a7d88e58ce137449e603f15dca1a06f56e5200', hashlib.sha256(manifest).hexdigest())
replace_once('bd0a23fb642365f6ef15a5b0dac263ec81ae85eca86515fde44cfecfc39276d4', hashlib.sha256(survey.encode()).hexdigest())
replace_once("'Sign22DirectNoAliasNative','Sign22DirectNoAliasStandard','Sign22DirectNoAliasTranslated'", "'Sign22ExactDegree',")
replace_once("if local=='Sign22DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign22DirectPolynomialBridge.olean'",
             "if local=='Sign22DegreeLower':expected_hash=base['rows'][6]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign22DegreeLower.olean'\n   elif local=='Sign22DegreeCompose':expected_hash=upper_data['objects'][local]['sha256'];path=Path(upper_data['objects'][local]['realpath'])")
anchor="check_external_syntax()\nneed(sha(D/"
upper_pin=hashlib.sha256((check/'upper-survey.py').read_bytes()).hexdigest()
extra="""def check_upper():
 need(sha(P/'upper-survey.py')=='UPPER_PIN','upper survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'upper-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'upper survey');data=json.loads(r.stdout);need(data['status']=='PASS','upper status');return data
upper_data=check_upper()
""".replace('UPPER_PIN',upper_pin)
replace_once(anchor,'check_external_syntax()\n'+extra+'need(sha(D/')
anchor="for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))"
injection="""for n,rec in upper_data['objects'].items():
 q=OUT/'lib/DiophantineConsistency'/(n+'.olean');need(not os.path.lexists(q),'upper collision '+n);q.symlink_to(rec['realpath']);links[str(q)]=str(q.resolve());need(sha(q)==rec['sha256'],'upper object '+n)
"""
replace_once(anchor,injection+anchor)
replace_once(" check_external_syntax()\n state['status']='PASS'", " check_external_syntax()\n need(check_upper()==upper_data,'upper final drift')\n state['status']='PASS'")
runner=runner.replace('Bounded sign22 no-alias endpoint attempt','Bounded sign22 exact-degree provider union')
runner=runner.replace('PASS sign22 no-alias endpoint attempt','PASS sign22 exact-degree provider union')
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign22 exact degree guarded client\n\nA source-only client combines the independently audited upper and lower degree\nproofs. The runner rechecks the lower provider's seven stages and overlay; an\nupper survey rechecks four upper stages and their 1,426 byte-matching overlay\nlinks, with no extras. It injects those four exact upper objects in a fresh\noutput and reruns both surveys at postflight. Same `-M3600`, sampled RSS,\nhost floor, timeout and disk guards apply. This is not a JSON/PDF binding.\n''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                  'framework_survey_sha256':hashlib.sha256(survey.encode()).hexdigest(),
                  'upper_survey_sha256':upper_pin},sort_keys=True))
