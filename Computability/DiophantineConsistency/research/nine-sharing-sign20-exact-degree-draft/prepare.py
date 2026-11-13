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
old=research/'nine-sharing-sign20-endpoint-check'
check=research/'nine-sharing-sign20-exact-degree-check'
assert not check.exists(), 'refusing to overwrite exact-degree packet'
check.mkdir(); (check/'src/DiophantineConsistency').mkdir(parents=True)
src=draft/'Sign20ExactDegree.lean'; data=src.read_bytes()
shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
shutil.copyfile(draft/'upper-survey.py',check/'upper-survey.py')
shutil.copyfile(draft/'beta-survey.py',check/'beta-survey.py')
manifest=(json.dumps({'rows':[{'module':'DiophantineConsistency.Sign20ExactDegree',
    'source':str(src.relative_to(research.parents[2])),
    'source_sha256':hashlib.sha256(data).hexdigest(),
    'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)}]},indent=2)+'\n').encode()
(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109'
newbase='/tmp/nine-sharing-sign20-count-lower-20261110'
survey=(old/'framework-survey.py').read_text(); assert survey.count(oldbase)==1
survey=survey.replace(oldbase,newbase); (check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def replace_once(a,b):
    global runner
    assert runner.count(a)==1, ('replacement count',a)
    runner=runner.replace(a,b)
replace_once(oldbase,newbase)
replace_once('/tmp/nine-sharing-sign20-endpoint-check-20261109', '/tmp/nine-sharing-sign20-exact-degree-20261109')
replace_once('research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/state.json',
             'research/nine-sharing-sign20-count-lower-check/attempt01/state.json')
replace_once('4bdbfc5abea2289faa93fce3677b81a4b274c5e814eb2fe4d1769758eae48a62',
             'c204dc08027fae9e1515802f91c1717d9bf6384393604df09cd04825411530d6')
replace_once("base['status']=='PASS' and len(base['rows'])==1",
             "base['status']=='PASS' and len(base['rows'])==2 and base['rows'][1]['module']=='Sign20DegreeLower'")
replace_once("['author_observed_numeric_outer_exit']", "['outer_exit_code']")
old_outer='research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/outer-result.json'
assert runner.count(old_outer)==2
runner=runner.replace(old_outer,'research/nine-sharing-sign20-count-lower-check/attempt01/outer-result.json')
replace_once('ba57aa78858d7003a243a23364b6972d8e74865cc639ad061db37077dc5b6f9a',
             'eefde572907c967dbba0c49af8a5bf4fc041174553952b4950223f350543ea81')
replace_once('reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py',
             'reviews/nine-sharing-sign20-count-lower-terminal-independent/check.py')
replace_once('e1744c21057a550a8a35912d1a0be4ba260855a7d219bb01ecc7e88eaf59309b',
             '64568c0bc5766e903f2dca992bd9003ef72f9204042965f5333a7913a1811a6d')
replace_once('ed79c1bb35d1b6f5bf9014e275b372610c220a93c7bf9b815e66da12a5537c87', hashlib.sha256(manifest).hexdigest())
replace_once('e520ea55d5db51d161783a9841a40e7465a6bf544204c882945fdd6ef9cf9a7c', hashlib.sha256(survey.encode()).hexdigest())
replace_once("'Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard','Sign20DirectNoAliasTranslated'", "'Sign20ExactDegree',")
replace_once("if local=='Sign20DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20DirectPolynomialBridge.olean'",
             "if local=='Sign20DegreeLower':expected_hash=base['rows'][1]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20DegreeLower.olean'\n   elif local=='Sign20DegreeCompose':expected_hash=upper_data['objects'][local]['sha256'];path=Path(upper_data['objects'][local]['realpath'])\n   elif local=='Sign20CurrentBeta':expected_hash=beta_data['objects'][local]['sha256'];path=Path(beta_data['objects'][local]['realpath'])")
anchor="check_external_syntax()\nneed(sha(D/"
upper_pin=hashlib.sha256((check/'upper-survey.py').read_bytes()).hexdigest()
beta_pin=hashlib.sha256((check/'beta-survey.py').read_bytes()).hexdigest()
extra="""def check_upper():
 need(sha(P/'upper-survey.py')=='UPPER_PIN','upper survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'upper-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'upper survey');data=json.loads(r.stdout);need(data['status']=='PASS','upper status');return data
upper_data=check_upper()
def check_beta():
 need(sha(P/'beta-survey.py')=='BETA_PIN','beta survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'beta-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'beta survey');data=json.loads(r.stdout);need(data['status']=='PASS','beta status');return data
beta_data=check_beta()
""".replace('UPPER_PIN',upper_pin).replace('BETA_PIN',beta_pin)
replace_once(anchor,'check_external_syntax()\n'+extra+'need(sha(D/')
anchor="for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))"
injection="""for n,rec in {**upper_data['objects'],**beta_data['objects']}.items():
 q=OUT/'lib/DiophantineConsistency'/(n+'.olean');need(not os.path.lexists(q),'upper collision '+n);q.symlink_to(rec['realpath']);links[str(q)]=str(q.resolve());need(sha(q)==rec['sha256'],'upper object '+n)
"""
replace_once(anchor,injection+anchor)
replace_once(" check_external_syntax()\n state['status']='PASS'", " check_external_syntax()\n need(check_upper()==upper_data,'upper final drift')\n need(check_beta()==beta_data,'beta final drift')\n state['status']='PASS'")
runner=runner.replace('Bounded sign20 no-alias endpoint attempt','Bounded sign20 exact-degree provider union')
runner=runner.replace('PASS sign20 no-alias endpoint attempt','PASS sign20 exact-degree provider union')
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign20 exact degree guarded client\n\nA source-only client combines the independently audited upper and lower degree\nproofs. The runner rechecks the lower provider's seven stages and overlay; an\nupper survey rechecks four upper stages and their 1,455 byte-matching overlay\nlinks, with no extras. It injects those four exact upper objects in a fresh\noutput and reruns both surveys at postflight. Same `-M3600`, sampled RSS,\nhost floor, timeout and disk guards apply. This is not a JSON/PDF binding.\n''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                  'framework_survey_sha256':hashlib.sha256(survey.encode()).hexdigest(),
                  'upper_survey_sha256':upper_pin,'beta_survey_sha256':beta_pin},sort_keys=True))
