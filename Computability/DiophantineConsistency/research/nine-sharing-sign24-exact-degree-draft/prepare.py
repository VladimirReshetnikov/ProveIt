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
old=research/'nine-sharing-sign24-endpoint-memory-check'
check=research/'nine-sharing-sign24-exact-degree-check'
assert not check.exists(), 'refusing to overwrite exact-degree packet'
check.mkdir(); (check/'src/DiophantineConsistency').mkdir(parents=True)
src=draft/'Sign24ExactDegree.lean'; data=src.read_bytes()
shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
shutil.copyfile(draft/'upper-survey.py',check/'upper-survey.py')
manifest=(json.dumps({'rows':[{'module':'DiophantineConsistency.Sign24ExactDegree',
    'source':str(src.relative_to(research.parents[2])),
    'source_sha256':hashlib.sha256(data).hexdigest(),
    'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)}]},indent=2)+'\n').encode()
(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign24-concrete-bridge-memory-retry-20261109'
newbase='/tmp/nine-sharing-sign24-full-coeff-retry02-20261109'
survey=(old/'framework-survey.py').read_text(); assert survey.count(oldbase)==1
survey=survey.replace(oldbase,newbase); (check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def replace_once(a,b):
    global runner
    assert runner.count(a)==1, ('replacement count',a)
    runner=runner.replace(a,b)
replace_once(oldbase,newbase)
replace_once('/tmp/nine-sharing-sign24-endpoint-memory-20261109', '/tmp/nine-sharing-sign24-exact-degree-20261109')
replace_once('research/nine-sharing-sign24-concrete-bridge-memory-retry-check/attempt01/state.json',
             'research/nine-sharing-sign24-full-coeff-retry02-check/attempt01/state.json')
replace_once('cabef9b9e1fb3291b298cd4f46ad820ecadf3918eb3d35253b8dbe048c36cddc',
             'd9554ac684c8c809238cafba65a1171434dc044e647e8accf88a88e3c31749b0')
replace_once("base['status']=='PASS' and len(base['rows'])==1",
             "base['status']=='PASS' and len(base['rows'])==7 and base['rows'][6]['module']=='Sign24DegreeLower'")
old_outer='research/nine-sharing-sign24-concrete-bridge-memory-retry-check/attempt01/outer-result.json'
assert runner.count(old_outer)==2
runner=runner.replace(old_outer,'research/nine-sharing-sign24-full-coeff-retry02-check/attempt01/outer-result.json')
replace_once('8cd9eac76f5a3b196511327079ba1e3a2b2d8ec23769b242cd693fc867c106d8',
             '9384c47e21e8864e4b0201aacab77de849ad9f74537427c6c4c889a039a63dfc')
replace_once('reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py',
             'reviews/nine-sharing-sign24-full-coeff-retry02-terminal-independent/check.py')
replace_once('c8854f8e0ebf1e998192738f75119fbc1796b114a4f7fab96279d88686a04d87',
             'a8d86b31534ae787daff9f5fa230d50fc5a3102159ee0081627314a1d34999bf')
replace_once('5b817535ec860c794c84fe479283ddf7fa3bc01edae34ddf56be70ac9bf5c793', hashlib.sha256(manifest).hexdigest())
replace_once('e76b7ad869ccd5f86efdcfe14ca26ffa720bd248ecd97fcea127b778cecb4096', hashlib.sha256(survey.encode()).hexdigest())
replace_once("'Sign24DirectNoAliasNative','Sign24DirectNoAliasStandard','Sign24DirectNoAliasTranslated'", "'Sign24ExactDegree',")
replace_once("if local=='Sign24DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign24DirectPolynomialBridge.olean'",
             "if local=='Sign24DegreeLower':expected_hash=base['rows'][6]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign24DegreeLower.olean'\n   elif local=='Sign24DegreeCompose':expected_hash=upper_data['objects'][local]['sha256'];path=Path(upper_data['objects'][local]['realpath'])")
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
runner=runner.replace('Bounded sign24 memory-limit endpoint attempt','Bounded sign24 exact-degree provider union')
runner=runner.replace('PASS sign24 memory-limit endpoint attempt','PASS sign24 exact-degree provider union')
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign24 exact degree guarded client\n\nA source-only client combines the independently audited upper and lower degree\nproofs. The runner rechecks the lower provider's seven stages and overlay; an\nupper survey rechecks four upper stages and their 1,398 byte-matching overlay\nlinks, with no extras. It injects those four exact upper objects in a fresh\noutput and reruns both surveys at postflight. Same `-M3600`, sampled RSS,\nhost floor, timeout and disk guards apply. This is not a JSON/PDF binding.\n''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                  'framework_survey_sha256':hashlib.sha256(survey.encode()).hexdigest(),
                  'upper_survey_sha256':upper_pin},sort_keys=True))
