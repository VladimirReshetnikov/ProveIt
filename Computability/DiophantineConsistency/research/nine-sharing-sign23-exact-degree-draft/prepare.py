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
old=research/'nine-sharing-sign23-endpoint-check'
check=research/'nine-sharing-sign23-exact-degree-check'
assert not check.exists(), 'refusing to overwrite exact-degree packet'
check.mkdir(); (check/'src/DiophantineConsistency').mkdir(parents=True)
src=draft/'Sign23ExactDegree.lean'; data=src.read_bytes()
shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
shutil.copyfile(draft/'upper-survey.py',check/'upper-survey.py')
manifest=(json.dumps({'rows':[{'module':'DiophantineConsistency.Sign23ExactDegree',
    'source':str(src.relative_to(research.parents[2])),
    'source_sha256':hashlib.sha256(data).hexdigest(),
    'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)}]},indent=2)+'\n').encode()
(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign23-concrete-polynomial-bridge-check-20261109'
newbase='/tmp/nine-sharing-sign23-full-coeff-20261109'
survey=(old/'framework-survey.py').read_text(); assert survey.count(oldbase)==1
survey=survey.replace(oldbase,newbase); (check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def replace_once(a,b):
    global runner
    assert runner.count(a)==1, ('replacement count',a)
    runner=runner.replace(a,b)
replace_once(oldbase,newbase)
replace_once('/tmp/nine-sharing-sign23-endpoint-check-20261109', '/tmp/nine-sharing-sign23-exact-degree-20261109')
replace_once('research/nine-sharing-sign23-concrete-polynomial-bridge-check/attempt01/state.json',
             'research/nine-sharing-sign23-full-coeff-check/attempt01/state.json')
replace_once('9c07d4def940f0b9c88a3d8bcb273998415c30093bb0d5823cc63b4c9f9b6ddc',
             'db86b046b6c66c6ff54313ceb782b18d1cf19689c718b7e347464d1929815e1a')
replace_once("base['status']=='PASS' and len(base['rows'])==1",
             "base['status']=='PASS' and len(base['rows'])==7 and base['rows'][6]['module']=='Sign23DegreeLower'")
replace_once("['author_observed_numeric_outer_exit']", "['outer_exit_code']")
old_outer='research/nine-sharing-sign23-concrete-polynomial-bridge-check/attempt01/outer-result.json'
assert runner.count(old_outer)==2
runner=runner.replace(old_outer,'research/nine-sharing-sign23-full-coeff-check/attempt01/outer-result.json')
replace_once('c4cdca9899a028dd242d87302c6975a69453c7f74ed0aa0494dbcf051e237492',
             '067725c83c30b04e7690196e67d24132b95e1be792421ee4f53a98286280db83')
replace_once('reviews/nine-sharing-sign23-concrete-polynomial-bridge-terminal-independent/check.py',
             'reviews/nine-sharing-sign23-full-coeff-terminal-independent/check.py')
replace_once('4b8965bc5acdbb9ead4bf8bd13fadc0d49a1f3c220b24a75e9af3aa29e747769',
             'd27c66cc30520edf9cc3c81c4fb81fb9db4be244de1875a7b1e1fe12d153f2cf')
replace_once('1a79ce4431773050aa667daab1458d92b55917a81f7dfe8366f07ee2fe6247f7', hashlib.sha256(manifest).hexdigest())
replace_once('77d04a3bb3cfec40baf02321b82c5ffc579c63607a6910d023c550e427436dcd', hashlib.sha256(survey.encode()).hexdigest())
replace_once("'Sign23DirectNoAliasNative','Sign23DirectNoAliasStandard','Sign23DirectNoAliasTranslated'", "'Sign23ExactDegree',")
replace_once("if local=='Sign23DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign23DirectPolynomialBridge.olean'",
             "if local=='Sign23DegreeLower':expected_hash=base['rows'][6]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign23DegreeLower.olean'\n   elif local=='Sign23DegreeCompose':expected_hash=upper_data['objects'][local]['sha256'];path=Path(upper_data['objects'][local]['realpath'])")
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
runner=runner.replace('Bounded sign23 no-alias endpoint attempt','Bounded sign23 exact-degree provider union')
runner=runner.replace('PASS sign23 no-alias endpoint attempt','PASS sign23 exact-degree provider union')
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign23 exact degree guarded client\n\nA source-only client combines the independently audited upper and lower degree\nproofs. The runner rechecks the lower provider's seven stages and overlay; an\nupper survey rechecks four upper stages and their 1,412 byte-matching overlay\nlinks, with no extras. It injects those four exact upper objects in a fresh\noutput and reruns both surveys at postflight. Same `-M3600`, sampled RSS,\nhost floor, timeout and disk guards apply. This is not a JSON/PDF binding.\n''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                  'framework_survey_sha256':hashlib.sha256(survey.encode()).hexdigest(),
                  'upper_survey_sha256':upper_pin},sort_keys=True))
