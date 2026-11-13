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
old=research/'nine-sharing-sign21-endpoint-check'
check=research/'nine-sharing-sign21-exact-degree-check'
assert not check.exists(), 'refusing to overwrite exact-degree packet'
check.mkdir(); (check/'src/DiophantineConsistency').mkdir(parents=True)
src=draft/'Sign21ExactDegree.lean'; data=src.read_bytes()
shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
shutil.copyfile(draft/'upper-survey.py',check/'upper-survey.py')
manifest=(json.dumps({'rows':[{'module':'DiophantineConsistency.Sign21ExactDegree',
    'source':str(src.relative_to(research.parents[2])),
    'source_sha256':hashlib.sha256(data).hexdigest(),
    'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)}]},indent=2)+'\n').encode()
(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign21-concrete-polynomial-bridge-check-20261109'
newbase='/tmp/nine-sharing-sign21-full-coeff-20261109'
survey=(old/'framework-survey.py').read_text(); assert survey.count(oldbase)==1
survey=survey.replace(oldbase,newbase); (check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def replace_once(a,b):
    global runner
    assert runner.count(a)==1, ('replacement count',a)
    runner=runner.replace(a,b)
replace_once(oldbase,newbase)
replace_once('/tmp/nine-sharing-sign21-endpoint-check-20261109', '/tmp/nine-sharing-sign21-exact-degree-20261109')
replace_once('research/nine-sharing-sign21-concrete-polynomial-bridge-check/attempt01/state.json',
             'research/nine-sharing-sign21-full-coeff-check/attempt01/state.json')
replace_once('a39faef23d06b893831abec1de2356f6718745c1b25328c1dec069534ba96ffb',
             '5c5fd144a0c16e362e7eb8bb4ce2eb503694e852838517cfc8efbdeb22ed45ec')
replace_once("base['status']=='PASS' and len(base['rows'])==1",
             "base['status']=='PASS' and len(base['rows'])==7 and base['rows'][6]['module']=='Sign21DegreeLower'")
replace_once("['author_observed_numeric_outer_exit']", "['outer_exit_code']")
old_outer='research/nine-sharing-sign21-concrete-polynomial-bridge-check/attempt01/outer-result.json'
assert runner.count(old_outer)==2
runner=runner.replace(old_outer,'research/nine-sharing-sign21-full-coeff-check/attempt01/outer-result.json')
replace_once('b2f8aca8c356193f1dcf521a6c07397f7c13c6d036319e94d3bf1eac715856d0',
             '91b4ba2612e15d07bd5e049b7d639701ceb69974ed900dd5f698b5b0284dbc75')
replace_once('reviews/nine-sharing-sign21-concrete-polynomial-bridge-terminal-independent/check.py',
             'reviews/nine-sharing-sign21-full-coeff-terminal-independent/check.py')
replace_once('f25640c5d74e8165b4c574054b09332b87c58b03a21f058eff13891ef210279f',
             '06ed9505eef7be48135ac5ae1dee342c676a8e82e74e50c4200d98106348c16d')
replace_once('d93091286d66e5029cb8c175792c2001348cdbe5bbb87906a75613f1761c4ff0', hashlib.sha256(manifest).hexdigest())
replace_once('66ed61302f8cd5deca6812994e17dade30c22f8b339cf354294e7bdc86dcc500', hashlib.sha256(survey.encode()).hexdigest())
replace_once("'Sign21DirectNoAliasNative','Sign21DirectNoAliasStandard','Sign21DirectNoAliasTranslated'", "'Sign21ExactDegree',")
replace_once("if local=='Sign21DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign21DirectPolynomialBridge.olean'",
             "if local=='Sign21DegreeLower':expected_hash=base['rows'][6]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign21DegreeLower.olean'\n   elif local=='Sign21DegreeCompose':expected_hash=upper_data['objects'][local]['sha256'];path=Path(upper_data['objects'][local]['realpath'])")
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
runner=runner.replace('Bounded sign21 no-alias endpoint attempt','Bounded sign21 exact-degree provider union')
runner=runner.replace('PASS sign21 no-alias endpoint attempt','PASS sign21 exact-degree provider union')
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign21 exact degree guarded client\n\nA source-only client combines the independently audited upper and lower degree\nproofs. The runner rechecks the lower provider's seven stages and overlay; an\nupper survey rechecks four upper stages and their 1,440 byte-matching overlay\nlinks, with no extras. It injects those four exact upper objects in a fresh\noutput and reruns both surveys at postflight. Same `-M3600`, sampled RSS,\nhost floor, timeout and disk guards apply. This is not a JSON/PDF binding.\n''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),
                  'manifest_sha256':hashlib.sha256(manifest).hexdigest(),
                  'framework_survey_sha256':hashlib.sha256(survey.encode()).hexdigest(),
                  'upper_survey_sha256':upper_pin},sort_keys=True))
