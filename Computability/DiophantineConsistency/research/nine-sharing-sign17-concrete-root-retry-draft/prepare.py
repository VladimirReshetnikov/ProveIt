#!/usr/bin/env python3
"""Prepare isolated count diagnostic against audited successful partial children."""
import hashlib,json,re,shutil,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
draft=Path(__file__).resolve().parent; research=draft.parent
old=research/'nine-sharing-sign20-endpoint-check'; check=research/'nine-sharing-sign17-concrete-root-retry-check'
assert not check.exists();check.mkdir();(check/'src/DiophantineConsistency').mkdir(parents=True)
names=['Sign17ConcreteRoot','Sign17ConcreteGap']
rows=[]
for name in names:
 src=draft/(name+'.lean');data=src.read_bytes();shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(src.relative_to(research.parents[2])), 'source_sha256':hashlib.sha256(data).hexdigest(),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)})
manifest=(json.dumps({'rows':rows},indent=2)+'\n').encode();(check/'source-manifest.json').write_bytes(manifest)
shutil.copyfile(draft/'staged-survey.py',check/'staged-survey.py')
oldbase='/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109';newbase='/tmp/nine-sharing-sign17-root-lift-20261110'
survey=(old/'framework-survey.py').read_text();assert survey.count(oldbase)==1;survey=survey.replace(oldbase,newbase);(check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def rep(a,b):
 global runner
 assert runner.count(a)==1,('count',a)
 runner=runner.replace(a,b)
rep(oldbase,newbase)
rep('/tmp/nine-sharing-sign20-endpoint-check-20261109','/tmp/nine-sharing-sign17-concrete-root-retry-20261110')
rep('research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/state.json','research/nine-sharing-sign17-root-lift-check/attempt01/state.json')
rep('4bdbfc5abea2289faa93fce3677b81a4b274c5e814eb2fe4d1769758eae48a62','6c1ad7ff961909377a643e0eb6ef6c5ea5bcf942d3ee352aa20d9dce87e332c7')
rep("base['status']=='PASS' and len(base['rows'])==1", "base['status']=='PASS' and len(base['rows'])==1 and base['rows'][0]['module']=='Sign17RootLift'")
rep("['author_observed_numeric_outer_exit']", "['outer_exit_code']")
oldouter='research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/outer-result.json';assert runner.count(oldouter)==2;runner=runner.replace(oldouter,'research/nine-sharing-sign17-root-lift-check/attempt01/outer-result.json')
rep('ba57aa78858d7003a243a23364b6972d8e74865cc639ad061db37077dc5b6f9a','5915599cdba617bf25d6a6a606ebc105ac465e61b6d363aad8ea5a720055f2d7')
rep("['outer_exit_code']==0,'bridge outer status'", "['outer_exit_code']==0,'shape outer status'")
rep('reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py','reviews/nine-sharing-sign17-root-lift-terminal-independent/check.py')
rep('e1744c21057a550a8a35912d1a0be4ba260855a7d219bb01ecc7e88eaf59309b','9cf038c8b9a7ac10514e699aaaeaacff380aa34a43a243e3f920098690c0287f')
rep('ed79c1bb35d1b6f5bf9014e275b372610c220a93c7bf9b815e66da12a5537c87',hashlib.sha256(manifest).hexdigest())
rep('e520ea55d5db51d161783a9841a40e7465a6bf544204c882945fdd6ef9cf9a7c',hashlib.sha256(survey.encode()).hexdigest())
rep("'Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard','Sign20DirectNoAliasTranslated'","'Sign17ConcreteRoot','Sign17ConcreteGap'")
rep("if local=='Sign20DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20DirectPolynomialBridge.olean'", "if local=='Sign17RootLift':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign17RootLift.olean'\n   elif local=='SharingSeed17Row06':expected_hash=staged_data['objects'][local]['sha256'];path=Path(staged_data['objects'][local]['realpath'])")
rep("elif local in ('Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard'):", "elif local in ('Sign17ConcreteRoot',):")
staged_pin=hashlib.sha256((check/'staged-survey.py').read_bytes()).hexdigest()
anchor="check_external_syntax()\nneed(sha(D/"
extra="""def check_staged():
 need(sha(P/'staged-survey.py')=='STAGED_PIN','staged survey pin')
 r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'staged-survey.py')],capture_output=True,timeout=120);need(r.returncode==0 and not r.stderr,'staged survey');data=json.loads(r.stdout);need(data['status']=='PASS','staged status');return data
staged_data=check_staged()
""".replace('STAGED_PIN',staged_pin)
rep(anchor,'check_external_syntax()\n'+extra+'need(sha(D/')
anchor="for n in names:shutil.copyfile(P/'src/DiophantineConsistency'/(n+'.lean'),OUT/'src/DiophantineConsistency'/(n+'.lean'))"
injection="""for n,rec in staged_data['objects'].items():
 q=OUT/'lib/DiophantineConsistency'/(n+'.olean');need(not os.path.lexists(q),'staged collision '+n);q.symlink_to(rec['realpath']);links[str(q)]=str(q.resolve());need(sha(q)==rec['sha256'],'staged object '+n)
"""
rep(anchor,injection+anchor)
rep(" check_external_syntax()\n state['status']='PASS'", " check_external_syntax()\n need(check_staged()==staged_data,'staged final drift')\n state['status']='PASS'")
assert runner.count("for row in base['rows']:")==2;runner=runner.replace("for row in base['rows']:","for row in base['rows']:")
runner=runner.replace('Bounded sign20 no-alias endpoint attempt','Bounded sign17 root-form lift using audited staged syntax and root-lift providers')
runner=runner.replace('PASS sign20 no-alias endpoint attempt','PASS sign17 concrete root and gap')
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign20 p-dependent count proof candidate

A single source-only stage proposes converting boolean AST equality to
propositional equality in the finite counts. Its base is explicitly a failed
parent: only the first five successful child objects are authenticated and
linked; the failed sixth child and parent postflight are not claimed. The
independent failure audit, numeric outer exit, source/object/log and direct
provider guards are pinned. This is not a full coefficient or degree theorem.
The monitor retains the same resource limits and historic provider caveats.
''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),'manifest_sha256':hashlib.sha256(manifest).hexdigest()},sort_keys=True))
