#!/usr/bin/env python3
"""Prepare isolated count diagnostic against audited successful partial children."""
import hashlib,json,re,shutil,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
draft=Path(__file__).resolve().parent; research=draft.parent
old=research/'nine-sharing-sign20-endpoint-check'; check=research/'nine-sharing-sign20-count-lower-check'
assert not check.exists();check.mkdir();(check/'src/DiophantineConsistency').mkdir(parents=True)
names=['Sign20SeedCoefficient','Sign20DegreeLower']
rows=[]
for name in names:
 src=draft/(name+'.lean');data=src.read_bytes();shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(src.relative_to(research.parents[2])), 'source_sha256':hashlib.sha256(data).hexdigest(),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)})
manifest=(json.dumps({'rows':rows},indent=2)+'\n').encode();(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109';newbase='/tmp/nine-sharing-sign20-count-proof-20261110'
survey=(old/'framework-survey.py').read_text();assert survey.count(oldbase)==1;survey=survey.replace(oldbase,newbase);(check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def rep(a,b):
 global runner
 assert runner.count(a)==1,('count',a)
 runner=runner.replace(a,b)
rep(oldbase,newbase)
rep('/tmp/nine-sharing-sign20-endpoint-check-20261109','/tmp/nine-sharing-sign20-count-lower-20261110')
rep('research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/state.json','research/nine-sharing-sign20-count-proof-check/attempt01/state.json')
rep('4bdbfc5abea2289faa93fce3677b81a4b274c5e814eb2fe4d1769758eae48a62','e68cf86e09dfa6e0e27534e8c6e7989e4e6afd66be110852f4a70a18ba329afa')
rep("base['status']=='PASS' and len(base['rows'])==1", "base['status']=='PASS' and len(base['rows'])==1 and base['rows'][0]['module']=='Sign20CountProof'")
rep("['author_observed_numeric_outer_exit']", "['outer_exit_code']")
oldouter='research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/outer-result.json';assert runner.count(oldouter)==2;runner=runner.replace(oldouter,'research/nine-sharing-sign20-count-proof-check/attempt01/outer-result.json')
rep('ba57aa78858d7003a243a23364b6972d8e74865cc639ad061db37077dc5b6f9a','92799d4a14de1a19475fd135987bafa55e93006b33952749a5637f5b29a682b4')
rep("['outer_exit_code']==0,'bridge outer status'", "['outer_exit_code']==0,'shape outer status'")
rep('reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py','reviews/nine-sharing-sign20-count-proof-terminal-independent/check.py')
rep('e1744c21057a550a8a35912d1a0be4ba260855a7d219bb01ecc7e88eaf59309b','80dce4c8965ce52280e9295e79b4ef4e5a447251b4085c9c5ca94a256f56a378')
rep('ed79c1bb35d1b6f5bf9014e275b372610c220a93c7bf9b815e66da12a5537c87',hashlib.sha256(manifest).hexdigest())
rep('e520ea55d5db51d161783a9841a40e7465a6bf544204c882945fdd6ef9cf9a7c',hashlib.sha256(survey.encode()).hexdigest())
rep("'Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard','Sign20DirectNoAliasTranslated'","'Sign20SeedCoefficient','Sign20DegreeLower'")
rep("if local=='Sign20DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20DirectPolynomialBridge.olean'", "if local=='Sign20CountProof':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20CountProof.olean'\n   elif local=='Sign20DiagonalDegree':expected_hash=partial['rows'][1]['object_sha256'];path=PARTIAL/'lib/DiophantineConsistency/Sign20DiagonalDegree.olean'")
rep("elif local in ('Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard'):", "elif local in ('Sign20SeedCoefficient',):")
anchor="for row in base['rows']:\n"
partial="""PARTIAL=Path('/tmp/nine-sharing-sign20-full-coeff-retry03-20261109')
PARTIAL_STATE=D/'research/nine-sharing-sign20-full-coeff-retry03-check/attempt01/state.json'
need(sha(PARTIAL_STATE)=='d9dc10f0d38cfb7875ddcad092cb35abf30c77f13972393ba49af1c3b117b789','partial state pin')
need(sha(D/'research/nine-sharing-sign20-full-coeff-retry03-check/attempt01/outer-result.json')=='8c6446991042db4807a8f5ecd8e605382c58aceae5ae5db663eff2ce21ef2305','partial outer pin')
need(sha(D/'reviews/nine-sharing-sign20-full-coeff-retry03-failure-independent/check.py')=='7c466400674c4477f5e430b4b6111998766cbd2194c3478909ecc473c732a1b8','partial audit pin')
partial=json.loads(PARTIAL_STATE.read_text());need(partial['status']=='FAILED' and partial['rows'][1]['module']=='Sign20DiagonalDegree' and partial['rows'][1]['compile']['exit']==0,'partial diagonal stage')
need(json.loads((D/'research/nine-sharing-sign20-full-coeff-retry03-check/attempt01/outer-result.json').read_text())['outer_exit_code']==1,'partial outer failure')
diag=partial['rows'][1];dn='Sign20DiagonalDegree'
need(sha(PARTIAL/'src/DiophantineConsistency'/(dn+'.lean'))==diag['source_sha256'] and sha(PARTIAL/'lib/DiophantineConsistency'/(dn+'.olean'))==diag['object_sha256'],'partial diagonal source/object')
for kind in ('deps','compile'):need(sha(PARTIAL/(dn+'-'+kind+'.txt'))==diag[kind]['log_sha256'],'partial diagonal log')
for k,v in diag['direct_guard'].items():
 q=Path(k)
 if v is None:need(not os.path.lexists(q),'partial diagonal unexpected')
 else:need(q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],'partial diagonal guard')
"""
assert runner.count(anchor)==2;runner=runner.replace(anchor,partial+anchor,1)
assert runner.count("for row in base['rows']:")==2;runner=runner.replace("for row in base['rows']:","for row in base['rows'][:1]:")
runner=runner.replace('Bounded sign20 no-alias endpoint attempt','Bounded sign20 conditional lower using audited count and failed-grandparent diagonal child')
runner=runner.replace('PASS sign20 no-alias endpoint attempt','PASS sign20 conditional degree lower')
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
