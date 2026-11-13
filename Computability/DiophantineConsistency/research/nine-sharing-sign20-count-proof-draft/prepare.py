#!/usr/bin/env python3
"""Prepare isolated count diagnostic against audited successful partial children."""
import hashlib,json,re,shutil,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
draft=Path(__file__).resolve().parent; research=draft.parent
old=research/'nine-sharing-sign20-endpoint-check'; check=research/'nine-sharing-sign20-count-proof-check'
assert not check.exists();check.mkdir();(check/'src/DiophantineConsistency').mkdir(parents=True)
src=draft/'Sign20CountProof.lean';data=src.read_bytes();shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
manifest=(json.dumps({'rows':[{'module':'DiophantineConsistency.Sign20CountProof','source':str(src.relative_to(research.parents[2])), 'source_sha256':hashlib.sha256(data).hexdigest(),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)}]},indent=2)+'\n').encode();(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109';newbase='/tmp/nine-sharing-sign20-count-shapes-20261110'
survey=(old/'framework-survey.py').read_text();assert survey.count(oldbase)==1;survey=survey.replace(oldbase,newbase);(check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def rep(a,b):
 global runner
 assert runner.count(a)==1,('count',a)
 runner=runner.replace(a,b)
rep(oldbase,newbase)
rep('/tmp/nine-sharing-sign20-endpoint-check-20261109','/tmp/nine-sharing-sign20-count-proof-20261110')
rep('research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/state.json','research/nine-sharing-sign20-count-shapes-check/attempt01/state.json')
rep('4bdbfc5abea2289faa93fce3677b81a4b274c5e814eb2fe4d1769758eae48a62','a088e6e081bab78ba26fae063a3388a97309228017e5203f9a12970584ecdbd4')
rep("base['status']=='PASS' and len(base['rows'])==1", "base['status']=='PASS' and len(base['rows'])==1 and base['rows'][0]['module']=='Sign20CountShapes'")
rep("['author_observed_numeric_outer_exit']", "['outer_exit_code']")
oldouter='research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/outer-result.json';assert runner.count(oldouter)==2;runner=runner.replace(oldouter,'research/nine-sharing-sign20-count-shapes-check/attempt01/outer-result.json')
rep('ba57aa78858d7003a243a23364b6972d8e74865cc639ad061db37077dc5b6f9a','0256c249c5e24f8ddbc92dea16915018b9330413959669f2da3c74f22abcf7c6')
rep("['outer_exit_code']==0,'bridge outer status'", "['outer_exit_code']==0,'shape outer status'")
rep('reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py','reviews/nine-sharing-sign20-count-shapes-terminal-independent/check.py')
rep('e1744c21057a550a8a35912d1a0be4ba260855a7d219bb01ecc7e88eaf59309b','28f0daefeccf9427e547de50714a155f3cad40e2d91b1c13bf224bd689b22a9b')
rep('ed79c1bb35d1b6f5bf9014e275b372610c220a93c7bf9b815e66da12a5537c87',hashlib.sha256(manifest).hexdigest())
rep('e520ea55d5db51d161783a9841a40e7465a6bf544204c882945fdd6ef9cf9a7c',hashlib.sha256(survey.encode()).hexdigest())
rep("'Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard','Sign20DirectNoAliasTranslated'","'Sign20CountProof',")
rep("if local=='Sign20DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20DirectPolynomialBridge.olean'", "if local=='Sign20CountShapes':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20CountShapes.olean'")
assert runner.count("for row in base['rows']:")==2;runner=runner.replace("for row in base['rows']:","for row in base['rows'][:1]:")
runner=runner.replace('Bounded sign20 no-alias endpoint attempt','Bounded sign20 count proof using five successful children of a failed parent')
runner=runner.replace('PASS sign20 no-alias endpoint attempt','PASS sign20 count proof')
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
