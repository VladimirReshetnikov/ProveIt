#!/usr/bin/env python3
"""Prepare degree-upper stages on the audited sign14 expression provider."""
import hashlib,json,re,shutil,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
draft=Path(__file__).resolve().parent;research=draft.parent
old=research/'nine-sharing-sign20-endpoint-check';check=research/'nine-sharing-sign14-degree-upper-check'
assert not check.exists();check.mkdir();(check/'src/DiophantineConsistency').mkdir(parents=True)
names=['Sign14SyntaxDegree']+[f'Sign14SharedDegree{i:02}' for i in range(9)]+[f'Sign14RowDegree{i:02}' for i in range(5)]+['Sign14DegreeStructural','Sign14DegreeResiduals','Sign14DegreeCompose'];rows=[]
for name in names:
 src=draft/(name+'.lean');data=src.read_bytes();shutil.copyfile(src,check/'src/DiophantineConsistency'/src.name)
 rows.append({'module':'DiophantineConsistency.'+name,'source':str(src.relative_to(research.parents[2])),
  'source_sha256':hashlib.sha256(data).hexdigest(),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',data.decode(),re.M)})
manifest=(json.dumps({'rows':rows},indent=2)+'\n').encode();(check/'source-manifest.json').write_bytes(manifest)
oldbase='/tmp/nine-sharing-sign20-concrete-polynomial-bridge-check-20261109';newbase='/tmp/nine-sharing-sign14-expression-eval-check-20261110'
survey=(old/'framework-survey.py').read_text();assert survey.count(oldbase)==1;survey=survey.replace(oldbase,newbase);(check/'framework-survey.py').write_text(survey)
runner=(old/'run.py').read_text()
def rep(a,b):
 global runner
 assert runner.count(a)==1,('count',a)
 runner=runner.replace(a,b)
rep(oldbase,newbase)
rep('/tmp/nine-sharing-sign20-endpoint-check-20261109','/tmp/nine-sharing-sign14-degree-upper-check-20261110')
rep('research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/state.json','research/nine-sharing-sign14-expression-eval-check/attempt01/state.json')
rep('4bdbfc5abea2289faa93fce3677b81a4b274c5e814eb2fe4d1769758eae48a62','2845701170bad15d792b2a893bae1635e2878b2b5ebe00904aab0ebae2da8e38')
rep("base['status']=='PASS' and len(base['rows'])==1", "base['status']=='PASS' and len(base['rows'])==4 and base['rows'][2]['module']=='Sign14CurrentExpressionDef'")
oldouter='research/nine-sharing-sign20-concrete-polynomial-bridge-check/attempt01/outer-result.json';assert runner.count(oldouter)==2;runner=runner.replace(oldouter,'research/nine-sharing-sign14-expression-eval-check/attempt01/outer-result.json')
rep('ba57aa78858d7003a243a23364b6972d8e74865cc639ad061db37077dc5b6f9a','c36f1e3212ad92b5e7ade6a276e551a57848a6c9e936d270d7bf4b810688c4ef')
rep('reviews/nine-sharing-sign20-concrete-polynomial-bridge-terminal-independent/check.py','reviews/nine-sharing-sign14-expression-eval-terminal-independent/check.py')
rep('e1744c21057a550a8a35912d1a0be4ba260855a7d219bb01ecc7e88eaf59309b','4e4e42a17bfdaca569da35ea60752aa257dae9622fb403b3df7b1257bc87b3ae')
rep('ed79c1bb35d1b6f5bf9014e275b372610c220a93c7bf9b815e66da12a5537c87',hashlib.sha256(manifest).hexdigest())
rep('e520ea55d5db51d161783a9841a40e7465a6bf544204c882945fdd6ef9cf9a7c',hashlib.sha256(survey.encode()).hexdigest())
rep("'Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard','Sign20DirectNoAliasTranslated'",','.join(repr(x) for x in names))
rep("if local=='Sign20DirectPolynomialBridge':expected_hash=base['rows'][0]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign20DirectPolynomialBridge.olean'", "if local=='Sign14CurrentExpressionDef':expected_hash=base['rows'][2]['object_sha256'];path=BASE/'lib/DiophantineConsistency/Sign14CurrentExpressionDef.olean'")
rep("elif local in ('Sign20DirectNoAliasNative','Sign20DirectNoAliasStandard'):","elif local in ("+','.join(repr(x) for x in names[:-1])+"):")
runner=runner.replace('Bounded sign20 no-alias endpoint attempt','Bounded sign14 symbolic degree upper on audited expression provider').replace('PASS sign20 no-alias endpoint attempt','PASS sign14 symbolic degree upper')
(check/'run.py').write_text(runner)
(check/'README.md').write_text('''# Sign14 symbolic degree-upper candidate

Four source-only stages propose arbitrary-port Fin17 totalDegree ≤124. The
runner authenticates the four-stage audited expression provider, including its
numeric outer exit, sources, objects, logs, direct guards and overlay. It
retains bounded resource guards and inherited ancestry qualifications. No Lean
degree, exact lower, external binding or iPRA endpoint is claimed yet.
''')
print(json.dumps({'runner_sha256':hashlib.sha256(runner.encode()).hexdigest(),'manifest_sha256':hashlib.sha256(manifest).hexdigest()},sort_keys=True))
