#!/usr/bin/env python3
"""Prepare current expression exact-degree specialization without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here=Path(__file__).resolve().parent;d=here.parents[1]
repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
previous=here.parent/'current14-carrier65-q-fields-check';check=here.parent/'current14-carrier65-degree-expression-check'
srcdir=check/'src/DiophantineConsistency';srcdir.mkdir(parents=True,exist_ok=True)
src=srcdir/'Current14Carrier65DegreeExpression.lean';shutil.copyfile(here/src.name,src)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[{'module':'DiophantineConsistency.Current14Carrier65DegreeExpression','source':str(src.relative_to(repo)),
       'source_sha256':sha(src),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)}]
manifest=check/'source-manifest.json';manifest.write_text(json.dumps({'rows':rows},indent=2)+'\n')
provider=Path('/tmp/current14-carrier65-degree-direct-retry-20261110')
state=here.parent/'current14-carrier65-degree-direct-retry-check/attempt01/state.json';outer=state.parent/'outer-result.json'
audit=d/'reviews/current14-carrier65-degree-direct-retry-terminal-independent/check.py'
old=(previous/'run.py').read_text()
old=old.replace("BASE=Path('/tmp/current14-carrier65-q-inputs-retry-20261110')",f"BASE=Path({str(provider)!r})")
old=old.replace("OUT=Path('/tmp/current14-carrier65-q-fields-20261110')","OUT=Path('/tmp/current14-carrier65-degree-expression-20261110')")
start=old.index("STATE=D/'research/current14-carrier65-q-inputs-retry-check/attempt01/state.json'");end=old.index('\nroots=',start)
old=old[:start]+("STATE=D/'research/current14-carrier65-degree-direct-retry-check/attempt01/state.json';"
                "OUTER=STATE.parent/'outer-result.json';AUDIT=D/'reviews/current14-carrier65-degree-direct-retry-terminal-independent/check.py'")+old[end:]
old=re.sub(r"need\(sha\(STATE\)=='[0-9a-f]+'",f"need(sha(STATE)=='{sha(state)}'",old)
old=re.sub(r"need\(sha\(OUTER\)=='[0-9a-f]+'",f"need(sha(OUTER)=='{sha(outer)}'",old)
old=re.sub(r"need\(sha\(AUDIT\)=='[0-9a-f]+'",f"need(sha(AUDIT)=='{sha(audit)}'",old)
old=old.replace("len(base['rows'])==1 and base['rows'][-1]['module']=='Current14Carrier65QInputs'",
                "len(base['rows'])==2 and base['rows'][-1]['module']=='Current14Carrier65DegreeDirect'")
old=re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'",f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'",old)
old=old.replace("draft=D/'research/current14-carrier65-q-fields-draft/Current14Carrier65QFields.lean'",
                "draft=D/'research/current14-carrier65-degree-expression-draft/Current14Carrier65DegreeExpression.lean'")
old=re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'",f"need(sha(draft)=='{sha(here/src.name)}'",old)
old=old.replace("P/'src/DiophantineConsistency/Current14Carrier65QFields.lean'","P/'src/DiophantineConsistency/Current14Carrier65DegreeExpression.lean'")
point=provider/'lib/DiophantineConsistency/WeightedExpressionDegree.olean'
pin={'realpath':str(point.resolve()),'sha256':sha(point)}
extra=f'''weighted_pin={pin!r}
weighted=BASE/'lib/DiophantineConsistency/WeightedExpressionDegree.olean'
need(weighted.is_file() and str(weighted.resolve())==weighted_pin['realpath'] and sha(weighted)==weighted_pin['sha256'],'weighted expression point pin')
'''
needle="draft=D/'research/current14-carrier65-degree-expression-draft/Current14Carrier65DegreeExpression.lean'"
assert needle in old;old=old.replace(needle,extra+needle)
old=old.replace("m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or",
                "m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65','DiophantineConsistency.WeightedExpressionDegree') or")
needle="if mod=='DiophantineConsistency.CurrentEquationSyntax2011':expected=syntax_pin['sha256'];path=Path(syntax_pin['realpath'])"
assert needle in old;old=old.replace(needle,needle+"\n   elif mod=='DiophantineConsistency.WeightedExpressionDegree':expected=weighted_pin['sha256'];path=Path(weighted_pin['realpath'])")
old=old.replace('PASS current14 Q field bindings and input bounds','PASS conditional current expression exact degree')
(check/'run.py').write_text(old)
print('Prepared conditional expression specialization; no Lean invoked.')
