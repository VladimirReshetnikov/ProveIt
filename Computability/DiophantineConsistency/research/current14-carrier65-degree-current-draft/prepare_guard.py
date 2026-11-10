#!/usr/bin/env python3
"""Prepare current-port exact-degree specialization without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here=Path(__file__).resolve().parent;d=here.parents[1]
repo=next(p for p in here.parents if (p/'lakefile.toml').is_file())
previous=here.parent/'current14-carrier65-q-fields-check';check=here.parent/'current14-carrier65-degree-current-check'
srcdir=check/'src/DiophantineConsistency';srcdir.mkdir(parents=True,exist_ok=True)
src=srcdir/'Current14Carrier65DegreeCurrent.lean';shutil.copyfile(here/src.name,src)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[{'module':'DiophantineConsistency.Current14Carrier65DegreeCurrent','source':str(src.relative_to(repo)),
       'source_sha256':sha(src),'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)}]
manifest=check/'source-manifest.json';manifest.write_text(json.dumps({'rows':rows},indent=2)+'\n')
provider=Path('/tmp/current14-carrier65-degree-direct-retry-20261110')
state=here.parent/'current14-carrier65-degree-direct-retry-check/attempt01/state.json';outer=state.parent/'outer-result.json'
audit=d/'reviews/current14-carrier65-degree-direct-retry-terminal-independent/check.py'
old=(previous/'run.py').read_text()
old=old.replace("BASE=Path('/tmp/current14-carrier65-q-inputs-retry-20261110')",f"BASE=Path({str(provider)!r})")
old=old.replace("OUT=Path('/tmp/current14-carrier65-q-fields-20261110')","OUT=Path('/tmp/current14-carrier65-degree-current-20261110')")
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
                "draft=D/'research/current14-carrier65-degree-current-draft/Current14Carrier65DegreeCurrent.lean'")
old=re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'",f"need(sha(draft)=='{sha(here/src.name)}'",old)
old=old.replace("P/'src/DiophantineConsistency/Current14Carrier65QFields.lean'","P/'src/DiophantineConsistency/Current14Carrier65DegreeCurrent.lean'")
point=provider/'lib/DiophantineConsistency/Sign17ExactDegree.olean'
pin={'realpath':str(point.resolve()),'sha256':sha(point)}
prior=here.parent/'nine-sharing-sign17-exact-degree-check/attempt01/state.json'
prioraudit=d/'reviews/nine-sharing-sign17-exact-degree-terminal-independent/check.py'
extra=f'''beta_pin={pin!r}
beta=BASE/'lib/DiophantineConsistency/Sign17ExactDegree.olean'
need(beta.is_file() and str(beta.resolve())==beta_pin['realpath'] and sha(beta)==beta_pin['sha256'],'beta point pin')
beta_state=Path({str(prior)!r});beta_audit=Path({str(prioraudit)!r});bs=json.loads(beta_state.read_text())
need(sha(beta_state)=='{sha(prior)}' and bs['status']=='PASS' and sha(beta_audit)=='{sha(prioraudit)}','audited beta provider')
matched=[r for r in bs['rows'] if r['module']=='Sign17ExactDegree' and r['compile']['exit']==0]
need(len(matched)==1 and matched[0]['object_sha256']==beta_pin['sha256'],'beta equal-byte audited point')
'''
needle="draft=D/'research/current14-carrier65-degree-current-draft/Current14Carrier65DegreeCurrent.lean'"
assert needle in old;old=old.replace(needle,extra+needle)
old=old.replace("m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or",
                "m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65','DiophantineConsistency.Sign17ExactDegree') or")
needle="if mod=='DiophantineConsistency.CurrentEquationSyntax2011':expected=syntax_pin['sha256'];path=Path(syntax_pin['realpath'])"
assert needle in old;old=old.replace(needle,needle+"\n   elif mod=='DiophantineConsistency.Sign17ExactDegree':expected=beta_pin['sha256'];path=Path(beta_pin['realpath'])")
old=old.replace('PASS current14 Q field bindings and input bounds','PASS current-port exact Carrier65 degree')
(check/'run.py').write_text(old)
print('Prepared current-port specialization; no Lean invoked.')
