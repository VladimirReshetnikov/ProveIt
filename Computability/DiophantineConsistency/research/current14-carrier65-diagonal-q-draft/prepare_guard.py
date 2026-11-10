#!/usr/bin/env python3
"""Prepare actual diagonal Q degree client without invoking Lean."""
import hashlib
import json
import re
import shutil
from pathlib import Path

here = Path(__file__).resolve().parent
d = here.parents[1]
repo = next(p for p in here.parents if (p / 'lakefile.toml').is_file())
previous = here.parent / 'current14-carrier65-diagonal-uz-check'
check = here.parent / 'current14-carrier65-diagonal-q-check'
srcdir=check/'src/DiophantineConsistency';srcdir.mkdir(parents=True,exist_ok=True)
src=srcdir/'Current14Carrier65DiagonalQ.lean';shutil.copyfile(here/src.name,src)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rows=[{'module':'DiophantineConsistency.Current14Carrier65DiagonalQ',
       'source':str(src.relative_to(repo)),'source_sha256':sha(src),
       'imports':re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)}]
manifest=check/'source-manifest.json';manifest.write_text(json.dumps({'rows':rows},indent=2)+'\n')
old=(previous/'run.py').read_text()
old=old.replace("OUT=Path('/tmp/current14-carrier65-diagonal-uz-20261110')","OUT=Path('/tmp/current14-carrier65-diagonal-q-20261110')")
old=re.sub(r"need\(sha\(P/'source-manifest.json'\)=='[0-9a-f]+'",f"need(sha(P/'source-manifest.json')=='{sha(manifest)}'",old)
old=old.replace("draft=D/'research/current14-carrier65-diagonal-uz-draft/Current14Carrier65DiagonalUZ.lean'",
                "draft=D/'research/current14-carrier65-diagonal-q-draft/Current14Carrier65DiagonalQ.lean'")
old=re.sub(r"need\(sha\(draft\)=='[0-9a-f]+'",f"need(sha(draft)=='{sha(here/src.name)}'",old)
old=old.replace("P/'src/DiophantineConsistency/Current14Carrier65DiagonalUZ.lean'","P/'src/DiophantineConsistency/Current14Carrier65DiagonalQ.lean'")
qstate=here.parent/'current14-carrier65-q-actual-retry-check/attempt01/state.json';qouter=qstate.parent/'outer-result.json'
qaudit=d/'reviews/current14-carrier65-q-actual-retry-terminal-independent/check.py'
qobj=Path('/tmp/current14-carrier65-diagonal-p-20261110/lib/DiophantineConsistency/Current14Carrier65QCancel.olean')
pin={'realpath':str(qobj.resolve()),'sha256':sha(qobj)}
extra=f'''q_replay_state=D/'research/current14-carrier65-q-actual-retry-check/attempt01/state.json'
q_replay_outer=q_replay_state.parent/'outer-result.json'
q_replay_audit=D/'reviews/current14-carrier65-q-actual-retry-terminal-independent/check.py'
need(sha(q_replay_state)=='{sha(qstate)}' and json.loads(q_replay_state.read_text())['status']=='PASS','Q replay state')
need(sha(q_replay_outer)=='{sha(qouter)}' and json.loads(q_replay_outer.read_text())['outer_exit_code']==0,'Q replay outer')
need(sha(q_replay_audit)=='{sha(qaudit)}','Q replay audit')
qcancel_pin={pin!r}
qcancel=BASE/'lib/DiophantineConsistency/Current14Carrier65QCancel.olean'
need(qcancel.is_file() and str(qcancel.resolve())==qcancel_pin['realpath'] and sha(qcancel)==qcancel_pin['sha256'],'Q cancellation point pin')
'''
needle="draft=D/'research/current14-carrier65-diagonal-q-draft/Current14Carrier65DiagonalQ.lean'"
assert needle in old;old=old.replace(needle,extra+needle)
old=old.replace("m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65') or",
                "m in ('DiophantineConsistency.CurrentEquationSyntax2011','DiophantineConsistency.Carrier65','DiophantineConsistency.Current14Carrier65QCancel') or")
needle="if mod=='DiophantineConsistency.CurrentEquationSyntax2011':expected=syntax_pin['sha256'];path=Path(syntax_pin['realpath'])"
assert needle in old
old=old.replace(needle,needle+"\n   elif mod=='DiophantineConsistency.Current14Carrier65QCancel':expected=qcancel_pin['sha256'];path=Path(qcancel_pin['realpath'])")
old=old.replace('PASS actual diagonal V/S/U/Z degrees','PASS actual diagonal Q degree')
(check/'run.py').write_text(old)
print('Prepared actual diagonal Q degree client; no Lean invoked.')
