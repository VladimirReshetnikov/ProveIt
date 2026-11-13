#!/usr/bin/env python3
"""Compare retained archive entries with the post-run source, row and log files."""
import hashlib,json,sys,tarfile
from pathlib import Path,PurePosixPath
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
terminal=D/'research/p72-current-base-extension-build-attempt02/terminal'
out=Path('/tmp/p72-current-base-extension-attempt02-20261105')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
archive=terminal/'stage-evidence.tar.gz'
assert sha(archive)=='884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541'
outer=json.loads((terminal/'outer-terminal.json').read_text())
assert outer['actual_session']==92122 and outer['exit_code']==0 and outer['observed_output']=='PASS all 681 P72 source-snapshot extension modules\n'
assert sha(terminal/'progress.json')==sha(out/'progress.json')=='f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a'
for name in ('0679.json','0680.json','0679-compile.txt','0680-compile.txt','source-snapshot.json','base-links.json','external-guard-before.json'):
 ref=out/('rows' if name.endswith('.json') and name[:1]=='0' else 'logs' if name.endswith('.txt') else '')/name
 assert sha(terminal/name)==sha(ref),name
counts={'rows':0,'logs':0,'src':0};seen=set()
with tarfile.open(archive,'r:gz') as tar:
 for m in tar:
  path=PurePosixPath(m.name)
  assert not path.is_absolute() and '..' not in path.parts and path.parts[0] in counts
  if m.isdir():continue
  assert m.isfile() and m.name not in seen;seen.add(m.name)
  data=tar.extractfile(m).read();ref=out.joinpath(*path.parts)
  assert hashlib.sha256(data).hexdigest()==sha(ref),m.name
  counts[path.parts[0]]+=1
assert counts=={'rows':681,'logs':1362,'src':681}
print(json.dumps({'status':'PASS_RETAINED_ARCHIVE_COMPARISON','archive_sha256':sha(archive),'outer_receipt_sha256':sha(terminal/'outer-terminal.json'),'recorded_outer_session':outer['actual_session'],'recorded_exit_code':outer['exit_code'],'progress_sha256':sha(terminal/'progress.json'),'files':counts,'scope':'Compares author-recorded outer receipt and retained archive with live stage files; no independent observation of the past process exit or Lean replay.'},indent=2,sort_keys=True))
