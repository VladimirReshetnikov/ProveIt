#!/usr/bin/env python3
"""Prepare an empty replay workspace; execute no search, allocator or proof."""
from pathlib import Path
import argparse,hashlib,json,shutil
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
here=Path(__file__).resolve().parent;evidence=here/'evidence';record=json.loads((evidence/'freeze.json').read_text());repo=a.repo.resolve();out=a.out.resolve()
assert not out.exists(),'Output must be fresh'
seed=repo/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
for name,pin in [('sites218.json','b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9'),('k218.native.tm','2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f')]:
 assert hashlib.sha256((seed/name).read_bytes()).hexdigest()==pin,('Seed changed',name)
selected=[]
for row in record['files']:
 name=Path(row['path'])
 if len(name.parts)!=1 or name.suffix not in ('.py','.cpp'):continue
 source=evidence/name;assert hashlib.sha256(source.read_bytes()).hexdigest()==row['sha256'];selected.append((name,source))
old="ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')";text=(evidence/'prepare.py').read_text();assert text.count(old)==1
out.mkdir(parents=True)
for name,source in selected:shutil.copyfile(source,out/name)
(out/'prepare.py').write_text(text.replace(old,'ROOT=Path('+repr(str(repo))+')'))
(out/'adapter.json').write_text(json.dumps({'status':'PATH_ONLY_REPLAY_PREPARED','repository':str(repo),'original_prepare_sha256':hashlib.sha256(text.encode()).hexdigest(),'adapted_prepare_sha256':hashlib.sha256((out/'prepare.py').read_bytes()).hexdigest(),'change':'Only repository ROOT literal; all source/table pins, source algorithms and limits unchanged. No computation executed.'},indent=2)+'\n')
print(out)
