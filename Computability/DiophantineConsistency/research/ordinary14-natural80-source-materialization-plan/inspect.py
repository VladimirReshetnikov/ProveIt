#!/usr/bin/env python3
"""Derive source/output path blueprint without creating files or running Lean."""
import hashlib,json,re,sys
from pathlib import Path,PurePosixPath
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];plan=D/'research/ordinary14-natural80-ordered-provider-plan/plan.json'
def sha(b):return hashlib.sha256(b).hexdigest()
data=plan.read_bytes();assert sha(data)=='c99e528e09727720dbad410b475ea612e758fc4eb0d705c40ef4da555dac5e54'
a=json.loads(data); rows=a['candidate_stages'];assert len(rows)==189 and rows[-1]['module']=='Natural80Endpoint'
suffixes=a['bounded_collision_scan']['suffixes'];assert len(suffixes)==13 and len(set(suffixes))==13 and '.olean' in suffixes
srcs=set();outs=set();result=[];kinds={};sizes=0
for index,row in enumerate(rows,1):
 name=row['module'];assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',name),name
 rel=PurePosixPath(row['source']);assert not rel.is_absolute() and '..' not in rel.parts
 source=D/str(rel);assert source.is_file() and not source.is_symlink(),str(source)
 b=source.read_bytes();assert sha(b)==row['source_sha256'],name
 dst=PurePosixPath('src',*name.split('.')).with_suffix('.lean')
 out=PurePosixPath('lib',*name.split('.')).with_suffix('.olean')
 assert str(out.relative_to('lib'))==row['unreserved_output_name'],name
 assert dst not in srcs and out not in outs;srcs.add(dst);outs.add(out)
 kinds[row['kind']]=kinds.get(row['kind'],0)+1;sizes+=len(b)
 result.append({'stage':index,'module':name,'kind':row['kind'],'input_source':str(rel),
  'input_sha256':sha(b),'input_bytes':len(b),'proposed_source':str(dst),'proposed_primary_output':str(out)})
# The historical suffix list defines a bounded *hypothetical* output namespace.
# No destination path is inspected or created, and no root is reserved.
guards=set()
for row in result:
 primary=PurePosixPath(row['proposed_primary_output']);base=str(primary)[:-len('.olean')]
 for suffix in suffixes:
  target=base+suffix;assert target not in guards,(row['module'],target);guards.add(target)
assert kinds=={'qualified-source-candidate':5,'bare-inert-overlay':184}
assert len(srcs)==len(outs)==189 and len(guards)==189*13
assert not set(map(str,srcs)) & guards
print(json.dumps({'scope':'read-only unreserved source and output-name blueprint; no materialization, Lean or provider validation',
 'ordered_plan_sha256':sha(data),'source_count':len(result),'source_bytes':sizes,'source_kinds':kinds,
 'proposed_root':'<FRESH_ROOT_NOT_SELECTED_OR_RESERVED>','primary_output_count':len(outs),
 'bounded_output_suffixes':suffixes,'bounded_output_guard_name_count':len(guards),'entries':result},sort_keys=True,indent=2))
