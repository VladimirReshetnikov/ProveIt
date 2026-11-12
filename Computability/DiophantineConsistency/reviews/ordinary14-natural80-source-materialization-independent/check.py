#!/usr/bin/env python3
"""Independently check hypothetical path mapping; no outputs or Lean."""
from pathlib import Path,PurePosixPath
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def load(p,h):
 assert sha(p)==h,str(p)
 return json.loads(p.read_bytes())
plan=load(D/'research/ordinary14-natural80-ordered-provider-plan/plan.json','c99e528e09727720dbad410b475ea612e758fc4eb0d705c40ef4da555dac5e54')
b=load(D/'research/ordinary14-natural80-source-materialization-plan/blueprint.json','2543ed678993f5858048e51ee759a53847ad767c797cd25583d47352fdb99fb4')
rows=plan['candidate_stages'];assert len(rows)==b['source_count']==189 and rows[-1]['module']=='Natural80Endpoint'
assert b['proposed_root']=='<FRESH_ROOT_NOT_SELECTED_OR_RESERVED>'
suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash','.so','.dll','.dylib']
assert plan['bounded_collision_scan']['suffixes']==b['bounded_output_suffixes']==suffixes
source_paths=set();objects=set();alloutputs=set();entries=[];total=0;kinds={}
for stage,(row,entry) in enumerate(zip(rows,b['entries']),1):
 n=row['module'];assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*',n),n
 inp=row['source'];pp=PurePosixPath(inp)
 assert not pp.is_absolute() and '..' not in pp.parts and str(pp)==inp
 path=D.joinpath(*pp.parts);assert path.is_file() and not path.is_symlink()
 actual_hash=sha(path);assert actual_hash==row['source_sha256']
 # Construct destinations by explicit module components, independently of the
 # blueprint inspector's PurePosixPath.with_suffix mapping.
 stem='/'.join(n.split('.'));src='src/'+stem+'.lean';primary='lib/'+stem+'.olean'
 assert row['unreserved_output_name']==stem+'.olean'
 expected={'stage':stage,'module':n,'kind':row['kind'],'input_source':inp,
  'input_sha256':actual_hash,'input_bytes':path.stat().st_size,'proposed_source':src,'proposed_primary_output':primary}
 assert entry==expected,n
 assert src not in source_paths and primary not in objects
 source_paths.add(src);objects.add(primary);kinds[row['kind']]=kinds.get(row['kind'],0)+1
 total+=path.stat().st_size;entries.append(expected)
 for suffix in suffixes:
  dest='lib/'+stem+suffix
  assert dest not in alloutputs,(n,dest)
  alloutputs.add(dest)
assert len(b['entries'])==len(entries)==189 and len(source_paths)==len(objects)==189
assert len(alloutputs)==b['bounded_output_guard_name_count']==2457
assert not (source_paths & alloutputs)
assert kinds==b['source_kinds']=={'qualified-source-candidate':5,'bare-inert-overlay':184}
assert total==b['source_bytes']==597347 and b['primary_output_count']==189
print(json.dumps({'scope':'read-only path/hash reconstruction; no selected root, materialization, Lean or provider claim',
 'source_stages':len(entries),'qualified_source_candidates':5,'inert_overlay_drafts':184,
 'snapshot_source_bytes':total,'distinct_source_names':len(source_paths),
 'distinct_primary_outputs':len(objects),'distinct_bounded_output_names':len(alloutputs),
 'root_reserved':False},sort_keys=True,indent=2))
