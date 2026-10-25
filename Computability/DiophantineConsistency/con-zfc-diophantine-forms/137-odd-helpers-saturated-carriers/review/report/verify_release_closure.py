#!/usr/bin/env python3
"""Static manifest/plan/import closure review; never imports release code."""
import argparse,ast,hashlib,json
from pathlib import Path,PurePosixPath

def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(s):
 p=PurePosixPath(s);need(bool(s) and s!='.' and p.as_posix()==s and not p.is_absolute() and '..' not in p.parts and '\\' not in s and ':' not in s,'unsafe path '+s)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--release',type=Path,required=True);ap.add_argument('--working',type=Path);a=ap.parse_args();r=a.release
 p=json.loads((r/'REPRODUCE_PLAN.json').read_text());c=json.loads((r/'CODE_REVIEW.json').read_text());by={x['path']:x for x in c['files']};need(len(by)==len(c['files']),'duplicate reviewed source')
 def file(rel):
  q=r/rel
  if not q.is_file() and a.working:q=a.working/rel
  need(q.is_file(),'missing source '+rel);return q
 imports=[];missing=[];sources=[]
 for rel,row in by.items():
  safe(rel);q=file(rel);need(sha(q)==row['sha256'] and q.stat().st_size==row['bytes'],'review hash differs '+rel)
  sources.append({'path':rel,'sha256':sha(q)})
  if not rel.endswith('.py'):continue
  tree=ast.parse(q.read_text());need(not any(isinstance(x,ast.Assert) for x in ast.walk(tree)),'removable assert in '+rel)
  for n in ast.walk(tree):
   names=([x.name for x in n.names] if isinstance(n,ast.Import) else [n.module] if isinstance(n,ast.ImportFrom) and n.module else [])
   for mod in names:
    for base in [PurePosixPath(rel).parent,PurePosixPath(rel).parent/'vendor',PurePosixPath('.')]:
     test=str(base/(mod.replace('.','/')+'.py'))
     if (r/test).is_file() or (a.working and (a.working/test).is_file()):
      imports.append({'importer':rel,'module':test});
      if test not in by:missing.append(test)
      break
  if rel=='integer/check.py':
   test='integer/coefficients/recipe/source34_builder.py';imports.append({'importer':rel,'dynamic_module':test});need(test in by,'missing dynamic recipe')
 need(not missing,'unreviewed local modules '+str(sorted(set(missing))))
 for mode in ['normal','optimized']:
  def exp(s):return s.replace('{mode}',mode).replace('{mode_upper}',mode.upper()).replace('{check_suffix}','_OPTIMIZED' if mode=='optimized' else '')
  for key in ['rebuild_files','compare_files']:
   vals=list(map(exp,p[key]));need(len(vals)==len(set(vals)),'duplicate '+key)
   for rel in vals:safe(rel)
  need(set(map(exp,p['rebuild_files']))<=set(map(exp,p['compare_files'])),'uncompared rebuilt output')
  for s in p['commands']:
   args=list(map(exp,s['args']));root=s.get('cwd','');rel=str(PurePosixPath(root)/args[0]);safe(rel);need(rel in by,'unreviewed plan command '+rel)
   if root:safe(root)
   if s.get('stdout_reference'):safe(exp(s['stdout_reference']))
 for rel in p['negative_control_targets'].values():safe(rel)
 print(json.dumps({'status':'PASS','scope':'Static source hashes, all explicit plan entry points, local import closure, dynamic source34 recipe, safe paths, no removable assertions, exact-rebuild comparison coverage. No release program executed.','assembled_release_only':a.working is None,'plan_sha256':sha(r/'REPRODUCE_PLAN.json'),'code_review_sha256':sha(r/'CODE_REVIEW.json'),'commands_per_mode':len(p['commands']),'regenerated_paths_per_mode':len(p['rebuild_files']),'reviewed_source_files':len(by),'local_import_edges':imports,'sources':sources},indent=2))
if __name__=='__main__':main()
