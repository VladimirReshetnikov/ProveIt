#!/usr/bin/env python3
"""Prepare exact phase-six status updates; apply only after final PASS and root GO.
No compiler, TeX process, supplied program, Git mutation, or phase-six evidence write.
"""
import argparse,difflib,hashlib,json,re
from pathlib import Path
from urllib.parse import unquote,urlsplit

ROOT=Path(__file__).resolve().parent
FORMAL='Computability/BusyBeaver/Research/ZFC/k225-formal/'
MANIFEST='SetTheory/Cardinals/docs/reports/manifest.tex'
def sha(b):return hashlib.sha256(b).hexdigest()
def readj(p):return json.loads(p.read_bytes())
def save(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def terminal(result_path,review_path):
 r=readj(result_path);v=readj(review_path)
 assert r['status']=='PASS' and v['status']=='PASS_LIVE_POST_AUDIT_REVIEW'
 assert r['primary_project_modules']==v['project_modules']==187
 assert r['basis_project_modules']==v['basis_project_modules']==184
 assert r['typed_audits']==v['typed_clients']==2
 assert r['axiom_reports']==v['axiom_reports']==10
 assert v['audit_warnings']==0
 assert r['fresh_modules']==v['fresh_modules']
 assert r['reused_modules']==v['reused_modules']
 assert r['fresh_modules']+r['reused_modules']==187
 assert r['project_linter_warnings']==v['project_warnings']
 assert v['result_sha256']==sha(result_path.read_bytes())
 for key in ['all_private_objects_logs_and_toolchain_rechecked_after_audits','basis_unchanged']:assert r[key] is True
 for key in ['all187_objects_rehashed_after_audits','all184_basis_objects_and_logs_unchanged','current_inventory_exact','toolchain_and_compiler_rehashed','exact_source_imports_and_dependency_sets']:assert v[key] is True
 assert len(r['audits'])==2 and {x['module'] for x in r['audits']}=={'EndpointAudit215','K215Audit'}
 for a in r['audits']:
  assert a['status']=='PASS'
  log=Path(a['log']);assert sha(log.read_bytes())==a['log_sha256']
  assert 'warning:' not in log.read_text() and 'error:' not in log.read_text()
 return dict(FRESH=str(r['fresh_modules']),REUSED=str(r['reused_modules']),WARNINGS=str(r['project_linter_warnings'])),dict(result=str(result_path.resolve()),result_sha256=sha(result_path.read_bytes()),live_review=str(review_path.resolve()),live_review_sha256=sha(review_path.read_bytes()))
def protected(before,after,path):
 if path==MANIFEST:
  for prefix in ('\\entrysource','{\\raggedright\\footnotesize Placements'):
   assert [l for l in before.splitlines() if l.startswith(prefix)]==[l for l in after.splitlines() if l.startswith(prefix)],prefix
  assert before.count('\\entry{')==after.count('\\entry{')==290
 if path=='docs/incoming/README.md':
  marker='## Queue status after batch 208 placement\n'
  assert before.split(marker,1)[1]==after.split(marker,1)[1], 'Historical queue paragraphs/ledger changed'
 # Replacements are the only allowed changes; unchanged remainder bound by plan.
 return True
def links(repo,path,before,after,pending):
 found=[]
 for target in set(re.findall(r'\]\(([^\s)]+)\)',after))-set(re.findall(r'\]\(([^\s)]+)\)',before)):
  if urlsplit(target).scheme or target.startswith('#'):continue
  target=unquote(target.split('#',1)[0]);full=(repo/path).parent/target
  relative=full.resolve().relative_to(repo.resolve()).as_posix()
  exists=full.is_file()
  allowed=relative==FORMAL+'verification/k215/simplification/phase6/README.md'
  assert exists or (pending and allowed),(path,target)
  found.append(dict(source=path,target=target,path=relative,exists=exists,pending_publication=not exists))
 return found
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
 ap.add_argument('--result',type=Path);ap.add_argument('--live-review',type=Path);ap.add_argument('--apply',action='store_true')
 a=ap.parse_args();assert bool(a.result)==bool(a.live_review),'Supply both actual receipts or neither'
 assert not a.apply or a.result, 'Canonical application requires final PASS and actual live review'
 plan=readj(ROOT/'plan.json');values={k:'{{'+k+'}}' for k in plan['actual_fields']};actual=None
 if a.result:values,actual=terminal(a.result,a.live_review)
 prepared=[];linkrows=[];patch=[]
 for row in plan['files']:
  rel=row['path'];p=a.repo/rel;b=p.read_bytes();assert sha(b)==row['before_sha256'],f'Current file changed: {rel}'
  text=b.decode();new=text
  for change in row['hunks']:
   assert new.count(change['old'])==1,(rel,change['reason'])
   replacement=change['new']
   for key,value in values.items():replacement=replacement.replace('{{'+key+'}}',value)
   new=new.replace(change['old'],replacement,1)
  assert protected(text,new,rel)
  if actual:assert '{{' not in new,rel
  linkrows.extend(links(a.repo,rel,text,new,not a.apply))
  nb=new.encode();prepared.append((rel,b,nb))
  patch.extend(difflib.unified_diff(text.splitlines(True),new.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
 assert len(prepared)==10
 out=a.out.resolve();out.mkdir(parents=True,exist_ok=False)
 for rel,b,nb in prepared:
  for folder,data in [('before',b),('after',nb)]:
   p=out/folder/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 (out/'status.patch').write_text(''.join(patch))
 record=dict(status='FINAL_STATUS_PREPARED' if actual else 'PLACEHOLDER_PREVIEW_ONLY',actual=actual,values=values,canonical_modified=False,files=[dict(path=rel,before_sha256=sha(b),after_sha256=sha(nb)) for rel,b,nb in prepared],protected_historical_sections=True,source_archive_and_placement_lines_exact=True,report_entries=290,source_count=178,pending_sources=[165,166],pending_arrivals=['5314ca0e6b','b07002a86b'],links=linkrows,plan_sha256=sha((ROOT/'plan.json').read_bytes()),updater_sha256=sha(Path(__file__).read_bytes()),patch_sha256=sha((out/'status.patch').read_bytes()),pdf_built=False)
 save(out/'result.json',record)
 if a.apply:
  # Check every input again before any canonical write. All before bytes are retained.
  for rel,b,_ in prepared:assert (a.repo/rel).read_bytes()==b,rel
  for rel,_,nb in prepared:(a.repo/rel).write_bytes(nb)
  for rel,_,nb in prepared:assert (a.repo/rel).read_bytes()==nb,rel
  record.update(status='APPLIED_FINAL_STATUS_AFTER_PASS',canonical_modified=True);save(out/'result.json',record)
 print(json.dumps(dict(status=record['status'],files=len(prepared),values=values,patch=str(out/'status.patch'))))
if __name__=='__main__':main()
