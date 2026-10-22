#!/usr/bin/env python3
"""Own full catalogue-entry/prefix audit; installs only the verified rendered PDF."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');S=Path(__file__).resolve().parent;O=S/'run1';A=S/'applied';P=R/'SetTheory/Cardinals/docs/reports'
def sha(b):return hashlib.sha256(b).hexdigest()
def entries(s):
 out=[]
 for m in re.finditer(r'^\\entry\{',s,re.M):
  i=m.start()+len('\\entry');args=[]
  for _ in range(5):
   while s[i].isspace():i+=1
   assert s[i]=='{';start=i;i+=1;level=1
   while level:
    c=s[i]
    if c=='\\':i+=2;continue
    if c=='{':level+=1
    if c=='}':level-=1
    i+=1
   args.append(s[start+1:i-1])
  out.append((s[m.start():i],args))
 return out
old=(A/'before-manifest.tex').read_text();cur=(P/'manifest.tex').read_text();before=entries(old);after=entries(cur);ctl=json.loads((A/'text-control.json').read_bytes())
assert len(before)==len(after)==290
assert [x[1][:3] for x in before]==[x[1][:3] for x in after]
assert [x[0] for x in before[:-1]]==[x[0] for x in after[:-1]]
assert after[-1][1][1]=='set-theory/zfc-closure-kernels'
assert after[-1][1][3]==before[-1][1][3]+ctl['archive_list_exact_append']
pat=r'\{\\raggedright\\footnotesize Placements (.*?)\;\narticles recoverable'
a=re.search(pat,old,re.S).group(1);b=re.search(pat,cur,re.S).group(1);assert b==a+ctl['placement_list_exact_append']
# Invert every permitted text operation to show the entire old manifest remains exact.
x=cur.replace(ctl['archive_list_exact_append'],'',1).replace(ctl['placement_list_exact_append'],'',1)
x=x.replace('187 numbered sources after supplemental batch~213. Its written reconciliation covers\nSources~1--164 and~167--187;','179 numbered sources after batch~212. Its written reconciliation covers\nSources~1--164 and~167--179;',1)
x=x.replace('{187 numbered sources, with written reconciliations for Sources~1--164 and~167--187;','{179 numbered sources, with written reconciliations for Sources~1--164 and~167--179;',1)
lo=x.index('Supplemental batch~213 reconciles Sources~180--187');hi=x.index(r'{\raggedright\footnotesize Placements',lo);x=x[:lo]+x[hi:];assert x==old
tracked=set(subprocess.check_output(['git','ls-tree','-d','-r','--name-only','HEAD','--','SetTheory/Cardinals/docs/reports'],cwd=R,text=True).splitlines())
dirs=['SetTheory/Cardinals/docs/reports/'+x[1][1] for x in after];assert len(set(dirs))==290 and set(dirs)<=tracked
readme=(P/'README.md').read_text();oldreadme=(A/'before-README.md').read_text();assert readme.startswith(oldreadme)
category=lambda s:s[s.index('| Category | Reports |'):s.index('## Later deliveries')]
assert category(readme)==category(oldreadme);nums=[int(x) for x in re.findall(r'\| (\d+) \|',category(readme))];assert sum(nums)==290
article='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/article.tex'
gitarticle=subprocess.check_output(['git','show','8a298fa5fbbc9d9d5db250c3671c9b26fe67cabb:'+article],cwd=R);assert (R/article).read_bytes()==gitarticle
labels=re.findall(rb'\\label(?:\[[^]]*\])?\{([^}]+)\}',gitarticle)
run=json.loads((O/'result.json').read_text());assert run['status']=='PDF_VALIDATED_AWAITING_VISUAL_REVIEW' and run['entries']==290 and run['diagnostics']==0
assert sha(cur.encode())==run['source_sha256'];pdf=(O/'manifest.pdf').read_bytes();assert sha(pdf)==run['pdf_sha256']
target=P/'manifest.pdf';prior=target.read_bytes();assert prior==subprocess.check_output(['git','show','8a298fa5fbbc9d9d5db250c3671c9b26fe67cabb:SetTheory/Cardinals/docs/reports/manifest.pdf'],cwd=R)
result={'status':'PASS_CATALOGUE_213_AFTER_VISUAL_REVIEW','write_commit':'8a298fa5fbbc9d9d5db250c3671c9b26fe67cabb','collection_reports':290,'host_sources':187,'tracked_entry_directories':290,'title_directory_main_fields_unchanged':True,'other289_entries_byte_identical':True,'category_table_unchanged':True,'source_archive_list_exact_append_only':True,'placement_list_exact_append_only':True,'whole_old_manifest_recovered_by_inverse_of_declared_edits':True,'collection_readme_old_prefix_exact':True,'base_article_sha256':sha(gitarticle),'base_article_labels_unchanged':len(labels),'visual_review':{'reviewer':'opening_encoder','pages':[2,123,141,142],'findings':[],'scope':'Scope count, complete new archive tail/source heading, new results/phase12 status and final placement tail. No clipping or overlap; exact finalfooter142.'},'manifest_sha256':sha(cur.encode()),'pdf_sha256':sha(pdf),'previous_pdf_sha256':sha(prior),'pdf_pages':run['pages'],'build_record_sha256':sha((O/'result.json').read_bytes()),'validator_sha256':sha(Path(__file__).read_bytes()),'owned_proof_source_edits':False,'staged':False}
target.write_bytes(pdf);(S/'final-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
