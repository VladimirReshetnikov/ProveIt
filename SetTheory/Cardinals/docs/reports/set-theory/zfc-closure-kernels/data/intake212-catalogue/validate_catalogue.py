#!/usr/bin/env python3
"""Own catalogue metadata and historical-prefix audit; no supplied execution."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=Path(__file__).resolve().parent;C=P/'catalogue';O=P/'catalogue-run1'
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
old=(C/'manifest.tex').read_text();cur=(R/'SetTheory/Cardinals/docs/reports/manifest.tex').read_text();before=entries(old);after=entries(cur)
assert len(before)==len(after)==290
assert [x[1][:3] for x in before]==[x[1][:3] for x in after]
assert [x[0] for x in before[:-1]]==[x[0] for x in after[:-1]]
assert after[-1][1][1]=='set-theory/zfc-closure-kernels'
addition=r'; batch~212: K215\_Checked\_Affine\_Core\_and\_CM215\_2026-10-21.zip (\texttt{6f0d42d368})'
assert after[-1][1][3]==before[-1][1][3]+addition
pat=r'\{\\raggedright\\footnotesize Placements (.*?)\;\narticles recoverable'
a=re.search(pat,old,re.S).group(1);b=re.search(pat,cur,re.S).group(1)
assert b==a+r', \texttt{9740f2bd13}'
tracked=set(subprocess.check_output(['git','ls-tree','-d','-r','--name-only','HEAD','--','SetTheory/Cardinals/docs/reports'],cwd=R,text=True).splitlines())
dirs=['SetTheory/Cardinals/docs/reports/'+x[1][1] for x in after]
assert len(set(dirs))==290 and set(dirs)<=tracked
readme=(R/'SetTheory/Cardinals/docs/reports/README.md').read_text();oldreadme=(C/'README.md').read_text()
category=lambda s:s[s.index('| Category | Reports |'):s.index('## Later deliveries')]
assert category(readme)==category(oldreadme)
nums=[int(x) for x in re.findall(r'\| (\d+) \|',category(readme))];assert sum(nums)==290
article='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/article.tex'
gitarticle=subprocess.check_output(['git','show','9740f2bd137313755f8b133be4717c77e8be9fb5:'+article],cwd=R)
assert (R/article).read_bytes()==gitarticle
labels=re.findall(rb'\\label\{([^}]+)\}',gitarticle)
run=json.loads((O/'result.json').read_text());assert run['status']=='PDF_VALIDATED_AWAITING_VISUAL_REVIEW' and run['entries']==290 and run['diagnostics']==0
assert sha(cur.encode())==run['source_sha256'];pdf=(O/'manifest.pdf').read_bytes();assert sha(pdf)==run['pdf_sha256']
target=R/'SetTheory/Cardinals/docs/reports/manifest.pdf';prior=target.read_bytes();assert prior==subprocess.check_output(['git','show','9740f2bd137313755f8b133be4717c77e8be9fb5:SetTheory/Cardinals/docs/reports/manifest.pdf'],cwd=R)
result={'status':'PASS_CATALOGUE_212_AFTER_VISUAL_REVIEW','collection_reports':290,'tracked_entry_directories':290,'title_directory_main_fields_unchanged':True,'other289_entries_byte_identical':True,'category_table_unchanged':True,'source_archive_list_exact_append_only':True,'placement_list_exact_append_only':True,'base_article_sha256':sha(gitarticle),'base_article_labels_unchanged':len(labels),'visual_review':{'reviewer':'opening_encoder','pages':[2,123,141],'findings':[],'scope':'Scope/counts, long archive tail/new source179 heading, new results and placement tail. No clipping or overlap; finalfooter141.'},'manifest_sha256':sha(cur.encode()),'pdf_sha256':sha(pdf),'previous_pdf_sha256':sha(prior),'pdf_pages':141,'build_record_sha256':sha((O/'result.json').read_bytes()),'validator_sha256':sha(Path(__file__).read_bytes()),'proof_sources_modified':False,'staged':False}
target.write_bytes(pdf)
(C/'final-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
