#!/usr/bin/env python3
"""Fresh read-only Git metadata collector. Never imports report code or builds."""
import subprocess,hashlib,json,re
from pathlib import Path
ROOT='/home/codex/.codex/worktrees/2a71/Proofs'
OUT=Path('/tmp/review_reciprocal_c70ced0dd.json')
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
def sha(x):return hashlib.sha256(x).hexdigest()
def full(c):return git('rev-parse',c).decode().strip()
def content(c,p):return git('show',c+':'+p)
def pin(c,p):
 b=content(c,p);return {'commit':full(c),'path':p,'blob':git('rev-parse',c+':'+p).decode().strip(),'bytes':len(b),'sha256':sha(b)}
def span(c,p,a,b,scope='selected human-read source text'):
 raw=content(c,p).decode('utf8').replace('\r\n','\n').replace('\r','\n').splitlines(keepends=True)
 assert 1<=a<=b<=len(raw),(p,a,b,len(raw))
 return dict(pin(c,p),start_line=a,end_line=b,span_sha256=sha(''.join(raw[a-1:b]).encode()),normalization='UTF-8, CRLF/CR to LF, preserved final newline status',scope=scope)
label=re.compile(r'\\label(?:\[[^\]]*\])?\{([^}]+)\}')
bib=re.compile(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}')
commits=[]; files=[]; reads=[]; refs=[]
for short in ['c70ced0dd','b8bc36acc']:
 c=full(short);parent=full(c+'^');commits.append({'commit':c,'parent':parent})
 paths=git('diff','--name-only',parent,c).decode().splitlines()
 for p in paths:
  before=content(parent,p);after=content(c,p)
  d=git('diff','--no-ext-diff','--no-textconv','--unified=3',parent,c,'--',p)
  text=p.endswith(('.md','.tex'))
  f={'path':p,'before':pin(parent,p),'after':pin(c,p),'diff_bytes':len(d),'diff_sha256':sha(d),'coverage':'full raw text diff including hunk context read' if text else 'Git blob/diff authentication only; PDF not viewed or rebuilt'}
  if text:
   ds=d.decode();f['diff_line_count']=len(ds.splitlines());f['added_lines']=sum(x.startswith('+') and not x.startswith('+++') for x in ds.splitlines());f['removed_lines']=sum(x.startswith('-') and not x.startswith('---') for x in ds.splitlines())
   f['hunks']=[]
   for m in re.finditer(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',ds,re.M):
    oa,on,na,nn=(int(m[1]),int(m[2] or 1),int(m[3]),int(m[4] or 1));f['hunks'].append({'before_start':oa,'before_count':on,'after_start':na,'after_count':nn})
    if on:reads.append(span(parent,p,oa,oa+on-1,'full changed raw-diff hunk before/context read'))
    if nn:reads.append(span(c,p,na,na+nn-1,'full changed raw-diff hunk after/context read'))
   if p.endswith('.tex'):
    ls0=label.findall(before.decode());ls1=label.findall(after.decode());bs0=bib.findall(before.decode());bs1=bib.findall(after.decode())
    f['labels']={'before_count':len(ls0),'after_count':len(ls1),'ordered_unchanged':ls0==ls1,'ordered_sha256':sha(json.dumps(ls1,ensure_ascii=False,separators=(',',':')).encode())}
    f['bibliography_keys']={'before_count':len(bs0),'after_count':len(bs1),'ordered_unchanged':bs0==bs1}
    added='\n'.join(x[1:] for x in ds.splitlines() if x.startswith('+') and not x.startswith('+++'))
    for m in re.finditer(r'\\(?:lbl|replabel|cref|ref|leref|eqref)\{([^}]+)\}',added):
     for key in m[1].split(','):refs.append({'commit':c,'source_path':p,'label':key})
  files.append(f)
base='Algebra/SurrealNumbers/docs/'
pma=base+'foundations-and-computation/polish-models-of-omnific-arithmetic/article.tex'
dsn=base+'foundations-and-computation/definable-surreals-and-omnific-integers/article.tex'
extra={
 pma:[(33150,33217),(35312,35364),(35465,35480),(35535,35578),(35664,35728),(35767,35818),(34925,34985),(35025,35092),(36020,36135),(36160,36210),(36630,36688)],
 dsn:[(6605,6742),(6802,6824),(7100,7240),(7315,7382),(7837,7852),(8134,8164),(9195,9280),(9360,9410),(9465,9530),(10776,10808),(10990,11096),(11260,11283)],
 base+'surreal/real-vector-space-structure/README.md':[(250,275)],
 base+'foundations-and-computation/large-cardinal-embeddings-and-normal-forms/article.tex':[(945,995)],
 'Algebra/SurrealNumbers/AGENTS.md':[(1,182)],'docs/incoming/README.md':[(421,440)]}
for p,rs in extra.items():
 for a,b in rs:reads.append(span('c70ced0dd',p,a,b))
reads.append(span('b8bc36acc',pma,36706,36734))
reads.append(span('b8bc36acc','Algebra/SurrealNumbers/Surreal/Algebra/LaurentResidueChange.lean',1,290,'Lean declaration/source read only; not built'))
reads.append(span('b8bc36acc',base+'FORMALIZATION.md',658,658,'full single ledger row read; not a full-ledger audit'))
# Label target presence only; selected target text coverage is listed separately above.
labelpaths={f['path'] for f in files if f['path'].endswith('.tex')}|{pma,dsn}
bycommit={};targetfiles=[]
for c in {r['commit'] for r in refs}:
 idx={}
 for p in sorted(labelpaths):
  b=content(c,p);targetfiles.append(dict(pin(c,p),coverage='machine label indexing only unless a human-read span is separately listed'))
  for i,line in enumerate(b.decode().splitlines(),1):
   for k in label.findall(line):idx.setdefault(k,[]).append({'path':p,'line':i,'blob':git('rev-parse',c+':'+p).decode().strip()})
 bycommit[c]=idx
for r in refs:r['matches']=bycommit[r['commit']].get(r['label'],[])
result={'schema':'immutable reciprocal-note review v1','commits':commits,'executed_scope':{'fresh_metadata_collector_only':True,'supplied_or_frozen_programs_executed':False,'imports_of_report_code':False,'builds':False,'repo_mutation':False},'files':files,'human_read_spans':reads,'new_article_crossrefs':refs,'label_index_files':targetfiles,'findings':[{'id':'R1','commit':full('c70ced0dd'),'path':base+'surreal/real-vector-space-structure/README.md','lines':[258,262],'issue':'Image formula requires a nonzero; zero derivation has image {0}, while division by zero is undefined. Article and cited corollary retain the hypothesis.'},{'id':'R2','commit':full('b8bc36acc'),'path':pma,'lines':[36711,36729],'issue':'Correct CharZero scope repair. Retain prior false all-fields assertion: in F_2((X)), residue(X)=0 but coefficient X in every derivative is 2*a_2=0, so X is not a derivative. Original error retained in this review; no new error in corrected theorem scope.'}],'limits':['All changed README/article raw diffs read; only listed surrounding/cited spans read.','PDF bytes authenticated only; page counts, links in PDFs and builds not independently verified.','No external Gonshor/sign-expansion, forcing, or complete manuscript proof audit.','Label matches are presence evidence, not proof or reference-number verification.','No new ordinary-integer finite-arity paid compiler follows from these reciprocal notes.']}
result['totals']={'changed_files':len(files),'text_files':sum('hunks'in f for f in files),'pdf_files':sum(f['path'].endswith('.pdf') for f in files),'text_additions':sum(f.get('added_lines',0) for f in files),'text_deletions':sum(f.get('removed_lines',0) for f in files),'human_read_span_records':len(reads),'crossref_occurrences':len(refs),'crossrefs_without_index_match':sum(not r['matches'] for r in refs)}
with OUT.open('x')as f:json.dump(result,f,indent=2,ensure_ascii=False);f.write('\n')
print(json.dumps(result['totals'],indent=2))
print('unresolved',[(r['source_path'],r['label'])for r in refs if not r['matches']])
print('label_counts',[(f['path'],f['labels'])for f in files if 'labels'in f])
print('sha256',sha(OUT.read_bytes()))
