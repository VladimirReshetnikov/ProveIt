#!/usr/bin/env python3
"""Independent read-only reauthentication; no predecessor execution/import."""
import collections,hashlib,io,json,re,subprocess,zipfile
from pathlib import Path
ROOT='/home/codex/.codex/worktrees/2a71/Proofs'
STEM=Path('/tmp/review_surreal_foundations_abba38172')
PINS={'.md':'3ba28c536a6f6d34886c9fc0850243c61eb62ace24e57a3a9d4c577817bfdcec','.json':'3885ce42fd750f8cf5557349653ba089e7eb3a6d5425d9e42361a9ce83502c98','_metadata.py':'81bd6feb2927f0763b7d3d9929946edc28e91efea44692210b005db9a015dfb5'}
OUT=Path('/tmp/reauth_surreal_foundations_abba38172.json')
counts=collections.Counter(); evidence=[]
def check(ok,reason):
 if not ok:raise ValueError(reason)
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def data(c,p):return git('show',c+':'+p)
def lines(b):return b.splitlines(keepends=True)
def digest(b,r,where):
 check(len(b)==r['bytes'] and sha(b)==r['sha256'],'digest '+where)
def spans(b,rs,where):
 for r in rs:
  a,z=r['start_line'],r['end_line'];check(1<=a<=z<=len(lines(b)),'range '+where)
  digest(b''.join(lines(b)[a-1:z]),r,where);counts['read_spans']+=1;counts['span_lines_with_overlap']+=z-a+1
  evidence.append({'where':where,'start_line':a,'end_line':z,'sha256':r['sha256']})
def blob(r):
 b=data(r['commit'],r['path']);digest(b,r,r['path'])
 check(git('rev-parse',r['commit']+':'+r['path']).decode().strip()==r['blob_oid'],'blob OID')
 if 'lines'in r:check(len(lines(b))==r['lines'],'line count')
 spans(b,r.get('read_spans',[]),r['commit']+':'+r['path']);counts['git_blob_records']+=1
 return b
def labels(b):
 text=b.decode();return [{'label':m.group(1),'line':text.count('\n',0,m.start())+1}for m in re.finditer(r'\\label\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}',text)]
check(PINS,'missing final pins')
for suffix,h in PINS.items():check(sha(Path(str(STEM)+suffix).read_bytes())==h,'frozen input '+suffix)
j=json.loads(Path(str(STEM)+'.json').read_text())
check(j['helper_sha256']==PINS['_metadata.py'],'receipt helper pin')
c=j['commit'];p=j['parent'];check(git('rev-parse',c+'^').decode().strip()==p,'parent')
actualpaths=git('diff','--name-only',p,c).decode().splitlines()
check(actualpaths==[x['after']['path']for x in j['changed_files']],'complete changed path census')
by={}
for x in j['changed_files']:
 check(x['before']['commit']==p and x['after']['commit']==c,'changed commit scope')
 for side in ['before','after']:by[(side,x[side]['path'])]=blob(x[side])
for d in j['diffs']:
 b=git('diff','--no-ext-diff','--no-color','--unified=3',p,c,'--',d['path']);digest(b,d,'raw diff');check(len(lines(b))==d['lines'],'diff line count');counts['diffs']+=1
check([d['path']for d in j['diffs']]==actualpaths,'complete diff census')
context={r['path']:blob(r)for r in j['context']}
archivefiles={};source_labels={}
for a in j['archives']:
 b=blob(a);z=zipfile.ZipFile(io.BytesIO(b));names=[q.filename for q in z.infolist()if not q.is_dir()]
 check(len(names)==len(set(names)),'duplicate archive member names');check(names==[m['path']for m in a['members']],'complete member census')
 for m in a['members']:
  raw=z.read(m['path']);digest(raw,m,m['path']);archivefiles[(a['source_number'],m['path'])]=raw;counts['archive_members']+=1
  spans(raw,m.get('read_spans',[]),'archive '+m['path'])
  if 'labels'in m:
   labs=labels(raw);check(labs==m['labels'],'archive label inventory');source_labels[a['source_number']]=labs
   check(len(lines(raw))==m['lines'],'archive lines');check(raw.count(b'\\label')==m['raw_backslash_label_count'],'raw label count')
   check(len(re.findall(rb'\\begin\{question\}',raw))==m['question_environments'],'question census')
   check(len(re.findall(rb'\\bibitem(?:\[[^\]]*\])?\{',raw))==m['bibliography_entries'],'bibliography census')
 if 'supplied_checksum_entries_independently_matched'in a:
  ledger=next(m['path']for m in a['members']if m['path'].endswith('/SHA256SUMS'))
  rebuilt=[]
  for line in z.read(ledger).decode().splitlines():
   h,name=line.split(None,1);name=name.lstrip('*');path=ledger.rsplit('/',1)[0]+'/'+name
   check(sha(z.read(path))==h,'supplied checksum mismatch');rebuilt.append({'member':path,'sha256':h});counts['supplied_checksums']+=1
  check(rebuilt==a['supplied_checksum_entries_independently_matched'],'checksum coverage')
 counts['archives']+=1
for r in j['placements']:
 a=blob(r['first_placement']);b=blob(r['at_publication']);check(a==b==archivefiles[(r['source_number'],r['archive_member'])],'placement bytes');check(r['exact_archive_byte_match']is True,'placement flag');counts['placements']+=1
for ancestor in j['declared_ancestors_verified']:
 check(subprocess.run(['git','merge-base','--is-ancestor',ancestor,c],cwd=ROOT).returncode==0,'ancestry');counts['ancestor_checks']+=1
article=next(k for side,k in by if side=='after'and k.endswith('article.tex'))
for side in ['before','after']:check(labels(by[(side,article)])==j['host_labels'][side],'host label inventory')
old={r['label']for r in j['host_labels']['before']};new={r['label']for r in j['host_labels']['after']}
check(sorted(new-old)==j['host_labels']['added'] and sorted(old-new)==j['host_labels']['removed'],'label changes')
text=by[('after',article)].decode();refs=[]
for m in re.finditer(r'\\(?:[Cc](?:page)?ref|(?:eq|page|auto)?ref)\*?(?:\[[^\]]*\])?\{([^}]+)\}',text):
 for key in m.group(1).split(','):refs.append({'label':key.strip(),'line':text.count('\n',0,m.start())+1})
check(refs==j['host_labels']['literal_references'],'all literal reference occurrences')
check([r for r in refs if r['label']not in new]==j['host_labels']['missing_literal_references'],'missing literal refs')
expected={(n,r['label'],r['line'])for n,ls in source_labels.items()for r in ls};seen=[]
for r in j['source_label_routes']:
 key=(r['source_number'],r['source_label'],r['source_line']);check(key in expected,'source route existence');seen.append(key)
 check(r['target_labels']and all(t in new for t in r['target_labels']),'destination existence')
 if r['mode']=='prefix route':check(r['target_labels']==['hset:sf:'+r['source_label']],'prefix route')
 else:check(r['mode']=='manual subject route','unknown route convention')
 counts['routes']+=1
check(set(seen)==expected and len(seen)==len(expected),'complete unique routes')
prior=next(json.loads(b)for name,b in context.items()if name.endswith('review_new_foundations_f300069cf.json'))
for a in j['archives']:
 match=next(x for x in prior['archives']if x['path']==a['path']);check(match['sha256']==a['sha256']and match['commit']==a['commit'],'prior intake archive pin');counts['prior_archive_pins']+=1
actualtotals={'changed_paths':len(actualpaths),'before_after_blobs':2*len(actualpaths),'archives':counts['archives'],'archive_members':counts['archive_members'],'placed_files':counts['placements'],'checksum_entries':counts['supplied_checksums'],'host_labels_before':len(j['host_labels']['before']),'host_labels_after':len(j['host_labels']['after']),'new_sf_labels':sum(s.startswith('hset:sf:')for s in new-old),'source_labels':len(seen),'literal_reference_occurrences':len(refs),'selected_article_lines':sum(r['end_line']-r['start_line']+1 for r in next(x['after']['read_spans']for x in j['changed_files']if x['after']['path']==article)),'full_guide_diff_lines':next(d['lines']for d in j['diffs']if d['path'].endswith('/README.md'))}
check(actualtotals==j['totals'],'review totals')
out={'status':'PASS','input_pins':PINS,'helper_sha256':sha(Path(__file__).read_bytes()),'commit':c,'parent':p,'checks':dict(counts),'independently_derived_totals':actualtotals,'authenticated_spans':evidence,'limits':['Authenticated span bytes/ranges, not that a human actually read them.','Manual routes checked only for source/destination existence, not semantic or source-body equivalence.','No article/archived proof re-review, no PDF viewing/builds, no supplied/frozen code execution/import.','Fresh own metadata code used immutable Git and ZIP reads; no repository writes.']}
with OUT.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'status':'PASS','checks':dict(counts),'totals':actualtotals,'receipt_sha256':sha(OUT.read_bytes())},indent=2))
