#!/usr/bin/env python3
"""Read-only audit of the batch213 Write; no delivered code or proof execution."""
import argparse,base64,gzip,hashlib,json,re,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();R=a.repo.resolve();H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels';D=H/'data/intake213-review'
def h(b):return hashlib.sha256(b).hexdigest()
def obj(rel,commit='0388d93df69c7af1bd0b3e084d1df95218a6e63f'):return subprocess.check_output(['git','show',commit+':'+rel],cwd=R)
def rel(p):return p.relative_to(R).as_posix()
paths=[H/'intake-213.md',H/'README.md',R/'docs/incoming/README.md',D/'README.md']
links=[]
for f in paths:
 text=f.read_text()
 # Historical existing host/index links are outside this bounded new-content check.
 if f==H/'README.md':text=text.split('[Batch 212]',1)[0]
 if f==R/'docs/incoming/README.md':text=text.split('## Upstream parallel placement',1)[0]+'\n'+next(x for x in text.splitlines() if x.startswith('| 213 |'))
 for x in re.findall(r'\]\(([^)]+)\)',text):
  if '://' in x:continue
  q=(f.parent/x.split('#')[0]).resolve();assert q.exists(),(rel(f),x)
  links.append({'file':rel(f),'target':x})
old=obj(rel(H/'README.md')).decode();now=(H/'README.md').read_text()
assert old.split('[Batch 212]',1)[1]==now.split('[Batch 212]',1)[1]
assert now.split('[Batch 213]',1)[0]==old.split('[Batch 212]',1)[0].replace('**179 numbered sources**','**187 numbered sources**',1).replace('Sources 1–164 and 167–179','Sources 1–164 and 167–187',1)
old=obj('docs/incoming/README.md').decode();now=(R/'docs/incoming/README.md').read_text()
assert old.split('## Current queue',1)[0]==now.split('## Current queue',1)[0], 'proof-checkpoint prefix changed'
line=next(x for x in now.splitlines() if x.startswith('| 213 |'))
assert old.split('## Upstream parallel placement',1)[1]==now.replace(line+'\n','',1).split('## Upstream parallel placement',1)[1]
assert 'Sources 165–166' in now and '290' in line
q=json.loads((D/'quotation-control.json').read_bytes())
for x in q['rows']:
 b=obj(x['path'],q['commit']);assert h(b)==x['source_sha256'];assert b.decode().splitlines()[x['line']-1]==x['quote']
index=json.loads((D/'source-review-index.json').read_bytes());archive=(D/'source-review.json.gz').read_bytes();assert h(archive)==index['archive_sha256']
bundle=json.loads(gzip.decompress(archive));assert bundle['format']=='exact_source_review_records_v1'
records={}
for x in bundle['members']:
 assert x['path'] not in records and not Path(x['path']).is_absolute() and '..' not in Path(x['path']).parts
 records[x['path']]=base64.b64decode(x['content_base64'],validate=True)
assert sorted(records)==sorted(x['path'] for x in index['members'])
for x in index['members']:
 b=records[x['path']];assert len(b)==x['bytes'] and h(b)==x['sha256']
 assert not x['path'].endswith(('.olean','.ilean','.olean.private','.olean.server','.vo','.vos','.vok','.pyc'))
for k in ['interfaces','semantic','contracts']:assert records[k+'/review.md']==(D/(k+'-review.md')).read_bytes()
for k in ['interfaces','semantic','contracts']:
 stored=(H/'data/intake213-placement'/f'{k}-review.json').read_bytes();assert stored==obj(rel(H/'data/intake213-placement'/f'{k}-review.json'))
# Labels are unchanged: this Write edits no delivered article or TeX source.
base_tex=subprocess.check_output(['git','ls-tree','-r','--name-only','0388d93df69c7af1bd0b3e084d1df95218a6e63f','--',rel(H)],cwd=R).decode().splitlines()
tex=[]
for f in base_tex:
 if not f.endswith('.tex'):continue
 b=obj(f);assert (R/f).read_bytes()==b,f
 tex.append({'path':f,'sha256':h(b),'labels':len(re.findall(rb'\\label(?:\[[^]]*\])?\{',b))})
result={'status':'PASS_WRITE_LINKS_HISTORY_QUOTES_ARCHIVE_LABELS','scope':'Own read-only metadata control; no compiler, supplied executable, new mathematical proof or independent phase12 actual audit.','placement':'0388d93df69c7af1bd0b3e084d1df95218a6e63f','new_content_links':links,'unchanged_host_history_after_batch212':True,'unchanged_incoming_proof_prefix':True,'unchanged_incoming_history_after_parallel_placement_except_new213row':True,'exact_historical_source_quotes':len(q['rows']),'review_archive_members':len(index['members']),'unchanged_tex':tex,'files':[{'path':rel(f),'bytes':len(f.read_bytes()),'sha256':h(f.read_bytes())} for f in paths]}
a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'links':len(links),'source_quotes':len(q['rows']),'review_members':len(index['members']),'unchanged_tex':len(tex),'labels':sum(x['labels'] for x in tex)}))
