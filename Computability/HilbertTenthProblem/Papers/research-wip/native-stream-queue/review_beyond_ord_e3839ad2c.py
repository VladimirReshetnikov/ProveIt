#!/usr/bin/env python3
"""Fresh read-only intake metadata. Never runs or imports an archive member."""
import argparse
from collections import Counter,defaultdict
import hashlib
import io
import json
from pathlib import Path,PurePosixPath
import re
import subprocess
import zipfile

REPO=Path('/home/codex/.codex/worktrees/2a71/Proofs')
REV='e3839ad2c6be32ac5c6fdc422507da07f85f4fb6'
ARCHIVES={
 'Beyond_Ord_Class_Well_Orders.zip':'5dd3e2c30170c57bdd4353719333d2e5223f2ae5982cf9a6af5a58e61749537f',
 'Beyond_Ord_Research.zip':'c5a7aad5729d1c6dd46e4ad91919989a0f37c4a68eea3c3a3e96b13acb14d19c',
 'beyond_ord.zip':'03e0c90cd25e14e913bc80c7cf4c1c1add053e3bcf3f7f53b2c660c5d5614a8c',
 'class_orders_beyond_ord.zip':'ef9a694a68374ef4ae9dd3c1683e1b054045197d9558f0e25b22b07abd4f604d'}
FULL={
 'Beyond_Ord_Class_Well_Orders.zip':['README.md','PROOF_STATUS.md','SOURCE_AUDIT.md','verification_results.json','BUILD_REPORT.json','MANIFEST.sha256'],
 'Beyond_Ord_Research.zip':['README.md','PROOF_STATUS.md','finite_checks.json','SHA256SUMS'],
 'beyond_ord.zip':['README.txt','PROOF_STATUS.txt'],
 'class_orders_beyond_ord.zip':['README.txt','artifacts/finite_notation_results.json']}
TEX_READS={
 'Beyond_Ord_Class_Well_Orders.zip':('article.tex',[(400,472),(694,831),(977,1021),(1514,1649)]),
 'Beyond_Ord_Research.zip':('beyond_ord.tex',[(287,331),(481,518),(648,792),(794,883)]),
 'beyond_ord.zip':('beyond_ord.tex',[(118,172),(215,258),(426,505),(566,600),(857,950),(966,1004),(1333,1458),(2037,2086),(2198,2258)]),
 'class_orders_beyond_ord.zip':('class_orders_beyond_ord.tex',[(145,225),(1288,1338),(1595,1652),(1946,1992),(2079,2113),(2682,2727),(2964,3016)])}
HOST='Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/'
OLD='e1d2f3048b947801873a6e9ddc4e03736234b328'
OTHER='f158f27b46bd1efb5a771ffc3c07e64eea970501'
CONTEXT=[
 (REV,'docs/incoming/README.md',[(390,450)],'incoming workflow and retention rule'),
 (REV,'Algebra/SurrealNumbers/AGENTS.md',None,'full applicable working instructions'),
 (REV,HOST+'README.md',[(1,65)],'host routing and existing publication provenance'),
 (OLD,HOST+'article.tex',[(42845,42875),(53690,53770),(54060,54085)],'cited old GBC interface, retained question and incidental surrounding question text')]
SOURCE_LABELS=['swo:bw:ch:floors','swo:bw:ch:finite-changes','swo:bw:ch:normal-form-theorem','swo:bw:ch:convex-restriction','swo:bw:ch:equivalence']

def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=REPO)
def normalized(raw):return raw.decode('utf-8').replace('\r\n','\n').replace('\r','\n')
def spans(raw,selected):
 text=normalized(raw);lines=text.splitlines(keepends=True)
 if selected is None:selected=[(1,len(lines))]
 records=[]
 for first,last in selected:
  ck(1<=first<=last<=len(lines),'read span bounds')
  piece=''.join(lines[first-1:last]).encode('utf-8')
  records.append({'first_line':first,'last_line':last,'lines':last-first+1,'normalized_utf8_bytes':len(piece),'sha256':sha(piece)})
 return records

def labels(raw):
 text=normalized(raw)
 definitions=re.findall(r'\\label(?:\[[^\]]*\])?\{([^{}]+)\}',text)
 refs=[]
 for match in re.finditer(r'\\(?:[cC]ref|[aA]utoref|[pP]ageref|[eE]qref|[rR]ef)\*?\{([^{}]+)\}',text):
  refs.extend(p.strip() for p in match.group(1).split(','))
 keys=re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}',text)
 citations=[]
 for match in re.finditer(r'\\cite\w*\*?(?:\[[^\]]*\])*\{([^{}]+)\}',text):citations.extend(p.strip() for p in match.group(1).split(','))
 return {'definitions':len(definitions),'unique_definitions':len(set(definitions)),'labels':definitions,
  'duplicates':[k for k,v in Counter(definitions).items() if v>1],
  'literal_reference_occurrences':len(refs),'unresolved_literal_references':sorted(set(refs)-set(definitions)),
  'bibliography_keys':keys,'literal_citation_occurrences':len(citations),'unresolved_literal_citations':sorted(set(citations)-set(keys)),
  'question_environments':len(re.findall(r'\\begin\{question\}',text)),
  'scope':'Mechanical literal-source regex census; not TeX expansion or proof coverage.'}

def build():
 archive_records=[];identical=defaultdict(list);total_reads=0;total_lines=0;checksums=0
 for name,pin in ARCHIVES.items():
  path='docs/incoming/'+name;raw=git('show',REV+':'+path);ck(sha(raw)==pin,'archive pin')
  blob=git('rev-parse',REV+':'+path).decode().strip();z=zipfile.ZipFile(io.BytesIO(raw))
  infos=z.infolist();ck(len({i.filename for i in infos})==len(infos),'duplicate zip member')
  prefix=name[:-4]+'/'
  source_name,source_spans=TEX_READS[name]
  members=[];manifests=[]
  for info in infos:
   data=z.read(info);part=info.filename
   ck(not info.is_dir(),'unexpected directory member')
   ck(not PurePosixPath(part).is_absolute() and '..' not in PurePosixPath(part).parts,'member path safety')
   ck(part.startswith(prefix),'archive root')
   relative=part[len(prefix):]
   read=[]
   if relative in FULL[name]:read=spans(data,None)
   elif relative==source_name:read=spans(data,source_spans)
   total_reads+=len(read);total_lines+=sum(r['lines'] for r in read)
   member={'path':part,'bytes':len(data),'compressed_bytes':info.compress_size,'sha256':sha(data),'crc32':f'{info.CRC:08x}',
    'read_spans':read,'coverage':'full text read' if relative in FULL[name] else ('selected text spans' if read else 'metadata/hash only'),
    'executed_or_imported':False}
   if part.endswith('.tex'):member['literal_source_census']=labels(data)
   if read:member['utf8_line_count']=len(normalized(data).splitlines())
   if relative in ('MANIFEST.sha256','SHA256SUMS'):
    for line in normalized(data).splitlines():
     if not line.strip():continue
     expected,target=line.split(None,1);target=target.lstrip('*')
     delivered=z.read(prefix+target);ck(sha(delivered)==expected,'delivered checksum '+target)
     manifests.append({'manifest':part,'target':prefix+target,'sha256':expected,'matches':True});checksums+=1
   identical[sha(data)].append({'archive':path,'member':part})
   members.append(member)
  archive_records.append({'path':path,'commit':REV,'blob':blob,'bytes':len(raw),'sha256':pin,'members':members,'checksum_matches':manifests})
 contexts=[]
 for rev,path,selected,scope in CONTEXT:
  raw=git('show',rev+':'+path);ss=spans(raw,selected)
  contexts.append({'commit':rev,'path':path,'blob':git('rev-parse',rev+':'+path).decode().strip(),'bytes':len(raw),'sha256':sha(raw),'scope':scope,'read_spans':ss})
 routes=[]
 for rev in (OLD,OTHER):
  raw=git('show',rev+':'+HOST+'article.tex');text=normalized(raw)
  found=[]
  for label in SOURCE_LABELS:
   hits=[text.count('\n',0,m.start())+1 for m in re.finditer(r'\\label(?:\[[^\]]*\])?\{'+re.escape(label)+r'\}',text)]
   ck(len(hits)==1,'cited source label')
   found.append({'label':label,'line':hits[0]})
  routes.append({'commit':rev,'path':HOST+'article.tex','blob':git('rev-parse',rev+':'+HOST+'article.tex').decode().strip(),'sha256':sha(raw),'labels':found,'scope':'Label locations authenticated; complete linked bodies not compared or certified.'})
 return {'schema':'bounded beyond-Ord four-archive intake v1','reviewer_helper_sha256':sha(Path(__file__).read_bytes()),'arrival_commit':REV,
  'archives':archive_records,'contexts':contexts,'source_routes':routes,
  'identical_member_groups':[v for v in identical.values() if len(v)>1],
  'totals':{'archives':len(archive_records),'members':sum(len(a['members']) for a in archive_records),'archive_member_read_spans':total_reads,'archive_member_read_lines':total_lines,'delivered_checksum_matches':checksums,'context_read_spans':sum(len(c['read_spans']) for c in contexts),'context_read_lines':sum(s['lines'] for c in contexts for s in c['read_spans'])},
  'findings':[{'id':'I1','kind':'scope boundary','statement':'Finite set-coded supports and trees can contain arbitrary ordinal labels; ordinary effective notation requires a separately specified coefficient representation.'},
   {'id':'I2','kind':'scope boundary','statement':'Truth predicates, admitted class histories, ETR and inaccessible/beta-model assumptions are explicit semantic inputs, not Turing algorithms or paid integer gates.'},
   {'id':'I3','kind':'review priority','statement':'Two manuscripts claim the GBC-to-GB canonical-history refinement; the standalone choice-free power argument was checked, but full normal-form/history dependencies and fixed-point/spectrum proofs were not certified.'},
   {'id':'I4','kind':'provenance boundary','statement':'All four are distinct supplied manuscripts with overlapping topics; no full deduplication, precedence, source-body merge equivalence or external priority audit is asserted.'}],
  'scope':{'all_guides_read':True,'all_archive_members_hashed':True,'archived_programs_read':False,'supplied_programs_executed':False,'frozen_or_predecessor_helpers_executed':False,'builds_run':False,'PDFs_read_or_rendered':False,'external_citations_verified':False,'whole_manuscripts_certified':False,'new_fixed_arity_integer_compiler_established':False,'repository_mutated':False},'status':'PASS within stated bounded metadata/interface scope'}

if __name__=='__main__':
 p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);args=p.parse_args()
 value=build();raw=(json.dumps(value,sort_keys=True,indent=2)+'\n').encode()
 if args.output:
  with args.output.open('xb') as f:f.write(raw)
 else:ck(args.expect.read_bytes()==raw,'exact receipt')
 print(json.dumps({'status':'PASS','totals':value['totals'],'identical_member_groups':len(value['identical_member_groups'])},sort_keys=True))
