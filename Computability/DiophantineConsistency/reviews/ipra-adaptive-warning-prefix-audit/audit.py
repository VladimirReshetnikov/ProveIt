#!/usr/bin/env python3
"""Authenticate matched strict-warning-stop prefixes before source merge."""
from pathlib import Path
import collections,hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[3];C=R/'Computability/DiophantineConsistency';Q=C/'reviews/ipra-adaptive-native-prefix-continuation';M=Q/'manifest.json';DR=Q/'replay.py';FIRST=C/'reviews/ipra-adaptive-prefix-audit/receipt.json';A=Path('/tmp/ipra-adaptive-native-continuation-1l4gfe_m');B=Path('/tmp/ipra-adaptive-native-continuation-l58un8d6');P=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');FIRSTPEER=Path('/tmp/ipra-adaptive-native-current-qpk97_3z');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest(); norm=lambda data,root:data.replace(str(root).encode(),b'$BUILD'); m=json.loads(M.read_text());mh=h(M);dh=h(DR);ah=h(__file__);a=json.loads((A/'state.json').read_text());b=json.loads((B/'state.json').read_text());asum=h(A/'state.json');bsum=h(B/'state.json')
assert a['status']==b['status']=='FAILED' and a['failure']==b['failure']=='AssertionError()'
assert a['manifest_sha256']==b['manifest_sha256']==mh and a['driver_sha256']==b['driver_sha256']==dh==m['driver_sha256'];assert h(FIRST)==m['prefix_receipt_sha256'] and h(FIRSTPEER/'state.json')==m['prefix_state_sha256']
assert h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256']
ra=a['records'];rb=b['records'];k=min(len(ra),len(rb));assert k==51
assert [r['name'] for r in ra[:k]]==[r['name'] for r in rb[:k]]==m['order'][:k]
warning='ZFCinPA.NativeSchemaSem';assert ra[k-1]['name']==warning
oldprefix=set(m['prefix']);newprefix=set(m['order'][:k]);fullprefix=oldprefix|newprefix;scheduled=set(m['affected']);seen=set(oldprefix);names=set(m['source_files']);rev=collections.defaultdict(set)
for n,p in m['source_files'].items():
 for x in re.findall(r'^import\s+([A-Z][\w.]*)',(R/p).read_text(),re.M):
  if x in names:rev[x].add(n)
changed='ZFCinPA.ValidatorConsistencyEquivalence';affected={changed};todo=[changed]
while todo:
 for x in rev[todo.pop()]:
  if x not in affected:affected.add(x);todo.append(x)
assert not (fullprefix & affected),sorted(fullprefix & affected)
warn_pattern=re.compile(r'^.*?:\d+:\d+: warning: (.*)$',re.M)
for x,y in zip(ra[:k],rb[:k]):
 assert x['name']==y['name'] and x['exit']==y['exit']==0
 assert set(x['direct_imports'])==set(y['direct_imports'])
 for n in x['direct_imports']:
  p=x['direct_imports'][n];q=y['direct_imports'][n];assert p['sha256']==q['sha256'] and norm(p['resolved_path'].encode(),A)==norm(q['resolved_path'].encode(),B)
  assert n not in scheduled or n in seen,(x['name'],n)
 if x['name']!=warning:assert x['object_sha256']==y['object_sha256'] and x['log_sha256']==y['log_sha256']
 seen.add(x['name'])

def inventory():return {str((Path(d)/f).relative_to(P/'lib')) for d,_,fs in os.walk(P/'lib',followlinks=True) for f in fs if f.endswith('.olean')}
def audit():
 assert h(M)==mh and h(DR)==dh and h(__file__)==ah and h(A/'state.json')==asum and h(B/'state.json')==bsum
 assert h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256'] and h(FIRST)==m['prefix_receipt_sha256'] and h(FIRSTPEER/'state.json')==m['prefix_state_sha256']
 assert all(h(R/p)==m['source_sha256'][n] for n,p in m['source_files'].items())
 assert all(h(Q/'sources'/(n.replace('.','/')+'.lean'))==m['source_sha256'][n] for n in m['affected'])
 assert inventory()==set(m['parent_objects']) and all(h(P/'lib'/f)==v for f,v in m['parent_objects'].items())
 assert all(h(PKG/f)==v['sha256'] and str((PKG/f).resolve())==v['resolved_path'] for f,v in m['external_direct'].items())
 for n,row in m['prefix_records'].items():
  assert h(FIRSTPEER/'lib'/(n.replace('.','/')+'.olean'))==row['object_sha256'] and h(FIRSTPEER/'logs'/(n.replace('.','_')+'.log'))==row['log_sha256']
  assert all(h(v['resolved_path'])==v['sha256'] for v in row['direct_imports'].values())
 for root,rows in [(A,ra),(B,rb)]:
  for row in rows[:k]:
   n=row['name'];rel=n.replace('.','/')+'.olean';log=n.replace('.','_')+'.log';txt=(root/'logs'/log).read_text()
   assert h(root/'lib'/rel)==row['object_sha256'] and h(root/'logs'/log)==row['log_sha256'] and row['exit']==0
   assert all(h(v['resolved_path'])==v['sha256'] for v in row['direct_imports'].values())
   assert 'error:' not in txt and 'sorryAx' not in txt
   ws=warn_pattern.findall(txt)
   if n==warning:assert len(ws)==6 and sum(w.startswith('automatically included section variable(s) unused') for w in ws)==4 and sum(w.startswith('This simp argument is unused:') for w in ws)==2
   else:assert 'warning:' not in txt
 wa=(A/'lib/ZFCinPA/NativeSchemaSem.olean').read_bytes();wb=(B/'lib/ZFCinPA/NativeSchemaSem.olean').read_bytes();assert norm(wa,A)==norm(wb,B) and wa.count(str(A).encode())==wb.count(str(B).encode())==1
 la=(A/'logs/ZFCinPA_NativeSchemaSem.log').read_bytes();lb=(B/'logs/ZFCinPA_NativeSchemaSem.log').read_bytes();assert norm(la,A)==norm(lb,B)
 return hashlib.sha256(norm(wa,A)).hexdigest(),hashlib.sha256(norm(la,A)).hexdigest()
objnorm,lognorm=audit();D.mkdir(parents=True,exist_ok=True)
for label,root in [('author',A),('independent',B)]:
 shutil.copyfile(root/'state.json',D/(label+'-strict-failed-state.json'));dest=D/(label+'-logs');dest.mkdir(exist_ok=True)
 for row in ra[:k]:
  f=row['name'].replace('.','_')+'.log';shutil.copyfile(root/'logs'/f,dest/f)
 shutil.copyfile(root/'lib/ZFCinPA/NativeSchemaSem.olean',D/(label+'-NativeSchemaSem.olean'))
shutil.copyfile(R/m['source_files'][changed],D/'ValidatorConsistencyEquivalence-before-merge.lean')
assert audit()==(objnorm,lognorm)
receipt={'status':'PASS','purpose':'Authenticate strict-warning-stop prefix before merge, explicitly accepting only the two described linter diagnostics for the final row; this is not an endpoint proof.','author_root':str(A),'peer_root':str(B),'author_state_sha256':asum,'peer_state_sha256':bsum,'manifest_sha256':mh,'driver_sha256':dh,'audit_sha256':ah,'first_prefix_receipt_sha256':m['prefix_receipt_sha256'],'old_prefix':m['prefix'],'new_prefix_count':k,'new_prefix':m['order'][:k],'author_rows':ra[:k],'peer_rows':rb[:k],'warning_module':warning,'normalized_warning_object_sha256':objnorm,'normalized_warning_log_sha256':lognorm,'warning_counts':{'unusedSectionVars':4,'unusedSimpArgs':2},'changed_source':changed,'changed_reverse_cone':sorted(affected),'source_count':len(m['source_files']),'parent_object_count':len(m['parent_objects']),'external_file_count':len(m['external_direct']),'boundary':'The 848-module ancestor is author-only; package-transitive and dynamically loaded ancestry remain inherited and untraced.'}
(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('WARNING_PREFIX_AUDIT_PASS',len(oldprefix),'+',k,'normalized',objnorm,flush=True)
