#!/usr/bin/env python3
"""Narrow relocation/current-frontier addendum, preserving the main pinned census."""
from pathlib import Path
from zipfile import ZipFile
from collections import defaultdict,Counter
import subprocess,hashlib,json,sys,os
from audit_inventory import classify,sha
B=Path(__file__).resolve().parent;R=Path(os.environ.get('PA_AUDIT_REPO', str(B.parent/'ProveIt')))
OLD='8d31445d858761a8f6150c2e5012adae8895e932';NEW='ef0839bf15d8b556bc1e1634e6ad310adbcd4fe3'
blob=lambda b:hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
paths=['Computability/BusyBeaver/Research/PA','docs/incoming']
changes=[l.split('\t')for l in subprocess.check_output(['git','-C',str(R),'diff','--no-renames','--name-status',OLD,NEW,'--',*paths],text=True).splitlines()]
tr={}
for l in subprocess.check_output(['git','-C',str(R),'ls-tree','-r',NEW,*paths],text=True).splitlines():
 m,p=l.split('\t',1);tr[p]=m.split()[2]
arch_blobs=defaultdict(list)
incoming=B/'incoming' if (B/'incoming').exists() else R/'docs/incoming'
for p in sorted(incoming.glob('*.zip')):
 with ZipFile(p)as z:
  for i in z.infolist():
   if i.is_dir():continue
   b=z.read(i);arch_blobs[blob(b)].append('docs/incoming/'+p.name+'!'+i.filename)
added=[p for st,p in changes if st=='A'];matches=[{'path':p,'git_blob_sha1':tr[p],'old_archive_members':arch_blobs[tr[p]]}for p in added if tr[p]in arch_blobs];unmatched=[p for p in added if tr[p]not in arch_blobs]
oldpayload=json.loads((B/'census_all/payloads.json').read_text());known194={d['strong_graph_class']for d in json.loads((B/'census_all/frontier194.json').read_text())if d['has_spanning_root']}
tms=[p for st,p in changes if st!='D'and p.endswith('.tm')]
if tms:
 req=''.join(tr[p]+'\n'for p in tms).encode();raw=subprocess.check_output(['git','-C',str(R),'cat-file','--batch'],input=req);pos=0;records=[]
 for p in tms:
  e=raw.index(b'\n',pos);h,typ,sz=raw[pos:e].decode().split();pos=e+1;sz=int(sz);b=raw[pos:pos+sz];pos+=sz+1;assert h==tr[p]and typ=='blob'and blob(b)==h
  digest=sha(b);d=oldpayload.get(digest)
  if d is None:
   try:d=classify(b)
   except Exception as e:d={'error':str(e)}
  records.append({'path':p,'git_blob_sha1':h,'sha256':digest,'same_payload_in_original_census':digest in oldpayload,**d,'new_spanning194':bool(d.get('states')==194 and d.get('has_spanning_root')and d.get('strong_graph_class')not in known194)})
else: records=[]
summary={'original_pin':OLD,'late_pin':NEW,'change_counts':dict(Counter(st for st,p in changes)),'added_files':len(added),'added_files_matching_old_archive_git_blob_id':len(matches),'added_unmatched_files':unmatched,'new_or_modified_tm_files':len(records),'new_spanning194':sum(x['new_spanning194']for x in records),'all_new_tm_bytes_seen_in_original_census':all(x['same_payload_in_original_census']for x in records),'remaining_incoming_zip_paths':[p for p in tr if p.startswith('docs/incoming/')and p.endswith('.zip')],'modified_paths':[p for st,p in changes if st=='M'],'scope':'Every added source file compared by Git blob identity to all original outer-ZIP members; every new/modified .tm blob freshly retrieved and SHA-256 matched to original literal census. Metadata-only modified paths reviewed separately. No full rescan or original-census rewriting.'}
(B/'late_addendum.json').write_text(json.dumps({'summary':summary,'added_file_matches':matches,'tm_records':records},indent=2)+'\n')
print(json.dumps(summary,indent=2))
