#!/usr/bin/env python3
"""Write all-size statistics and independently verify every pinned source blob."""
from pathlib import Path
import argparse, collections, csv, hashlib, json
p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--census',type=Path,required=True);a=p.parse_args()
data={name:json.loads((a.census/(name+'.json')).read_text()) for name in ['occurrences','identities','classes']}
sizes=sorted({x['states'] for rows in data.values() for x in rows})
rows=[]
for n in sizes:
 row={'states':n,'matrix_occurrences':sum(x['states']==n for x in data['occurrences']),'normalized_labeled_identities':sum(x['states']==n for x in data['identities']),'spanning_graph_classes':sum(x['states']==n and x['spanning'] for x in data['classes']),'nonspanning_literal_identities':sum(x['states']==n and not x['spanning'] for x in data['classes'])};rows.append(row)
with (a.census/'all_size_distribution.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
(a.census/'all_size_distribution.json').write_text(json.dumps(rows,indent=2)+'\n')
keys=['states','spanning','table_class','class_key','maximum_reachable','occurrences','normalized_sha256','representative','json_pointer','local_representative']
with (a.census/'all_size_classes.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=keys,extrasaction='ignore');w.writeheader();w.writerows(data['classes'])
manifest=json.loads(a.manifest.read_text());verified=[];errors=[];total=0
for info in manifest['files']:
 path=a.source/info['path']
 try:
  content=path.read_bytes();sha=hashlib.sha1(b'blob '+str(len(content)).encode()+b'\0'+content).hexdigest();total+=len(content)
  ok=(sha==info['sha'] and (info.get('size') is None or len(content)==info['size']))
  verified.append({'path':info['path'],'git_blob_sha1':sha,'size':len(content),'matches_manifest':ok})
  if not ok:errors.append({'path':info['path'],'expected':info,'actual_sha':sha,'actual_size':len(content)})
 except Exception as e:errors.append({'path':info['path'],'error':repr(e)})
report={'source_revision':manifest['pin'],'status':'PASS' if not errors else 'FAIL','files_checked':len(verified),'manifest_entries':len(manifest['files']),'bytes_checked':total,'errors':errors}
(a.census/'full_source_blob_verification.json').write_text(json.dumps(report,indent=2)+'\n')
with (a.census/'all_source_blobs.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=list(verified[0]));w.writeheader();w.writerows(verified)
print(json.dumps(report,indent=2))
