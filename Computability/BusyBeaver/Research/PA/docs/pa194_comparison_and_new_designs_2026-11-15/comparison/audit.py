#!/usr/bin/env python3
"""Offline audit of the frozen current-corpus census and every194-control representative.

Default mode uses only bundled files. It verifies all139spanning194-state
representatives and the disconnected diagnostic from their literal rows,
checks census arithmetic and attribution ledgers, and checks pinned Gitblob
identities of the original filed catalog. It does not claim to reparse every
historical table whose bytes are absent from this bundle.

Optional --refresh reparses the complete six incomingZIPs recursively and
compares with the frozen census. Supply --archive-dir to reuse localZIPs;
otherwise the exact pinned public URLs are downloaded into temporary files.
The original87-filed-packet census remains an attributed pinned catalog.
"""
from pathlib import Path
import argparse,collections,csv,hashlib,importlib.util,io,json,tempfile,urllib.request,urllib.parse,zipfile
HERE=Path(__file__).resolve().parent
PIN='8d31445d858761a8f6150c2e5012adae8895e932'
spec=importlib.util.spec_from_file_location('pinned_machine_classes',HERE/'catalog/machine_classes.py')
mc=importlib.util.module_from_spec(spec);spec.loader.exec_module(mc)

def j(p):return json.loads(p.read_text())
def sha(data):return hashlib.sha256(data).hexdigest()
def gitblob(data):return hashlib.sha1(('blob '+str(len(data))+'\0').encode()+data).hexdigest()

def offline():
 for e in j(HERE/'catalog_identities.json'):
  b=(HERE/'catalog'/e['path']).read_bytes()
  assert len(b)==e['size']and gitblob(b)==e['sha']and sha(b)==e['sha256'],e['path']
 filed=list(csv.DictReader((HERE/'catalog/MACHINES.tsv').open(),delimiter='\t'))
 filed_files=list(csv.DictReader((HERE/'catalog/MACHINE_FILES.tsv').open(),delimiter='\t'))
 incoming=j(HERE/'incoming_table_classes.json');occ=j(HERE/'current_table_occurrences.json')
 grouped=collections.defaultdict(list)
 for o in occ:grouped[o['table']].append(o)
 assert len(filed)==705 and len(filed_files)==13879 and len(incoming)==389
 assert {r['table_class']for r in incoming}==set(grouped)
 for r in incoming:
  os=grouped[r['table_class']]
  assert r['occurrences']==len(os)and r['direct_occurrences']==sum(o['zip_depth']==0 for o in os)
  assert sorted(r['all_origins'])==sorted(o['origin']for o in os)
  assert any(o['origin']==r['representative']and o['byte_sha256']==r['byte_sha256']for o in os)
 base={r['table_class']for r in filed};now=set(grouped);assert len(base|now)==747 and len(now-base)==42
 index=j(HERE/'frontier194_index.json');anns=j(HERE/'frontier194_annotated.json');ann={r['table_class']:r for r in anns}
 assert len(index)==len(anns)==140
 literal=[]
 for r in index:
  p=HERE/r['local_representative'];assert p.parent==HERE/'frontier194'
  b=p.read_bytes();assert sha(b)==r['byte_sha256']
  cls=mc.classify(b);assert cls['states']==194 and cls['table']==r['table_class']and len(cls['halting'])==1
  rows,states,_,_=mc.parse(b);maximum=max(mc.rooted(rows,states,q)[1]for q in states)
  assert maximum==ann[r['table_class']]['reachable']
  literal.append({'table_class':r['table_class'],'states':194,'maximum_reachable':maximum,'sha256':sha(b),'representative':r['local_representative']})
 assert sum(r['maximum_reachable']==194 for r in literal)==139
 assert [r['maximum_reachable']for r in literal if r['maximum_reachable']<194]==[3]
 packets=list(csv.DictReader((HERE/'packet_ledger93.csv').open()));families=list(csv.DictReader((HERE/'family_comparison.csv').open()))
 assert len(packets)==93 and sum(r['source']=='filed_catalog'for r in packets)==87 and sum(r['source']=='current_incoming'for r in packets)==6
 assert len(families)==27
 roles=collections.Counter(r['role']for r in anns)
 assert roles=={'reported principal construction':56,'principal construction':11,'supplementary construction':7,'research auxiliary':47,'research seed':4,'rejected':14,'diagnostic control':1}
 return {'status':'PASS','pin':PIN,'filed_catalog_classes':len(filed),'filed_historical_members':len(filed_files),'current_direct_tm_occurrences':sum(o['zip_depth']==0 for o in occ),'current_recursive_tm_occurrences':len(occ),'current_byte_payloads':len({o['byte_sha256']for o in occ}),'current_classes':len(now),'new_classes_vs_filed':len(now-base),'combined_catalog_classes':len(base|now),'spanning194_classes':139,'nonspanning194_diagnostics':1,'packet_records':len(packets),'families':len(families),'attributed_roles':dict(roles),'literal_representatives_reparsed':literal,'scope':'Fresh literal reclassification of all140bundled194-control tables; exact consistency and source-identity audit of frozen catalog/occurrence metadata. All-size incoming census reparse requires optional refresh. No arithmetic correctness is inferred from census membership.'}

def refresh(archive_dir):
 expected=j(HERE/'current_archives_identity.json');cache={};got=[];ziprefs=[]
 def scan(data,origin,depth=0):
  assert depth<=6
  ziprefs.append((origin,sha(data),depth))
  with zipfile.ZipFile(io.BytesIO(data))as z:
   for item in z.infolist():
    if item.is_dir():continue
    origin2=origin+'!'+item.filename
    if item.filename.endswith('.tm'):
     b=z.read(item);h=sha(b)
     if h not in cache:cache[h]=mc.classify(b)
     c=cache[h]
     got.append((origin2,depth,h,c['table'],c['states'],c['start'],c['reachable']))
    elif item.filename.endswith('.zip'):scan(z.read(item),origin2,depth+1)
 for e in expected:
  p=archive_dir/Path(e['path']).name
  if not p.exists():
   url='https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/'+PIN+'/'+urllib.parse.quote(e['path'])
   with urllib.request.urlopen(url,timeout=120)as response:data=response.read()
   p.write_bytes(data)
  data=p.read_bytes();assert len(data)==e['bytes']and sha(data)==e['sha256']and gitblob(data)==e['git_blob_sha']
  scan(data,e['path'])
 frozen=[(o['origin'],o['zip_depth'],o['byte_sha256'],o['table'],o['states'],o['start'],o['reachable'])for o in j(HERE/'current_table_occurrences.json')]
 assert sorted(got)==sorted(frozen)
 zf=j(HERE/'current_zip_refs.json');assert sorted(ziprefs)==sorted((z['path'],z['sha256'],z['depth'])for z in zf)
 return {'status':'PASS','archives':6,'exact_occurrences':len(got),'distinct_payloads':len(cache),'zip_references':len(ziprefs),'frozen_occurrence_census_reproduced':True,'scope':'Fresh recursive incoming.tm census, compared entry-by-entry; historical filed catalog is retained, not reconstructed from absent87oldZIPs.'}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=HERE/'verification.json');p.add_argument('--refresh',action='store_true');p.add_argument('--archive-dir',type=Path);a=p.parse_args()
 assert __debug__
 result=offline()
 if a.refresh:
  if a.archive_dir:
   a.archive_dir.mkdir(parents=True,exist_ok=True);result['refresh']=refresh(a.archive_dir)
  else:
   with tempfile.TemporaryDirectory(prefix='pa194-incoming-reaudit-')as d:result['refresh']=refresh(Path(d))
 else:result['refresh']={'executed':False}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k!='literal_representatives_reparsed'},indent=2))
if __name__=='__main__':main()
