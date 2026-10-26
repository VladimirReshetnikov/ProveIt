#!/usr/bin/env python3
"""Offline evidence integrity checks only. Never imports or executes incoming code."""
from pathlib import Path
import argparse,hashlib,json,sys

def require(ok,msg):
 if not ok:raise ValueError(msg)
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def tree_hash(entries):
 parts=[]
 for e in sorted(entries,key=lambda x:(x['path']+('/' if x['type']=='tree' else '')).encode()):
  require('/' not in e['path'],'not a shallow tree')
  parts.append(e['mode'].lstrip('0').encode()+b' '+e['path'].encode()+b'\0'+bytes.fromhex(e['sha']))
 b=b''.join(parts);return hashlib.sha1(b'tree '+str(len(b)).encode()+b'\0'+b).hexdigest()
def check(root):
 b=root/'baseline_audit';m=json.loads((b/'DELIVERY_MANIFEST.json').read_text());n=0
 for e in m['files']:
  p=root/e['path'];data=p.read_bytes();require(len(data)==e['bytes'],'size mismatch '+e['path']);require(hashlib.sha256(data).hexdigest()==e['sha256'],'hash mismatch '+e['path']);n+=1
 receipts=json.loads((b/'TREE_RECEIPTS.json').read_text())
 for key,v in receipts['objects'].items():require(not v.get('truncated',False),'truncated '+key);require(tree_hash(v['tree'])==v['sha'],'Git tree mismatch '+key)
 for prefix in ['frozen','closing']:
  require(receipts['commits'][prefix]['tree']['sha']==receipts['objects'][prefix+'/root']['sha'],'commit root '+prefix)
  o=receipts['objects'];chain=[('root','Computability','computability'),('computability','DiophantineConsistency','dc'),('dc','research','research'),('research','lean-proof-simplification','proposals'),('root','docs','docs'),('docs','incoming','incoming')]
  for pa,name,ch in chain:require(next(e['sha']for e in o[prefix+'/'+pa]['tree']if e['path']==name)==o[prefix+'/'+ch]['sha'],'tree edge '+prefix+'/'+name)
 frozen={e['path']:e for e in receipts['objects']['frozen/proposals']['tree']};closing={e['path']:e for e in receipts['objects']['closing/proposals']['tree']}
 packets=[p for p,e in frozen.items()if e['type']=='tree'];require(len(packets)==43,'packet count');require(set(packets)=={p for p,e in closing.items()if e['type']=='tree'},'closing packet inventory');require(all(frozen[p]['sha']==closing[p]['sha']for p in packets),'closing packet changed')
 near=json.loads((b/'NEAREST_PRIOR_BINDINGS.json').read_text())
 for e in near['sources']:
  data=(root/e['path']).read_bytes();require(blob(data)==e['git_blob_sha1'],'nearest Git blob '+e['path']);require(hashlib.sha256(data).hexdigest()==e['sha256'],'nearest SHA256 '+e['path'])
 old=json.loads((b/'PRIOR_DELIVERY_BINDING.json').read_text())
 for e in old['verified_files']:
  p=b/'inherited/round6'/e['path'].split('baseline_audit/')[1];require(hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256'],'inherited delivery '+str(p))
 initial=json.loads((b/'FROZEN_INVENTORY.json').read_text());close=json.loads((b/'CLOSING_INVENTORY.json').read_text())
 require(len(initial['incoming_entries'])==4,'frozen incoming entries');require(len(close['incoming_entries'])==8,'closing incoming entries')
 fi={e['path']:e['sha']for e in initial['incoming_entries']};ci={e['path']:e['sha']for e in close['incoming_entries']};require(all(ci[p]==sha for p,sha in fi.items()),'old incoming changed');require(len(set(ci)-set(fi))==4,'new archive count')
 reads=json.loads((b/'DELIVERED_READING_BINDINGS.json').read_text());require(len(reads['files'])==127,'semantic read count')
 members=json.loads((b/'CLOSING_MEMBERS.json').read_text())+json.loads((b/'NEW_INCOMING_BINDINGS.json').read_text())['new_manuscript_members']
 mi={(e['archive'],e['member']):e for e in members}
 for e in reads['files']:
  data=(root/e['path']).read_bytes();require(blob(data)==e['git_blob_sha1'],'semantic Git blob '+e['path']);require(hashlib.sha256(data).hexdigest()==e['sha256'],'semantic SHA256 '+e['path']);require(mi[e['archive'],e['member']]['sha256']==e['sha256'],'archive member binding '+e['path'])
 status=json.loads((b/'AUDIT_STATUS.json').read_text());require(status['closing_scan_count']==1,'closing scan');require(not status['lean_executed'],'unexpected Lean claim');require(not status['incoming_scripts_executed'],'incoming execution claim')
 return {'status':'PASS','files_sha256_verified':n,'Git_tree_receipts_verified':len(receipts['objects']),'packet_trees_unchanged_at_closing':len(packets),'new_closing_archives':4,'complete_read_sources_verified':len(reads['files']),'nearest_sources_verified':len(near['sources']),'inherited_delivered_files_verified':len(old['verified_files']),'validation_scope':'Offline metadata/hash/tree consistency; not Lean compilation, semantic proof or archive refetch.','python_optimize':sys.flags.optimize}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);a=ap.parse_args()
 try: print(json.dumps(check(a.root.resolve()),indent=2))
 except (ValueError,KeyError,StopIteration,FileNotFoundError)as e:print('AUDIT FAIL: '+str(e),file=sys.stderr);raise SystemExit(1)
