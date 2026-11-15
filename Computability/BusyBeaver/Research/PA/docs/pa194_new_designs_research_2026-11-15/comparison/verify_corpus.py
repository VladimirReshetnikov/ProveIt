#!/usr/bin/env python3
"""Offline reclassification, identity and immediate-action congruence audit.

The catalogue counts include diagnostic/rejected experiments. This is not
a verification of 520 consistency theorems or a global lower-bound proof.
"""
from pathlib import Path
from collections import Counter
import argparse,csv,hashlib,json
import literal_inventory as lit
import machine_classes as mc
ROOT=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def congruence(rows,states,halt):
 colors={q:0 for q in states};colors[halt]=-1
 while True:
  sig={q:tuple((w,d,colors[t])for w,d,t in(rows[q,0],rows[q,1]))for q in states}
  uniq={s:i for i,s in enumerate(sorted(set(sig.values())))}
  new={q:uniq[sig[q]]for q in states};new[halt]=-1
  if len(set(new.values()))==len(set(colors.values())):return len(set(new.values()))-1
  colors=new
def main():
 assert __debug__
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=ROOT/'corpus_verification.json');a=ap.parse_args()
 identity=json.loads((ROOT/'source_identities.json').read_text())
 for r in identity['catalog']:
  b=(ROOT/'catalog'/r['path']).read_bytes();assert len(b)==r['bytes']and sha(b)==r['sha256']and blob(b)==r['git_blob_sha']
 classes=json.loads((ROOT/'census/classes.json').read_text());assert len(classes)==723
 frontier=json.loads((ROOT/'census/frontier194.json').read_text());fc={r['table_class']for r in frontier};assert len(fc)==520
 counts=Counter();verified=[]
 for i,r in enumerate(classes):
  b=(ROOT/'census'/r['representative']).read_bytes();assert sha(b)==r['sha256']
  c=mc.classify(b);assert c['table']==r['table_class']and c['states']==r['states']
  data=lit.parse_table(b);assert data
  if r['table_class']in fc:
   rows,states,halt=data;assert len(states)==194
   n=congruence(rows,states,halt);assert n==194;counts[n]+=1
  verified.append(dict(table_class=r['table_class'],sha256=sha(b),physical_states=c['states']))
  if(i+1)%100==0:print('Reclassified',i+1,'/',len(classes),flush=True)
 named=list(csv.DictReader((ROOT/'named_designs83.csv').open()));assert len(named)==len({r['table_class']for r in named})==83
 for r in named:assert r['table_class']in fc and sha((ROOT/r['local_representative']).read_bytes())==r['sha256']
 packets=list(csv.DictReader((ROOT/'packet_ledger97.csv').open()));assert len(packets)==97
 assert Counter(r['source']for r in packets)=={'filed_catalog':93,'current_incoming':4}
 families=list(csv.DictReader((ROOT/'family_comparison31.csv').open()));assert len(families)==31
 filed=list(csv.DictReader((ROOT/'catalog/MACHINES.tsv').open(),delimiter='\t'));keys={r['table_class']for r in filed};assert len(keys)==len(filed)==747
 assert len(keys|{r['table_class']for r in classes})==1137
 assert{r['table_class']for r in filed if r['states']=='194'}<=fc
 ann=list(csv.DictReader((ROOT/'frontier520_annotated.csv').open()));assert{r['table_class']for r in ann}==fc
 support_count=0
 if(ROOT/'support_scan.json').is_file():
  support=json.loads((ROOT/'support_scan.json').read_text());assert support['selected_files']==len(support['files'])==126 and not support['errors']
  for r in support['files']:
   b=(ROOT/r['local_payload']).read_bytes();assert len(b)==r['bytes']and sha(b)==r['sha256']and blob(b)==r['git_blob_sha']
  support_count=126
 result=dict(status='PASS',pin=identity['pin'],literal_representatives_reclassified=723,spanning194_classes=520,immediate_action_congruence_counts=dict(counts),named194_designs=83,families=31,deliveries=97,filed_catalogue_classes=747,combined_catalogue_classes=1137,outside_docs_payloads_verified=support_count,roles=dict(Counter(r['role']for r in ann)),representatives=verified,scope=__doc__)
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='representatives'},indent=2),flush=True)
if __name__=='__main__':main()
