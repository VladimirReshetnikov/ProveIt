#!/usr/bin/env python3
"""Read-only pre-launch receipt/provider check; invokes no Lean process."""
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];S=D/'research/ordinary12-direct90-ipra-join/run-v6.py'
PIN='0c1d2e7302ff5a6d8f7c3ab3e5957401dc7efae7488264e47257db419acb5a2c'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sha(S)==PIN,'runner pin')
spec=importlib.util.spec_from_file_location('join_v6_review',S);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for p,h in m.PINS.items():need(sha(p)==h,'input pin '+str(p))
f=json.loads(m.FINAL.read_text());need(sha(m.FINAL)=='7af1eefd72bdfb476941ae311cd2ddcbfd06d55f2e47e245b2a773679457519e','manifest pin')
cone=json.loads(m.APPROVED_CONE.read_text());old=json.loads(m.CONE.read_text());n='ZFCinPA.QSchema'
normalized=json.loads(json.dumps(cone));correction=normalized.pop('stage419_source_correction');row=normalized['candidate_sources'][n]
need(row['source_sha256']=='0a8ffaa78ef63fe51f4b9c35ddea5ee28908204a4e4a06376b43c285c88ca0c1','repair hash')
row['source_sha256']='80c040905d9d0565f17f6cce8d8036549096088fc2a3559d9c7f6f752b8caa0a';row['source_bytes']=10989
need(normalized==old and correction['module']==n and correction['failed_terminal_sha256']==m.PINS[m.QSCHEMA_FAILED], 'cone repair normalization')
m.validate_final(f);m.manifest_recheck(f);receipts=m.producer_receipts(cone,f)
need(len(receipts)==425,'producer count')
base=[]
for i,name in enumerate(cone['topological_candidate'][:5],1):
 matching=[x for x in receipts[name] if x['index']==i]
 need(len(matching)==1 and '/compact12-ipra-expanded-cone-rebuild/observations/' in matching[0]['path'],'base stage '+str(i))
 base.append({'module':name,'receipt_sha256':matching[0]['sha256']})
need(any(Path(x['path']).resolve()==m.QSCHEMA_RECEIPT.resolve() and x['sha256']==m.PINS[m.QSCHEMA_RECEIPT] and x['index']==419 for x in receipts[n]),'QSchema producer')
name=cone['topological_candidate'][-1];end=[x for x in receipts[name] if x['index']==425]
need(len(end)==1 and end[0]['sha256']=='5483e0f8444fcaeaec8a68929f63a77d2aa3435d27fafa1b89c78eed3dc57977','completion receipt')
for p,h in m.PINS.items():need(sha(p)==h,'input changed '+str(p))
need(sha(S)==PIN and sha(m.FINAL)=='7af1eefd72bdfb476941ae311cd2ddcbfd06d55f2e47e245b2a773679457519e','runner or manifest changed')
print(json.dumps({'status':'PASS','runner_sha256':PIN,'producer_modules':len(receipts),'base_stages':base,
 'qschema_receipt_sha256':m.PINS[m.QSCHEMA_RECEIPT],'stage425_receipt_sha256':end[0]['sha256'],
 'scope':'read-only call to selected v6 preflight functions; no Lean execution or join'},indent=2,sort_keys=True))
