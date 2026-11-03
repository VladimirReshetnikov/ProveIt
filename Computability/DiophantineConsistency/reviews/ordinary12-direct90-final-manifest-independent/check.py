#!/usr/bin/env python3
"""Independently reconstruct the post-build direct/cone provider comparison."""
from hashlib import sha256
import json
import os
from pathlib import Path
import sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];B=D/'research/ordinary12-ipra-bridge'
P=D/'reviews/ordinary12-direct-main-ipra-import-preflight/observations'
SCAN=P/'attempt01/result.json';OVERLAY=P/'overlay01/result.json';FINAL=P/'final01/result.json'
OLD=B/'compact12-ipra-expanded-cone-preflight/result-v2.json'
CONE=B/'compact12-ipra-expanded-cone-rebuild-stage419-source-retry/cone-repinned.json'
HALT=D/'research/ordinary12-direct-main-probe/observations/haltv2-attempt01/terminal.json'
STAGE=B/'compact12-ipra-expanded-cone-rebuild-stage420/observations/batch-085/stage-0425'
LIB=Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib')
PINS={SCAN:'01c68aaea9e3548f25589694cbb0c4582f66c0fce7b072ba0d3a3765fec950a1',
 OVERLAY:'385173546dacd65f2c441c8ed2fd0dfd2086e0a59b2f14a98fbc9a0c4ca1eeae',
 FINAL:'7af1eefd72bdfb476941ae311cd2ddcbfd06d55f2e47e245b2a773679457519e',
 OLD:'35fce2dd6720ca1f2db8c39e42ad099f5653bf6b12939fcb77db3fd0fa252ed4',
 CONE:'b5eb6a00e30599c49a851b38746582c75f1eaba2e6c9a66ed6a8adec9f4dc424',
 HALT:'67fc1a846731aab86e408e198475e2cae6a21820575a3a21a21accf8a3f15e4d'}
SUFFIX=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
def need(x,m):
 if not x:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'dangling/non-file '+str(p))
 return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
for p,h in PINS.items():need(sha(p)==h,'pin changed '+str(p))
scan=json.loads(SCAN.read_text())['roots']['DirectMainHalt'];old=json.loads(OLD.read_text());new=json.loads(CONE.read_text())
f=json.loads(FINAL.read_text());previous=json.loads(OVERLAY.read_text());h=json.loads(HALT.read_text())
direct=set(scan['selected_ancestors']);cone=set(old['topological_candidate']);records=f['records']
need(len(direct)==765 and len(cone)==425 and not direct&cone and set(records)==direct|cone,'record membership')
need(new['topological_candidate']==old['topological_candidate'],'repinned cone order')
need(f['input_pins']=={str(p):PINS[p] for p in (SCAN,OVERLAY,OLD)} and f['overlay_root']==str(LIB),'manifest pins')
need(not f['report']['changed_during_comparison'] and not f['records_before'],'unstable capture')
missing=[];mismatch=[];matched=[];absent=[]
for n,row in records.items():
 need(row['in_direct']==(n in direct) and row['in_cone']==(n in cone),'membership flags '+n)
 if n in cone and row['overlay']['.olean'] is None:absent.append(n)
 if n in direct:
  need(row['selected_provider']==scan['resolved'][n],'source provider record '+n)
  value=row['overlay']['.olean'];target=row['selected_provider']['record']
  same=value is not None and value['sha256']==target['sha256']
  need(row['same_object_sha256']==same,'hash comparison flag '+n)
  if value is None:missing.append(n)
  elif same:matched.append(n)
  else:mismatch.append(n)
report=f['report']
need(sorted(missing)==report['direct_missing']==previous['missing'] and len(missing)==65,'missing direct set')
need(sorted(matched)==previous['matched'] and len(matched)==700,'matched direct set')
need(sorted(mismatch)==report['direct_mismatched']==previous['mismatched']==[] and not absent and not report['cone_missing'],'mismatch/missing cone')
need(report['direct_matched']==len(matched),'count')
paths=[Path(h['output_root'])]+[Path(x) for x in h['lean_path'].split(':')[:-1]]
def check_all():
 for n,row in records.items():
  stem=str(LIB/n.replace('.','/'))
  need({s:rec(stem+s) for s in SUFFIX}==row['overlay'],'live overlay/companion drift '+n)
  if n in direct:
   selected=row['selected_provider'];p=Path(selected['path']);src=str(p)[:-len('.olean')]
   need(rec(p)==selected['record'] and {s:rec(src+s) for s in SUFFIX}==selected['companions'],'selected provider drift '+n)
   rel=n.replace('.','/')+'.olean';first=next((base/rel for base in paths if (base/rel).is_file()),None)
   need(first==p,'selected first-resolution changed '+n)
   if n in matched:
    for s in SUFFIX:
     a=row['overlay'][s];z=selected['companions'][s]
     need((None if a is None else a['sha256'])==(None if z is None else z['sha256']), 'overlap companion mismatch '+n+s)
check_all();check_all()
stage=json.loads((STAGE/'terminal.json').read_text());name=new['topological_candidate'][-1]
need(stage['index']==425 and stage['module']==name and stage['success'] and stage['exit_code']==0 and stage['source_unchanged'] and stage['guards_unchanged'],'completion receipt')
need(stage['object_sha256']==records[name]['overlay']['.olean']['sha256'],'completion object')
need(stage['source_sha256']==new['candidate_sources'][name]['source_sha256'] and sha(STAGE/'source.lean')==stage['source_sha256'],'completion source')
need(sha(STAGE/'compile.log')==stage['log_sha256'] and not (STAGE/'compile.log').read_bytes(),'completion log')
need(all(rec(p)==v for p,v in stage['guards'].items()),'completion guards')
for p,h in PINS.items():need(sha(p)==h,'pin changed after audit '+str(p))
print(json.dumps({'status':'PASS','selected_direct':len(direct),'cone':len(cone),'direct_matched':len(matched),
 'direct_missing':len(missing),'direct_mismatched':len(mismatch),'cone_missing':len(absent),
 'stage425_receipt_sha256':sha(STAGE/'terminal.json'),'stage425_object_sha256':stage['object_sha256'],
 'final_manifest_sha256':PINS[FINAL],
 'scope':'external point-in-time selected-project object/companion comparison; no package-transitive/dynamic/source-object or final Lean join'},indent=2,sort_keys=True))
