#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/normalized106-rational66-pair-replay';O=P/'observations/attempt01';A=D/'research/normalized106-rational66-pair';AO=A/'observations/attempt01'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'check01.py':'5d809f37ad1c43b190b377df92081037e45d34a365db2e0c81fd071fe269e52d','observations/attempt01/result.json':'d46f16e4147b8856ff8a315ec28f379202579a3d993e05efc766ce8e6cfebe76','observations/attempt01/outer-terminal.json':'0ff555a435ade1c1f406fdd8d3abddce2ed9d856599b65b1aba20b7e5d6304de'}
for f,h in pins.items():need(H(P/f)==h,'pin '+f)
need(H(A/'Normalized106RationalPair.lean')=='78a48cf3bca636ef1e9b78390957b2d00baa99104d16bbf4ec81254c78d21c38','source')
need(H(AO/'result.json')=='fc99f3b9ca1002e6bf75144820d727eb60a280fe20199aeff79ae79af77c3141' and H(AO/'outer-terminal.json')=='693b3b78b9f05e73f54a4dfeee7ca877e199376f4e72f2d5eb5083527fcb2da3','prior receipts')
r=json.loads((O/'result.json').read_text());a=json.loads((AO/'result.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==676,'result');need(t['session_id']==32461 and t['terminal_exit_code']==0 and t['returned_session_id'] is None,'outer exit')
need(r['lean_path']==a['lean_path'],'same provider search path');need(str(A/'Normalized106RationalPair.lean') in r['command'],'same source')
for name,meta in r['guards_after'].items():
 p=Path(name.split(':',1)[-1]);
 if meta is None:need(not os.path.lexists(p),'unexpected '+name)
 else:
  need(p.is_file() and str(p.resolve())==meta.get('realpath',meta.get('resolved')) and H(p)==meta['sha256'],'guard '+name)
  if 'link' in meta:need((os.readlink(p) if p.is_symlink() else None)==meta['link'],'link '+name)
need((O/'compile.log').read_bytes()==(AO/'compile.log').read_bytes() and H(O/'compile.log')==r['log_sha256']==a['log_sha256']=='e8a74c471b99f513888eb6fd1c7b7e3d2df715c51ed945f3a8f4865112ce342f','matching full log')
o=Path('/tmp/normalized106-rational66-pair-replay-priority-check01/Normalized106RationalPair.olean');q=Path('/tmp/normalized106-rational66-pair-priority-check01/Normalized106RationalPair.olean');need(o.read_bytes()==q.read_bytes() and H(o)==r['object_sha256']==a['object_sha256']=='7eb1409fde81bbc8fb224242dd71e575db55562fb7704764109d20e085c74a37','matching objects')
print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','guards':676,'outer_session':32461,'outer_exit':0,'child_exit':0,'source_and_object_and_complete_log_match':True,'scope':'Same-source same-provider replay; no Lean replay or fresh source-closure ancestry.'},indent=2,sort_keys=True))
