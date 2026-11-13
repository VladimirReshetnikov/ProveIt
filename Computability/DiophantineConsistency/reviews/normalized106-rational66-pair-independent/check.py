#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/normalized106-rational66-pair';O=P/'observations/attempt01'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'Normalized106RationalPair.lean':'78a48cf3bca636ef1e9b78390957b2d00baa99104d16bbf4ec81254c78d21c38','check01.py':'57895123ffb2c8365a5c7947f0ee2354244ab67b87defec9429de589cd2ac313','observations/attempt01/result.json':'fc99f3b9ca1002e6bf75144820d727eb60a280fe20199aeff79ae79af77c3141','observations/attempt01/outer-terminal.json':'693b3b78b9f05e73f54a4dfeee7ca877e199376f4e72f2d5eb5083527fcb2da3'}
for f,h in pins.items():need(H(P/f)==h,'pin '+f)
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==672,'result');need(t['session_id']==40786 and t['terminal_exit_code']==0 and t['returned_session_id'] is None,'outer exit')
for name,meta in r['guards_after'].items():
 p=Path(name.split(':',1)[-1]);
 if meta is None:need(not os.path.lexists(p),'unexpected '+name)
 else:
  need(p.is_file() and str(p.resolve())==meta.get('realpath',meta.get('resolved')) and H(p)==meta['sha256'],'guard '+name)
  if 'link' in meta:need((os.readlink(p) if p.is_symlink() else None)==meta['link'],'link '+name)
need(H(O/'compile.log')==r['log_sha256']=='e8a74c471b99f513888eb6fd1c7b7e3d2df715c51ed945f3a8f4865112ce342f','log');l=(O/'compile.log').read_text();need(l.count('depends on axioms:')==1 and all(x in l for x in ['Classical.choice','Quot.sound','propext']) and not any(x in l for x in ['sorryAx','warning:','error:']),'axioms')
obj=Path('/tmp/normalized106-rational66-pair-priority-check01/Normalized106RationalPair.olean');need(H(obj)==r['object_sha256']=='7eb1409fde81bbc8fb224242dd71e575db55562fb7704764109d20e085c74a37','object')
for file,h in [('ModelCarrierSyntax.olean','9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900'),('ModelCarrierCurrent.olean','79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122'),('CurrentKernelData2011.olean','932f7951a955a29106d40b5e2b94feeb34c612164e3e606970dc0933a142a455'),('Normalized106RationalActual.olean','64287a9ab9685809828186004896973e5c46e252391fadc992aaaf8cc761ae7c')]:need(any(k.endswith('/'+file) and v and v['sha256']==h for k,v in r['guards_after'].items()),'expected provider '+file)
need(any(k.startswith('producer79:') and k.endswith('/ModelCarrierSyntax.olean') and v and v['sha256']=='9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900' for k,v in r['guards_after'].items()),'stage079 syntax input')
print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','guards':672,'outer_session':40786,'outer_exit':0,'child_exit':0,'scope':'Two separate conjuncts; captured historical provider, inherited package/transitive and dynamic ancestry; no Lean replay.'},indent=2,sort_keys=True))
