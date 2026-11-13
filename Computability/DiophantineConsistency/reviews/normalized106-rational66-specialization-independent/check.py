#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2]; P=D/'research/normalized106-rational66-specialization'; O=P/'observations/attempt01';PRE=D/'research/normalized106-rational66-lean'
def H(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v: raise RuntimeError(s)
pins={'Normalized106RationalSpecialization.lean':'f4e4f191815ea9a826b1aeaac3fdfe3119b18aea30f7e919b7618bad11c71d2b','check01.py':'65e787ead46775ff5261010b70f09c267cbd275c2d6c53a6db2452b7e36c7cd0','observations/attempt01/result.json':'c3aac61e3de7684d63cac156e9b784cefa16dda0835dfd0775282d67ed612124','observations/attempt01/outer-terminal.json':'a688283eff351eea54d8c469644544bb449181917fe6aab9b12cb7a50d46a036'}
for f,h in pins.items():need(H(P/f)==h,'pin '+f)
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'result');need(t['session_id']==24944 and t['terminal_exit_code']==0 and t['returned_session_id'] is None,'outer exit')
for name,meta in r['guards_after'].items():
 p=Path(name.removeprefix('producer:'))
 if meta is None: need(not os.path.lexists(p),'unexpected '+name)
 else:
  target=meta.get('realpath',meta.get('resolved'));need(p.is_file() and str(p.resolve())==target and H(p)==meta['sha256'],'guard '+name)
  if 'link' in meta:need((os.readlink(p) if p.is_symlink() else None)==meta['link'],'link '+name)
need(H(O/'compile.log')==r['log_sha256']=='5e22e95d8158c52d7e9fae7bd921bd5d41bcdb2b718076420a45c87bb06cebb9','log');l=(O/'compile.log').read_text();need(l.count('depends on axioms:')==3 and l.count('Classical.choice')==3 and l.count('Quot.sound')==3 and l.count('propext')==3 and not any(x in l for x in ['sorryAx','warning:','error:']),'axioms')
obj=Path('/tmp/normalized106-rational66-specialization-priority-check01/Normalized106RationalSpecialization.olean');need(H(obj)==r['object_sha256']=='3efc847b71b735789230892c2929879672a2f4042acae0daab4b88c8aa3cff07','object')
prior=json.loads((PRE/'observations/attempt03/result.json').read_text());need(H(PRE/'observations/attempt03/result.json')=='6a172e130db1dac5c48afa6f0f9256231bfa9a23c3b748e5d7b0ee448922db42' and prior['exit']==0,'prior receipt')
prior_obj=Path('/tmp/normalized106-rational66-lean-priority-check03/Normalized106Rational66.olean');need(H(prior_obj)==prior['object_sha256']=='6978d8ef65c4cb77311bd9028143b4c6af95847e103a966936694eedc6890299','prior object')
need(any(k.endswith('/Normalized106Rational66.olean') and v and v['sha256']==H(prior_obj) for k,v in r['guards_after'].items()),'prior object direct guard')
need(any(k.endswith('/ModelCarrierSyntax.olean') and v and v['sha256']=='9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900' and H(Path(k.removeprefix('producer:'))) == v['sha256'] for k,v in prior['guards_after'].items()),'prior stage078 direct guard')
need(not any(k.endswith('/ModelCarrierSyntax.olean') for k in r['guards_after']),'unexpected specialization stage078 object guard')
print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','direct_guards':len(r['guards_after']),'outer_session':24944,'outer_exit':0,'lean_child_exit':0,'scope':'Historical stage-078 provider and previously checked identity object; no Lean replay or new transitive ancestry.'},sort_keys=True,indent=2))
