#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-unscaled66-vs106-fresh';O=P/'attempt01';PRE=D/'reviews/current2011-unscaled66-fresh-base-independent'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for n,h in {'Unscaled66Vs106Fresh.lean':'d734dcf78369eaa9b6b52ac4a4730d39e82aab4560e324b34cb7f05c02a23149','check01.py':'25ac9f8772b3132a30756d689698ed22fa7ae4f5e68c14d7a4f928c464317429','attempt01/result.json':'6bd021c2361b4d48daa649d848dac7e8788a5a8d847f07beb07d42352bcba4af','attempt01/outer-observation.json':'1f94e9543f399aeeda73b1290c04aef7f2d3b20e1ea70490ea68c950853fe4be'}.items():need(H(P/n)==h,'pin '+n)
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-observation.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==337,'success receipt');need(t['session_id']==95783 and t['observed_outer_exit']==0,'outer exit')
for n,m in r['guards_after'].items():
 p=Path(m['path'] if m is not None and 'path' in m else n.rsplit(':',1)[-1]);
 if m is None:need(not os.path.lexists(p),'unexpected '+n)
 else:need(p.is_file() and str(p.resolve())==m['realpath'] and H(p)==m['sha256'] and ('path' not in m or m['path']==str(p)),'guard '+n)
for file,h in [('Current2011Unscaled66Fresh.olean','43de05d18c2854a224ebcd01c560cb5327752118ee08164277f38e7611a01b00'),('FreshModel106.olean','d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942')]:need(any(k.endswith('/'+file) and v and v['sha256']==h for k,v in r['guards_after'].items()),'provider '+file)
need(H(O/'compile.log')==r['log_sha256']=='b8c1fc4e55f198f96112d77d4a20e012afa39a20464c54c29234d61015e74ee1','log');l=(O/'compile.log').read_text();need(l.count('depends on axioms:')==2 and '[propext, Quot.sound]' in l and '[propext, Classical.choice, Quot.sound]' in l and not any(x in l for x in ('sorryAx','warning:','error:')),'axioms');need(H(Path('/tmp/current2011-unscaled66-vs106-fresh-priority-check01/Unscaled66Vs106Fresh.olean'))==r['object_sha256']=='4eafb3349a554d7ac322280a50e8d163020be24147d83af603c0dfd470547a42','object')
need(H(PRE/'check.py')=='091a2e546f3bd2ad63a09bf7704fa1dca90e66284b023ece4c8e432b2de0203a','prior checker pin');p=subprocess.run([sys.executable,'-I','-S','-B',str(PRE/'check.py')],capture_output=True);need(p.returncode==0 and p.stdout==(PRE/'result.json').read_bytes(),'prior source/provider audits rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','direct_and_nested_provider_slots':337,'prior_fresh_model_audit_exit':0,'success_session':95783,'scope':'Ring identity and same-valuation model iff, recorded current-base provider; no Lean replay, fresh second base rebuild or formal degree/PDF proof.'},sort_keys=True,indent=2))
