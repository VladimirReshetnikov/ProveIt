#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-unscaled66-translated';O=P/'observations/attempt02';F=P/'observations/attempt01';PRE=D/'reviews/current2011-unscaled66-model-independent'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for n,h in {'Current2011Unscaled66Translated.lean':'38907c1d9d2c98bc1f30339d4244e7feecde7b210b9605a58206c8fb2d26ff04','check02.py':'1f9e0e809a644fba23990838c45e8c94f531fa9299f2a842b9e350eb05f83890','observations/attempt02/result.json':'916f5900771636d8b51b197ecc7c4295b0ba4774b129901c2cbb3faafe0debff','observations/attempt02/outer-terminal.json':'f184529a0316317f867486fb9a6698e8a621551bdf9aa44c1b0c7a88cdfe339c','observations/attempt01/result.json':'5a47aa4d3eef1052ad97d13ceb52bf5edd2b958c8723cd4cae3fce67addaa6b4','observations/attempt01/outer-terminal.json':'4bfd9bb466244d0ea104c035fc3c54b2ce657985e974e0bc2ab073abc6950e72'}.items():need(H(P/n)==h,'pin '+n)
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());f=json.loads((F/'result.json').read_text());ft=json.loads((F/'outer-terminal.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==418,'success receipt');need(t['session_id']==58233 and t['terminal_exit_code']==0 and t['returned_session_id'] is None,'outer exit');need(f['status']=='FAILED' and f['exit']==1 and f['object_sha256'] is None and ft['session_id']==95428 and ft['terminal_exit_code']==1,'failure receipt');need(H(F/'compile.log')==f['log_sha256'] and 'Ambiguous term' in (F/'compile.log').read_text() and 'sorryAx' in (F/'compile.log').read_text(),'failed log')
for n,m in r['guards_after'].items():
 p=Path(n.split(':',1)[-1]);
 if m is None:need(not os.path.lexists(p),'unexpected '+n)
 else:
  need(p.is_file() and str(p.resolve())==m.get('realpath',m.get('resolved')) and H(p)==m['sha256'],'guard '+n)
  if 'link' in m:need((os.readlink(p) if p.is_symlink() else None)==m['link'],'link '+n)
for file,h in [('Current2011Unscaled66.olean','a83b4237c02aa67f24f832f86e58f9afc04510b9ad6768f70f59524c50ad36a3'),('ModelCarrierCurrent.olean','79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122'),('ModelCarrierSyntax.olean','9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900')]:need(any(k.endswith('/'+file) and v and v['sha256']==h for k,v in r['guards_after'].items()),'provider '+file)
need(H(O/'compile.log')==r['log_sha256']=='dcdbb5141d3806af99baac0d127234209bb8a9572ed6121e77cbf70e3c9b58c6','log');l=(O/'compile.log').read_text();need(l.count('depends on axioms:')==1 and all(x in l for x in ('propext','Classical.choice','Quot.sound')) and not any(x in l for x in ('sorryAx','warning:','error:')),'axioms');need(H(Path('/tmp/current2011-unscaled66-translated-priority-check02/Current2011Unscaled66Translated.olean'))==r['object_sha256']=='32e0c92e8a6260195de73eb667f6366e3b63b3ab90fcfe6c70eb345811db6171','object')
need(H(PRE/'check.py')=='ce4f0c5a09eebcf9cf8cb51e89579aefad38d203dcdb9eea8ab0bceaaf71dcd7','prior checker pin');p=subprocess.run([sys.executable,'-I','-S','-B',str(PRE/'check.py')],capture_output=True);need(p.returncode==0 and p.stdout==(PRE/'result.json').read_bytes(),'prior model audit rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','direct_and_producer_slots':418,'prior_model_audit_exit':0,'failed_session':95428,'success_session':58233,'scope':'Mapped Godel-Gentzen Foundation consistency for fixed 66 syntax, recorded historical provider; no Lean replay or formal degree/PDF proof.'},sort_keys=True,indent=2))
