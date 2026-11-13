#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-spheres-fresh-translated';O=P/'attempt01';PRE=D/'reviews/current2011-spheres-fresh-base-independent'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for n,h in {'TranslatedSpheres.lean':'57f0275670e99cb0fb5171f37c7b98bd82fc75f93985db0b3b3a292366e11c5d','check01.py':'e0195badcf935a3741ecd605abedaef8e10b946934d73e35ef5f3e4400665e66','attempt01/result.json':'d3311197caca8f3168a6cb5388408e3d66504489d26d2ea2fb99b4cd807b1060','attempt01/outer-observation.json':'573357726ec2b4b5dffee9aefcb902b3c15aa3488b37b5a38ca7ba5074abf016'}.items():need(H(P/n)==h,'pin '+n)
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-observation.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==488,'success receipt');need(t['session_id']==19379 and t['observed_outer_exit']==0,'outer exit')
for n,m in r['guards_after'].items():
 p=Path(m['path'] if m is not None and 'path' in m else n.rsplit(':',1)[-1]);
 if m is None:need(not os.path.lexists(p),'unexpected '+n)
 else:need(p.is_file() and str(p.resolve())==m['realpath'] and H(p)==m['sha256'],'guard '+n)
for file,h in [('FreshCarrierSpheres.olean','37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020'),('FreshModel106.olean','d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942')]:need(any(k.endswith('/'+file) and v and v['sha256']==h for k,v in r['guards_after'].items()),'provider '+file)
need(H(O/'compile.log')==r['log_sha256']=='0de90eeb2005b7726b904048f2c3c0cdf9733be8bc4809f5e27f6ab33de33108','log');l=(O/'compile.log').read_text();reports=re.findall(r"'DiophantineConsistency\.FreshTranslatedSpheres\.(\w+)' depends on axioms: \[([^]]*)\]",l,re.S);need({n:{x.strip() for x in v.split(',')} for n,v in reports}=={n:{'propext','Classical.choice','Quot.sound'} for n in ('standard_translated_equivalence71','standard_translated_equivalence72')} and not any(x in l for x in ('sorryAx','warning:','error:')),'exact axiom reports');need(H(Path('/tmp/current2011-spheres-fresh-translated-priority-check01/TranslatedSpheres.olean'))==r['object_sha256']=='890d9de3298c927712251cfc2d0361a7319813fcf8e7964f108ab5054d26af79','object')
need(H(PRE/'check.py')=='1625cbb62969f5eae459978368ea137577b4e6d93fdd2188cf86d090190ed9f2','prior checker pin');p=subprocess.run([sys.executable,'-I','-S','-B',str(PRE/'check.py')],capture_output=True);need(p.returncode==0 and p.stdout==(PRE/'result.json').read_bytes(),'prior sphere model/DAG/degree audit')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','direct_and_nested_provider_slots':488,'prior_sphere_audit_exit':0,'success_session':19379,'scope':'Two mapped Godel-Gentzen Foundation consistency derivations for fixed sphere syntax, captured current-base provider; no Lean replay or new transitive ancestry.'},sort_keys=True,indent=2))
