#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary94-fresh-translated';O=P/'attempt01';PRE=D/'reviews/current2011-ordinary94-fresh-endpoint-independent'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for n,h in {'Translated94.lean':'2c86bbcf3e0bd807da52c634572b22b9f44471cd8af68243dd4cc5c2bb64ca66','check01.py':'2b32183af3d64c170878cc00ddcac39e25fa4d4593117647024d31d0d1879930','attempt01/result.json':'675f4e568e1c6bc82365cef14414928d113a28164cd7b782b1cb152b95fbdd62','attempt01/outer-observation.json':'7add47ea76ee72b1255fd4b6aa235fb1c952b983c239cd907c918807ef26087d'}.items():need(H(P/n)==h,'pin '+n)
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-observation.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==326,'success receipt');need(t['session_id']==61207 and t['observed_outer_exit']==0,'outer exit')
for n,m in r['guards_after'].items():
 p=Path(m['path'] if m is not None and 'path' in m else n.rsplit(':',1)[-1]);
 if m is None:need(not os.path.lexists(p),'unexpected '+n)
 else:need(p.is_file() and str(p.resolve())==m['realpath'] and H(p)==m['sha256'],'guard '+n)
need(any(k.endswith('/FreshCarrier94.olean') and v and v['sha256']=='dfe72edd726a5a140d509f606f866ce6dd8e8d1f008bc96a957c1c1509ce642c' for k,v in r['guards_after'].items()),'prior endpoint object')
need(H(O/'compile.log')==r['log_sha256']=='384e891ab4b907e3f322eb1e8b49da2a5314bc710926d76948ee9445cd4214fe','log');l=(O/'compile.log').read_text();need(re.search(r"'DiophantineConsistency\.FreshTranslated94\.standard_translated_equivalence94' depends on axioms: \[propext,\s*Classical\.choice,\s*Quot\.sound\]",l) is not None and l.count('depends on axioms:')==1 and not any(x in l for x in ('sorryAx','warning:','error:')),'axiom report');need(H(Path('/tmp/current2011-ordinary94-fresh-translated-check01/Translated94.olean'))==r['object_sha256']=='9864c3dc909141f45cb44717f7fc8d0bc571847c9d703942b4368e3edd1eba0d','object')
need(H(PRE/'check.py')=='18301fb4bc559158a08f48b8eb2c41586749823ca7eab081e7f870e0441f4afb','endpoint audit pin');p=subprocess.run([sys.executable,'-I','-S','-B',str(PRE/'check.py')],capture_output=True);need(p.returncode==0 and p.stdout==(PRE/'result.json').read_bytes(),'prior endpoint audit rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','direct_and_nested_provider_slots':326,'prior_endpoint_audit_exit':0,'success_session':61207,'scope':'Existential fixed-port 94 no-zero derivation with mapped Godel-Gentzen consistency, recorded fresh-base providers; no Lean replay or new transitive ancestry.'},sort_keys=True,indent=2))
