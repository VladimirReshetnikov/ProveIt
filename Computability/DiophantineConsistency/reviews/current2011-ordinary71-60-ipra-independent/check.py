#!/usr/bin/env python3
"""Read-only audit of recorded 71/60 standard-iPRA and GG endpoint."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary71-60-ipra'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'OrdinarySphere7160IPRA.lean':'a169a2e71e6699ef84f6196f43ef3bb54245208213cc32f776adadfa622f4421','check01.py':'1f2d2b5c598357b98478702afcf9ff70a2783d3dd9c64bf1d437bd48a453d5c5','attempt01/result.json':'02a0f2ee160b713451846433b47a097df22c4590c24711fb567fe2f1abac45b8','attempt01/compile.log':'dcd89bfab11a0a7040239ef3c78921d7c00f42403baed4251b9f76181f37a027','attempt01/outer-observation.json':'7c9e2f0d4ad8fa861a8aec2640bca30ad86014eefcd96a6fc2193fa286682b92'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
s=re.sub(r'\s+','',(P/'OrdinarySphere7160IPRA.lean').read_text())
prefix='IPRAStandardTheory.standardTheory⊢IPRAExpressionNative.nativeNoZero(positiveShift(OrdinarySphere7160Literal.expressionAtCurrentWindowCarry2011.ports))🡘'
need('theoremstandard_equivalence71:'+prefix+'∼mappedNativeRefutationembedding:=' in s,'native refutation theorem')
need('theoremstandard_translated_equivalence71:'+prefix+'(Semiformula.lMapembeddingsourceSentence)ᴺ:=' in s,'GG theorem')
need('not_congr(OrdinarySphere7160Model.sameZero94v)' in s and 'eqv.trans(FreshCarrier94.bridge94V)' in s,'bridge path')
r=json.loads((P/'attempt01/result.json').read_text());o=json.loads((P/'attempt01/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==525 and o['session_id']==77676 and o['observed_outer_exit']==0,'receipt/exit')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
for name,h in {'OrdinarySphere7160Model.olean':'dcf62bccbeb5ef8303104411996eba3d3798784cdc6fa9b40040e4a9d6d135e2','FreshCarrier94.olean':'dfe72edd726a5a140d509f606f866ce6dd8e8d1f008bc96a957c1c1509ce642c'}.items():
 need(any(k.endswith('/'+name) and v and v['sha256']==h for k,v in r['guards_after'].items()),'provider '+name)
obj=Path('/tmp/current2011-ordinary71-60-ipra-check01/OrdinarySphere7160IPRA.olean');need(H(obj)==r['object_sha256']=='652809cc682ad29cc7ed71fcdd008514c7b6d9438a59ff221d80a9e61ae71256','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and not any(x in log for x in ('warning:','error:','sorryAx')),'log')
reports=re.findall(r"'DiophantineConsistency\.OrdinarySphere7160IPRA\.(\w+)' depends on axioms: \[([^]]*)\]",log,re.S);need({n:{x.strip() for x in a.split(',')} for n,a in reports}=={n:{'propext','Classical.choice','Quot.sound'} for n in ('bridge71','standard_equivalence71','standard_translated_equivalence71')},'axioms')
for folder in ('current2011-ordinary71-60-model-join-independent','current2011-ordinary94-fresh-endpoint-independent'):
 q=D/'reviews'/folder;run=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True);need(run.returncode==0 and run.stdout==(q/'result.json').read_bytes(),'prior review '+folder)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_IPRA_AUDIT','guard_slots':525,'outer_session':77676,'predecessor_reviews':2,'scope':'Standard iPRA proof existence for mapped refutation negation and mapped GG consistency, fixed literal 71/60 syntax; no Lean replay or new package-transitive ancestry.'},indent=2,sort_keys=True))
