#!/usr/bin/env python3
"""Read-only audit of recorded 71/60 standard-iPRA and GG endpoint."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary70-84-ipra'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'OrdinarySphere7084IPRA.lean':'94af95ca1e15003016c71f8dc2e0f643c07d42aad6d4c4c958248974c1065e77','check01.py':'3e7bb228c9854ccac011edcb36a778fd30c85cc09f3249dcb219137c9822de9f','attempt01/result.json':'f73e1c926e9b5f178f486de44478973122d648fe743de321a649d58572fe9643','attempt01/compile.log':'b0e58376280cc1454998904e1ed4946afa13619bc11be2555d0b14d8ab2205da','attempt01/outer-observation.json':'9da8bd98574e3f38fa04789b1fede43f0c9bdf49747304441153df5f2358c521'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
s=re.sub(r'\s+','',(P/'OrdinarySphere7084IPRA.lean').read_text())
prefix='IPRAStandardTheory.standardTheory⊢IPRAExpressionNative.nativeNoZero(positiveShift(OrdinarySphere7084Literal.expressionAtCurrentWindowCarry2011.ports))🡘'
need('theoremstandard_equivalence70:'+prefix+'∼mappedNativeRefutationembedding:=' in s,'native refutation theorem')
need('theoremstandard_translated_equivalence70:'+prefix+'(Semiformula.lMapembeddingsourceSentence)ᴺ:=' in s,'GG theorem')
need('not_congr(OrdinarySphere7084Model.sameZero94v)' in s and 'eqv.trans(FreshCarrier94.bridge94V)' in s,'bridge path')
r=json.loads((P/'attempt01/result.json').read_text());o=json.loads((P/'attempt01/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==800 and o['session_id']==92210 and o['observed_outer_exit']==0,'receipt/exit')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
for name,h in {'OrdinarySphere7084Model.olean':'13d3363ef59913f3a5d92dc9a32ba0604e1b6f7bc7ec01edca81b0656e2c4d9e','FreshCarrier94.olean':'dfe72edd726a5a140d509f606f866ce6dd8e8d1f008bc96a957c1c1509ce642c'}.items():
 need(any(k.endswith('/'+name) and v and v['sha256']==h for k,v in r['guards_after'].items()),'provider '+name)
obj=Path('/tmp/current2011-ordinary70-84-ipra-check01/OrdinarySphere7084IPRA.olean');need(H(obj)==r['object_sha256']=='8a5118c46ede8edf5cab817207405e58c4a8632320d9ad8095ed48194a981eb9','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and not any(x in log for x in ('warning:','error:','sorryAx')),'log')
reports=re.findall(r"'DiophantineConsistency\.OrdinarySphere7084IPRA\.(\w+)' depends on axioms: \[([^]]*)\]",log,re.S);need({n:{x.strip() for x in a.split(',')} for n,a in reports}=={n:{'propext','Classical.choice','Quot.sound'} for n in ('bridge70','standard_equivalence70','standard_translated_equivalence70')},'axioms')
for folder in ('current2011-ordinary70-84-model-join-independent','current2011-ordinary94-fresh-endpoint-independent'):
 q=D/'reviews'/folder;run=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True);need(run.returncode==0 and run.stdout==(q/'result.json').read_bytes(),'prior review '+folder)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_IPRA_AUDIT','guard_slots':800,'outer_session':92210,'predecessor_reviews':2,'scope':'Standard iPRA proof existence for mapped refutation negation and mapped GG consistency, fixed literal 70/84 syntax; no Lean replay or new package-transitive ancestry.'},indent=2,sort_keys=True))
