#!/usr/bin/env python3
"""Independent recorded 69/84 all-model and iPRA endpoint audit."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary69-84-ipra'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'OrdinarySphere6984IPRA.lean':'5de0f23e5624ec63dc10708d68325adcd8e90455e26b687535ac70e376b6b5db','check01.py':'75123ea96b4699b6d0ef313433664476a554d05e491ebadfa5989c9a76b892f5','attempt01/result.json':'a2dd7786c10308bcbb79e1a545bfce481ae0d5ae92043fccf36bf9a26d79cf07','attempt01/compile.log':'f1b1c313b8a5bdb12db421a5953c8b46934c7d98d0732e7e188778c7b8f5455d','attempt01/outer-observation.json':'aa65e1a50779b6166ddefb57c3676f7c0b2704a75a48e2cf17f0af218838bbe5'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
s=re.sub(r'\s+','',(P/'OrdinarySphere6984IPRA.lean').read_text())
need('variable{V:Type}[ORingStructureV][V↓[ℒₒᵣ]⊧*𝗜𝚺₁]' in s,'model context')
need('theoremsameZero70(v:Fin14→V):InternalZero(positiveShift(OrdinarySphere6984Literal.expressionAtCurrentWindowCarry2011.ports))v↔InternalZero(positiveShift(OrdinarySphere7084Literal.expressionAtCurrentWindowCarry2011.ports))v:=' in s,'same valuation theorem')
prefix='IPRAStandardTheory.standardTheory⊢IPRAExpressionNative.nativeNoZero(positiveShift(OrdinarySphere6984Literal.expressionAtCurrentWindowCarry2011.ports))🡘'
need('theoremstandard_equivalence69:'+prefix+'∼mappedNativeRefutationembedding:=' in s,'mapped refutation')
need('theoremstandard_translated_equivalence69:'+prefix+'(Semiformula.lMapembeddingsourceSentence)ᴺ:=' in s,'mapped GG theorem')
need('OrdinarySphere6984Literal.value_eq70' in s and 'eqv.trans(OrdinarySphere7084IPRA.bridge70V)' in s,'bridge chain')
r=json.loads((P/'attempt01/result.json').read_text());o=json.loads((P/'attempt01/outer-observation.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==1035 and o['session_id']==34228 and o['observed_outer_exit']==0,'receipt/exit')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
for name,h in {'OrdinarySphere6984Literal.olean':'26e73fcd834d552ef3a24e2b45abadf48442ad964d534bba629f309e1b4794dd','OrdinarySphere7084IPRA.olean':'8a5118c46ede8edf5cab817207405e58c4a8632320d9ad8095ed48194a981eb9'}.items():
 need(any(k.endswith('/'+name) and v and v['sha256']==h for k,v in r['guards_after'].items()),'predecessor '+name)
obj=Path('/tmp/current2011-ordinary69-84-ipra-check01/OrdinarySphere6984IPRA.olean');need(H(obj)==r['object_sha256']=='b637b0c851a20ecb141a5a7a3267615e403294bc355ca21a6839c21a2fef68e3','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and not any(x in log for x in ('warning:','error:','sorryAx')),'log')
reports=re.findall(r"'DiophantineConsistency\.OrdinarySphere6984IPRA\.(\w+)' depends on axioms: \[([^]]*)\]",log,re.S);need({n:{x.strip() for x in a.split(',')} for n,a in reports}=={n:{'propext','Classical.choice','Quot.sound'} for n in ('sameZero70','bridge69','standard_equivalence69','standard_translated_equivalence69')},'axioms')
for folder in ('current2011-ordinary69-84-literal-independent','current2011-ordinary70-84-ipra-independent'):
 q=D/'reviews'/folder;z=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True);need(z.returncode==0 and z.stdout==(q/'result.json').read_bytes(),'prior review '+folder)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_IPRA_AUDIT','guard_slots':1035,'outer_session':34228,'predecessor_reviews':2,'scope':'All-model same-valuation 69/84↔70/84 and standard iPRA derivability with mapped refutation/GG consistency; no Lean replay or new package-transitive ancestry.'},indent=2,sort_keys=True))
