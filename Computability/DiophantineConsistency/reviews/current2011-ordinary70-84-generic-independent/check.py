#!/usr/bin/env python3
"""Read-only audit of 70/84 generic ordered-ring zero equivalence."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary70-84-generic'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'OrdinarySphere7084Generic.lean':'9ad402c654e1d5589d36bf1f6fd23142d20d8a14d8f4d3b553ec9607e4eb3e68','check01.py':'e673c13234095dd1033b0ce9d2c24a1cc2b9886b8b0e501b8e3ce1512570dbea','attempt01/result.json':'fcbb8f05f31075b399b090d133e44813786d87e3c461bc31e139a3caacc2c0e3','attempt01/compile.log':'ac9701dd7c90cc2d9f5006066928a13eabb9f222220131922dacbc0c3c7c2a93','attempt01/outer-observation.json':'d6d8a347cf5217ec8d3201db33c0376eff71165b4585599afdb3ead5a5921b87'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
s=re.sub(r'\s+','',(P/'OrdinarySphere7084Generic.lean').read_text())
need('variable{R:Type*}[CommRingR][LinearOrderR][IsStrictOrderedRingR]' in s and 'variable(F:FactsR)(p:Fin4→R)(v:Fin14→R)' in s and 'variable(hb:0<p0)(hv:∀j,0<vj)' in s,'ordered ring/Facts/positivity')
need('theoremzero_iff94:value70pv=0↔Carrier94Value.value94pv=0:=' in s,'same-coordinate zero iff')
need('(auxiliaryd)^2+(d.P*d.Q*d.W-1)^2+strong^2-1' in s and 'letstrong:=I^2-d.delta*(d.f^2-1)' in s,'value formula')
r=json.loads((P/'attempt01/result.json').read_text());o=json.loads((P/'attempt01/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==340 and o['session_id']==75341 and o['observed_outer_exit']==0,'receipt/exit')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
need(any(k.endswith('/OrdinarySphere7160Generic.olean') and v and v['sha256']=='73a022ff49f38e554c0ece51601aba36cd11931fceb2e020493fb5dd09127c2b' for k,v in r['guards_after'].items()),'prior generic object')
obj=Path('/tmp/current2011-ordinary70-84-generic-check01/OrdinarySphere7084Generic.olean');need(H(obj)==r['object_sha256']=='2e7f9a5e8041cee171653527db578adf1fcb426a3890b0415d13439f3436a0cd','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and not any(x in log for x in ('error:','warning:','sorryAx')),'log');m=re.fullmatch(r"\s*'DiophantineConsistency\.OrdinarySphere7084Generic\.zero_iff94' depends on axioms: \[([^]]*)\]\s*",log,re.S);need(m and {x.strip() for x in m.group(1).split(',')}=={'propext','Classical.choice','Quot.sound'},'axioms')
prior=D/'reviews/current2011-ordinary71-60-generic-independent';q=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],capture_output=True);need(q.returncode==0 and q.stdout==(prior/'result.json').read_bytes(),'prior generic review')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_GENERIC_AUDIT','outer_session':75341,'guard_slots':340,'prior_generic_review_exit':0,'scope':'Same-coordinate zero iff over ordered rings under stated Facts and positivity; no Lean replay, model or iPRA endpoint.'},indent=2,sort_keys=True))
