#!/usr/bin/env python3
"""Audit the recorded all-model same-valuation 71/60 to 67/94 join."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary70-84-model-join'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'OrdinarySphere7084Model.lean':'5236b781c9b4c6f74d33529c0311edd18897cb7201fc7176ee13db0fe7e179c5','check01.py':'7e9aa0855d91e21d1dae13830a3bedc9d1eb16321dd30bc303b0e0488ed553ac','attempt01/result.json':'a0b135c3c234976b72cfccbf4f468e7c9b67664623f1f5ce15cc9e3e4332f167','attempt01/compile.log':'e3131e3a615e5350f36123f950ef39f04ab079b1fe966cb791c9e20d2fb6adda','attempt01/outer-observation.json':'1b25dbaf54c66ed0406bc84b0ca808f815801e4eafceb428257562a5974aa472'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
import re
s=re.sub(r'\s+','',(P/'OrdinarySphere7084Model.lean').read_text());need('variable{V:Type}[ORingStructureV][V↓[ℒₒᵣ]⊧*𝗜𝚺₁]' in s,'model context')
need('theoremsameZero94(v:Fin14→V):InternalZero(positiveShift(OrdinarySphere7084Literal.expressionAtCurrentWindowCarry2011.ports))v↔InternalZeroCarrier94Syntax.naturalExpression94v:=' in s,'same valuation statement')
need('OrdinarySphere7084Generic.zero_iff94FreshCarrierSpheres.modelFacts__FreshModel106.beta_pos(FreshModel106.shifted_posv)' in s,'generic instance')
r=json.loads((P/'attempt01/result.json').read_text());o=json.loads((P/'attempt01/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==528 and o['session_id']==56964 and o['observed_outer_exit']==0,'receipt/exit')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
for name,h in {'OrdinarySphere7084Generic.olean':'2e7f9a5e8041cee171653527db578adf1fcb426a3890b0415d13439f3436a0cd','OrdinarySphere7084Literal.olean':'69aea03a50aeb2f6d10a445c5664438771fe668174e45ac456ded02716b50720'}.items():
 need(any(k.endswith('/'+name) and v and v['sha256']==h for k,v in r['guards_after'].items()),'predecessor '+name)
obj=Path('/tmp/current2011-ordinary70-84-model-join-check01/OrdinarySphere7084Model.olean');need(H(obj)==r['object_sha256']=='13d3363ef59913f3a5d92dc9a32ba0604e1b6f7bc7ec01edca81b0656e2c4d9e','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and not any(x in log for x in ('warning:','error:','sorryAx')),'log');m=re.fullmatch(r"\s*'DiophantineConsistency\.OrdinarySphere7084Model\.sameZero94' depends on axioms: \[([^]]*)\]\s*",log,re.S);need(m and {x.strip() for x in m.group(1).split(',')}=={'propext','Classical.choice','Quot.sound'},'axioms')
for folder in ('current2011-ordinary70-84-generic-independent','current2011-ordinary70-84-literal-independent','current2011-ordinary70-84-graph-independent'):
 q=D/'reviews'/folder;run=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True);need(run.returncode==0 and run.stdout==(q/'result.json').read_bytes(),'prior review '+folder)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_MODEL_JOIN_AUDIT','guard_slots':528,'outer_session':56964,'predecessor_reviews':3,'scope':'Same positively shifted valuation in every stated IΣ₁ model; no iPRA theorem, Lean replay or new transitive-provider audit.'},indent=2,sort_keys=True))
