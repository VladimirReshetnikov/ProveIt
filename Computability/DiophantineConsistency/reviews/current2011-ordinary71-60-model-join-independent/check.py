#!/usr/bin/env python3
"""Audit the recorded all-model same-valuation 71/60 to 67/94 join."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary71-60-model-join'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'OrdinarySphere7160Model.lean':'98eda3763aa05598820c567e52a4c89d51a3aaaeed2912a925a9c1560d20ef98','check01.py':'b725f413ae5087ed9d42fc6b4ebe9bc45e411c2078c5cc9c2bf9eee4aaf63efb','attempt01/result.json':'9d4251c3daf6f7ccde41232a354a5df7716e017a0d129bd8d9a8bab3534f694c','attempt01/compile.log':'170b80a199ae513e17faf0f40136ec13071d1951bbb7d0ec4fa06cf1724b90c1','attempt01/outer-observation.json':'41fc1dd4fd72461f3082288478d72003330c7d22e53c8002f328caa768afd064'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
import re
s=re.sub(r'\s+','',(P/'OrdinarySphere7160Model.lean').read_text());need('variable{V:Type}[ORingStructureV][V↓[ℒₒᵣ]⊧*𝗜𝚺₁]' in s,'model context')
need('theoremsameZero94(v:Fin14→V):InternalZero(positiveShift(OrdinarySphere7160Literal.expressionAtCurrentWindowCarry2011.ports))v↔InternalZeroCarrier94Syntax.naturalExpression94v:=' in s,'same valuation statement')
need('OrdinarySphere7160Generic.zero_iff94FreshCarrierSpheres.modelFacts__FreshModel106.beta_pos(FreshModel106.shifted_posv)' in s,'generic instance')
r=json.loads((P/'attempt01/result.json').read_text());o=json.loads((P/'attempt01/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==393 and o['session_id']==63341 and o['observed_outer_exit']==0,'receipt/exit')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
for name,h in {'OrdinarySphere7160Generic.olean':'73a022ff49f38e554c0ece51601aba36cd11931fceb2e020493fb5dd09127c2b','OrdinarySphere7160Literal.olean':'b4386569a433cc7a0e2033368a9167081bb5e6e50ee8fd867df1938c01ed4e60'}.items():
 need(any(k.endswith('/'+name) and v and v['sha256']==h for k,v in r['guards_after'].items()),'predecessor '+name)
obj=Path('/tmp/current2011-ordinary71-60-model-join-check01/OrdinarySphere7160Model.olean');need(H(obj)==r['object_sha256']=='dcf62bccbeb5ef8303104411996eba3d3798784cdc6fa9b40040e4a9d6d135e2','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and not any(x in log for x in ('warning:','error:','sorryAx')),'log');m=re.fullmatch(r"\s*'DiophantineConsistency\.OrdinarySphere7160Model\.sameZero94' depends on axioms: \[([^]]*)\]\s*",log,re.S);need(m and {x.strip() for x in m.group(1).split(',')}=={'propext','Classical.choice','Quot.sound'},'axioms')
for folder in ('current2011-ordinary71-60-generic-independent','current2011-ordinary71-60-literal-independent','current2011-ordinary71-60-graph-independent'):
 q=D/'reviews'/folder;run=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True);need(run.returncode==0 and run.stdout==(q/'result.json').read_bytes(),'prior review '+folder)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_MODEL_JOIN_AUDIT','guard_slots':393,'outer_session':63341,'predecessor_reviews':3,'scope':'Same positively shifted valuation in every stated IΣ₁ model; no iPRA theorem, Lean replay or new transitive-provider audit.'},indent=2,sort_keys=True))
