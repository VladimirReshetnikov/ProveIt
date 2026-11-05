#!/usr/bin/env python3
"""Read-only review of the generic ordered-ring 71/60 lemma and captured run."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary71-60-generic'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,s):
 if not b:raise RuntimeError(s)
pins={'OrdinarySphere7160Generic.lean':'5808bcc7f662ff319ad6c64811260e216739888a7d4a8d89c68390d2561f9bae','check02.py':'4424a2f434a9dfb42837367854ffdcfc646b3fa72ab6102c777aa9afd0fd2271','attempt02/result.json':'f528cbbcd0f7bca3b4f54e4ca7dfaded857eb662a7a586791d6935cfc96bb003','attempt02/compile.log':'e1a7d9d4633a1f3b32f62977eeb0d2349375d500f9e9d17402acec697a49bf77','attempt02/outer-observation.json':'13ede8a4c9f8db03b7d586047001dfdbb2a7f61be6d6f3c1482f49f8434dea12'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
s=(P/'OrdinarySphere7160Generic.lean').read_text();compact=re.sub(r'\s+','',s)
need('variable{R:Type*}[CommRingR][LinearOrderR][IsStrictOrderedRingR]' in compact,'ordered ring context')
need('variable(F:FactsR)(p:Fin4→R)(v:Fin14→R)' in compact and 'variable(hb:0<p0)(hv:∀j,0<vj)' in compact,'facts and positivity')
need('theoremzero_iff94:value71pv=0↔Carrier94Value.value94pv=0:=' in compact,'theorem statement')
need('d.P^2+(auxiliaryd)^2+(d.Q*d.W-1)^2+strong^2-2' in compact and 'letstrong:=I^2-d.delta*(d.f^2-1)' in compact,'value statement')
need('havebad:∀aif:ZMod4,1+i^2-((a+2)^2-1)*(f^2-1)≠-1:=bydecide' in compact,'mod4 exclusion')
r=json.loads((P/'attempt02/result.json').read_text());outer=json.loads((P/'attempt02/outer-observation.json').read_text());bad=json.loads((P/'attempt01/result.json').read_text());badout=json.loads((P/'attempt01/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==298,'success receipt')
need(outer['session_id']==51812 and outer['observed_outer_exit']==0 and badout['session_id']==4171 and badout['observed_outer_exit']==1 and bad['exit']==1,'outer/child exits')
need('error:' in (P/'attempt01/compile.log').read_text(),'failed run not preserved')
for path,rec in r['guards_after'].items():
 p=Path(rec.get('path',path.rsplit(':',1)[-1]) if rec is not None else path.rsplit(':',1)[-1])
 if rec is None:need(not os.path.lexists(p),'unexpected '+path)
 else:need(p.is_file() and str(p.resolve())==rec['realpath'] and H(p)==rec['sha256'],'guard drift '+path)
expected={'FreshCarrierSpheres.olean':'37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020','Carrier94Value.olean':'a9c320a8e69a693aa869dbb7b272fe642e1bf76420e2602e580abbdfff52e887'}
for suffix,h in expected.items():need(any(k.endswith('/'+suffix) and v and v['sha256']==h for k,v in r['guards_after'].items()),'provider '+suffix)
obj=Path('/tmp/current2011-ordinary71-60-generic-check02/OrdinarySphere7160Generic.olean');need(H(obj)==r['object_sha256']=='73a022ff49f38e554c0ece51601aba36cd11931fceb2e020493fb5dd09127c2b','object')
text=(P/'attempt02/compile.log').read_text();need(H(P/'attempt02/compile.log')==r['log_sha256'] and not any(x in text for x in ('error:','warning:','sorryAx')),'log')
reports=re.findall(r"'DiophantineConsistency\.OrdinarySphere7160Generic\.(\w+)' depends on axioms: \[([^]]*)\]",text,re.S)
need({n:{x.strip() for x in a.split(',')} for n,a in reports}=={n:{'propext','Classical.choice','Quot.sound'} for n in ('ordinary_strong_ne_neg_one','zero_iff94')},'reports')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_GENERIC_AUDIT','success_session':51812,'failed_session':4171,'guard_slots':len(r['guards_after']),'scope':'Generic ordered-ring zero iff with stated Facts and positivity; recorded direct providers; no model/iPRA theorem or Lean replay.'},indent=2,sort_keys=True))
