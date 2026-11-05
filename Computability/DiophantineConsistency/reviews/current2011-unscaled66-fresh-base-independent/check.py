#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-unscaled66-fresh-base';O=P/'attempt01';OUT=Path('/tmp/current2011-unscaled66-fresh-base-20261105');F=D/'research/normalized106-current14-sixteen-source-preflight/result.json';G=D/'research/current2011-unscaled66/polynomial.json';OLD=D/'research/current2011-unscaled66-model/Current2011Unscaled66.lean'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
for n,h in {'Current2011Unscaled66Fresh.lean':'9b323e56feabc402d02c49af27192013d0b9faf74631ead83f3cf7a0b51b0f7a','check-client.py':'4d924248b755b16e9564fa8f04e7a6b6c20d6c6791c75d97700f3f5fbea4ec9f','audit-rows.py':'ffe3c0228ecfaeacf677ee0eaa456b94475662e95a431317547a82a3719d2b69','attempt01/state.json':'900a60a742590560b4d95cbba945d22028e508c02964abde9f55a0b1a68b58a2','attempt01/outer-terminal.json':'b408670c584c7031db7714a2db794af933b0c1d40da374f42699e32ee8aec9c9'}.items():need(H(P/n)==h,'pin '+n)
need(H(G)=='bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75' and H(OLD)=='151dae72af79bf7d4714329ca3bda7a4b3308bb3e3a40d7ae3c14ae16bacd9a3','graph and historical source pins');g=json.loads(G.read_text());source=(P/'Current2011Unscaled66Fresh.lean').read_text();body=source.split('\ndef expressionAt ',1)[1].split('\nsection Eval',1)[0];prior=OLD.read_text().split('\ndef expressionAt ',1)[1].split('\nsection Eval',1)[0];need(body==prior,'historical literal graph parity')
for i,n in enumerate(g['witnesses']):need(f'  let {n} : Expr (Fin 14) := .var {i}\n' in body,'witness alias '+n)
for i,n in enumerate(g['fixed_numerals']):need(f'  let {n} : Expr (Fin 14) := .constant (p {i})\n' in body,'port alias '+n)
rows=[]
for line in body.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
 if m:
  n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
need(rows==g['source'] and len(rows)==66 and body.rstrip().endswith('\n  polynomial'),'complete graph rows')
r=json.loads((O/'state.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());need(r['status']=='PASS' and t['observed_session']==37489 and t['exit_code']==0 and t['state_sha256']==H(O/'state.json'),'actual terminal');need(H(OUT/'state.json')==H(O/'state.json') and H(OUT/'Current2011Unscaled66Fresh.lean')==r['source_sha256']==H(P/'Current2011Unscaled66Fresh.lean'),'source and state');need(H(OUT/'Current2011Unscaled66Fresh.olean')==r['object_sha256']=='43de05d18c2854a224ebcd01c560cb5327752118ee08164277f38e7611a01b00','object');need(len(r['direct_guard'])==80,'direct slot count')
for n,x in r['direct_guard'].items():
 p=Path(n)
 if x is None:need(not os.path.lexists(p),'unexpected '+n)
 else:need(p.is_file() and str(p.resolve())==x['realpath'] and H(p)==x['sha256'],'guard '+n)
need(set(r['dependencies'])=={'Init','FreshModel106'} and r['dependencies']['FreshModel106']['sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','prior provider')
for n,x in r['dependencies'].items():need(r['direct_guard'][x['path']]['sha256']==x['sha256'],'direct link '+n)
for i,n in enumerate(('deps','compile')):need(r['runs'][i]['exit']==0 and H(O/(n+'.txt'))==r['runs'][i]['log_sha256'] and (O/(n+'.txt')).read_bytes()==(OUT/(n+'.txt')).read_bytes(),'log '+n)
l=(O/'compile.txt').read_text();reports=re.findall(r"'DiophantineConsistency\.Current2011Unscaled66Fresh\.(\w+)' depends on axioms: \[([^]]*)\]",l,re.S);actual={n:{x.strip() for x in s.split(',')} for n,s in reports};need(actual=={'evalRing_expressionAt':{'propext'},'scaled_identity':{'propext','Quot.sound'},'sameZero138':{'propext','Classical.choice','Quot.sound'},'bridge138':{'propext','Classical.choice','Quot.sound'},'standard_equivalence138':{'propext','Classical.choice','Quot.sound'}} and not any(x in l for x in ('sorryAx','warning:','error:')),'axiom reports')
need(H(F)==r['preflight_before_sha256']==r['preflight_after_sha256'] and (OUT/'preflight-before.json').read_bytes()==F.read_bytes() and (OUT/'preflight-after.json').read_bytes()==F.read_bytes(),'preflight')
for rel,h in [('reviews/normalized106-fresh-base-model-independent/check.py','2f1e8f23caabe818d51ec8f3c56f6752794c9dee755624794cc8fb154a77361f'),('reviews/current2011-unscaled66-model-independent/check.py','ce4f0c5a09eebcf9cf8cb51e89579aefad38d203dcdb9eea8ab0bceaaf71dcd7')]:
 p=D/rel;need(H(p)==h,'prior checker pin');run=subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True);need(run.returncode==0 and run.stdout==(p.parent/'result.json').read_bytes(),'prior audit rerun '+rel)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','literal_rows':66,'direct_slots':80,'prior_independent_audits':2,'outer_session':37489,'outer_exit':0,'scope':'Fresh-base fixed 66 syntax and direct provider, no Lean replay or fresh second base rebuild; degree/PDF and transitive ancestry external.'},indent=2,sort_keys=True))
