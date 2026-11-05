#!/usr/bin/env python3
"""Independent literal graph and recorded Lean artifact audit; no Lean replay."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-unscaled66-model';G=D/'research/current2011-unscaled66/polynomial.json';O=P/'observations/attempt02';F=P/'observations/attempt01'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={'Current2011Unscaled66.lean':'151dae72af79bf7d4714329ca3bda7a4b3308bb3e3a40d7ae3c14ae16bacd9a3','audit_rows.py':'937305e1ca597ab8928cdd0d63e40f679bb111e48af1bb041ad566ae2f9fcb02','build_lean.py':'5a3747a9e97666633a057551a3f85ce29a5813d8e40b9deae03d7a69a3f2440d','check02.py':'76814377d072ee000fef99051a6491096309a685169958ce2851d022d1b1713f','observations/attempt02/result.json':'ba49c31dc6daffe99c8ae95fef7e414f63125e435f96bbc574b20218e8e2127a','observations/attempt02/outer-terminal.json':'2ed695a02a330c480633ef687e003b47684fbb783890def4db21d7cd92d3077a','observations/attempt01/result.json':'b2f8d81bc3b466ed0e0619862cb69890a53cd4c1f694b5e77a76cbb345b5ed20','observations/attempt01/outer-terminal.json':'64a89b568aacedfa6627641c1da711abae618e3740307f7f0b0698540076a17d'}
for n,h in pins.items():need(H(P/n)==h,'pin '+n)
need(H(G)=='bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75','graph pin');g=json.loads(G.read_text());text=(P/'Current2011Unscaled66.lean').read_text();body=text.split('\ndef expressionAt ',1)[1].split('\nsection Eval',1)[0]
for i,n in enumerate(g['witnesses']):need(f'  let {n} : Expr (Fin 14) := .var {i}\n' in body,'witness '+n)
for i,n in enumerate(g['fixed_numerals']):need(f'  let {n} : Expr (Fin 14) := .constant (p {i})\n' in body,'port '+n)
rows=[]
for line in body.splitlines():
 m=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
 if m:
  n,a,op,b=m.groups();rows.append([n,op,int(a) if a.isdecimal() else a,int(b) if b.isdecimal() else b])
need(rows==g['source'] and len(rows)==66 and body.rstrip().endswith('\n  polynomial'),'literal row graph')
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());f=json.loads((F/'result.json').read_text());ft=json.loads((F/'outer-terminal.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==380,'success receipt');need(t['session_id']==70423 and t['terminal_exit_code']==0 and t['returned_session_id'] is None,'outer exit');need(f['status']=='FAILED' and f['exit']==1 and f['object_sha256'] is None and ft['session_id']==18354 and ft['terminal_exit_code']==1,'failed receipt');need(H(F/'compile.log')==f['log_sha256'] and 'maximum recursion depth' in (F/'compile.log').read_text() and 'sorryAx' in (F/'compile.log').read_text(),'failed log')
for n,m in r['guards_after'].items():
 p=Path(n.split(':',1)[-1]);
 if m is None:need(not os.path.lexists(p),'unexpected '+n)
 else:
  need(p.is_file() and str(p.resolve())==m.get('realpath',m.get('resolved')) and H(p)==m['sha256'],'guard '+n)
  if 'link' in m:need((os.readlink(p) if p.is_symlink() else None)==m['link'],'link '+n)
for file,h in [('ModelCarrierCurrent.olean','79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122'),('ModelCarrierSyntax.olean','9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900')]:need(any(k.endswith('/'+file) and v and v['sha256']==h for k,v in r['guards_after'].items()),'historical provider '+file)
need(H(O/'compile.log')==r['log_sha256']=='659a55ed5bfc1c07bd9212b68321d6bc577fa6760a3031b9b85b0cdddfbaa4c4','log');l=(O/'compile.log').read_text();need(l.count('depends on axioms:')==5 and not any(x in l for x in ('sorryAx','warning:','error:')),'axioms and errors');reports=re.findall(r"'DiophantineConsistency\.Current2011Unscaled66\.(\w+)' depends on axioms: \[([^]]*)\]",l,re.S); actual={name:{x.strip() for x in report.split(',')} for name,report in reports};need(actual=={'evalRing_expressionAt':{'propext'},'scaled_identity':{'propext','Quot.sound'},'sameZero138':{'propext','Classical.choice','Quot.sound'},'bridge138':{'propext','Classical.choice','Quot.sound'},'standard_equivalence138':{'propext','Classical.choice','Quot.sound'}},'exact axiom reports');need(H(Path('/tmp/current2011-unscaled66-model-priority-check02/Current2011Unscaled66.olean'))==r['object_sha256']=='a83b4237c02aa67f24f832f86e58f9afc04510b9ad6768f70f59524c50ad36a3','object')
a=subprocess.run([sys.executable,'-I','-S','-B',str(P/'audit_rows.py')],capture_output=True,text=True);need(a.returncode==0 and a.stdout==(P/'row-audit.txt').read_text(),'author row checker')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','literal_rows':66,'direct_and_producer_slots':380,'failed_outer_session':18354,'success_outer_session':70423,'author_row_rerun_exit':0,'scope':'Recorded historical provider, literal row and theorem source audit; no Lean replay, fresh-base rebuild, formal degree or PDF binding.'},indent=2,sort_keys=True))
