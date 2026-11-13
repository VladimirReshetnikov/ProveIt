#!/usr/bin/env python3
"""Independent literal-row, ring-evaluator and recorded-provider audit."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary70-84-literal';G=D/'research/current2011-ordinary70-84-generic';GRAPH=D/'research/current2011-ordinary70-84-candidate/polynomial.json'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={P/'OrdinarySphere7084Literal.lean':'e498fa16e97284c4d048460769d758d4f5b354e2cd9faa616c1857f84897e8ec',P/'audit_rows.py':'df1f45cf58fb15d5153dbcb7eaedfbda150c661dacc64ffd106306eddd37d152',P/'row-audit.txt':'d4fdd6676226fa931ebc4c00c0c0fdeb743e807e1b015d4da32ce5eebd6d637a',P/'check01.py':'48241135b66cb72422ad5a462efbe4cab6007ba57e8388848dacfc5115639a40',P/'attempt01/result.json':'ccbd3ba0713022aaf04e1cbb26b3329742d699faa9fa7e9b303cb01acf62b44d',P/'attempt01/outer-observation.json':'99425c1647dd635c26e3ffa5b77745af4247544f8b3feb94c51796562453a180',GRAPH:'bb7df3586252e9c85be225a0373a8586c2c2f841683cc5f4b6f57f02175447e5',G/'OrdinarySphere7084Generic.lean':'9ad402c654e1d5589d36bf1f6fd23142d20d8a14d8f4d3b553ec9607e4eb3e68'}
for p,h in pins.items():need(H(p)==h,'pin '+str(p))
graph=json.loads(GRAPH.read_bytes());s=(P/'OrdinarySphere7084Literal.lean').read_text();gen=(G/'OrdinarySphere7084Generic.lean').read_text()
body=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Ring',1)[0]; lines=[x.strip() for x in body.splitlines() if x.strip()];need(lines[-1]=='polynomial','return')
expect=[]
expect += [f'let {name} : Expr (Fin 14) := .var {i}' for i,name in enumerate(graph['witnesses'])]
expect += [f'let {name} : Expr (Fin 14) := .constant (p {i})' for i,name in enumerate(graph['fixed_numerals'])]
expect += [f'let {name} := {a} {op} {b}' for name,op,a,b in graph['source']];expect+=['polynomial']
need(lines==expect and len(graph['source'])==70,'complete rows and aliases')
def definition(src,name):
 match=re.search(r'^def '+name+r'\s+(.*?)(?=\n(?:def |theorem |end Ring))',src,re.M|re.S)
 need(match is not None,'missing definition '+name)
 return re.sub(r'\s+','',match.group(1)).replace('Carrier65.Core','Core')
sphere=D/'research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean'
need(H(sphere)=='a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5','sphere source')
need(definition(s,'auxiliary')==definition(sphere.read_text(),'auxiliary') and definition(s,'value70')==definition(gen,'value70'),'generic auxiliary/value definitions differ')
compact=re.sub(r'\s+','',s);need('theoremeval_expression(p:Fin4→ℤ)(v:Fin14→R):(expressionAtp).evalRingv=value70(funj=>(pj:R))v:=' in compact,'ring evaluator statement')
r=json.loads((P/'attempt01/result.json').read_text());out=json.loads((P/'attempt01/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==251 and out['session_id']==28929 and out['observed_outer_exit']==0,'run receipt')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
need(any(k.endswith('/Carrier94Value.olean') and v and v['sha256']=='a9c320a8e69a693aa869dbb7b272fe642e1bf76420e2602e580abbdfff52e887' for k,v in r['guards_after'].items()),'value provider')
obj=Path('/tmp/current2011-ordinary70-84-literal-check01/OrdinarySphere7084Literal.olean');need(H(obj)==r['object_sha256']=='69aea03a50aeb2f6d10a445c5664438771fe668174e45ac456ded02716b50720','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and log.strip()=="'DiophantineConsistency.OrdinarySphere7084Literal.eval_expression' depends on axioms: [propext]",'log')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'audit_rows.py')],capture_output=True);need(q.returncode==0 and q.stdout==(P/'row-audit.txt').read_bytes(),'row checker rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_LITERAL_AUDIT','rows':70,'witness_aliases':14,'port_aliases':4,'guard_slots':251,'success_session':28929,'scope':'Exact Lean source/JSON rows and commutative-ring evaluator; no Lean replay, graph degree, model or iPRA theorem.'},indent=2,sort_keys=True))
