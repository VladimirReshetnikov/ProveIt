#!/usr/bin/env python3
"""Independent literal-row, ring-evaluator and recorded-provider audit."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary71-60-literal';G=D/'research/current2011-ordinary71-60-generic';GRAPH=D/'research/current2011-ordinary71-60-candidate/polynomial.json'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={P/'OrdinarySphere7160Literal.lean':'554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a',P/'audit_rows.py':'6925db7e1b835238e0cfc51406c7077870f49cc3ceae8f59a1eea15d1f2a808d',P/'row-audit.txt':'8820a305cd28c47d9fe1eeab2f953677493dda3eb5113261cad8b208f6a2c55c',P/'check04.py':'cbe8017ae44b334407f2d5ca61c2c556a83fbc1a655b07343122d5dfaeefdd09',P/'attempt04/result.json':'055028339fc050116ec50c065bc47a4d993fb69c0c591dec2527fa45464d4e68',P/'attempt04/outer-observation.json':'68b8843f7e21311cbcd136449fbc296b2922c42c110fffd9aa25df4a0a1ec92d',GRAPH:'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',G/'OrdinarySphere7160Generic.lean':'5808bcc7f662ff319ad6c64811260e216739888a7d4a8d89c68390d2561f9bae'}
for p,h in pins.items():need(H(p)==h,'pin '+str(p))
graph=json.loads(GRAPH.read_bytes());s=(P/'OrdinarySphere7160Literal.lean').read_text();gen=(G/'OrdinarySphere7160Generic.lean').read_text()
body=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Ring',1)[0]; lines=[x.strip() for x in body.splitlines() if x.strip()];need(lines[-1]=='polynomial','return')
expect=[]
expect += [f'let {name} : Expr (Fin 14) := .var {i}' for i,name in enumerate(graph['witnesses'])]
expect += [f'let {name} : Expr (Fin 14) := .constant (p {i})' for i,name in enumerate(graph['fixed_numerals'])]
expect += [f'let {name} := {a} {op} {b}' for name,op,a,b in graph['source']];expect+=['polynomial']
need(lines==expect and len(graph['source'])==71,'complete rows and aliases')
def definition(src,name):
 match=re.search(r'^def '+name+r'\s+(.*?)(?=\n(?:def |theorem |end Ring))',src,re.M|re.S)
 need(match is not None,'missing definition '+name)
 return re.sub(r'\s+','',match.group(1)).replace('Carrier65.Core','Core')
sphere=D/'research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean'
need(H(sphere)=='a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5','sphere source')
need(definition(s,'auxiliary')==definition(sphere.read_text(),'auxiliary') and definition(s,'value71')==definition(gen,'value71'),'generic auxiliary/value definitions differ')
compact=re.sub(r'\s+','',s);need('theoremeval_expression(p:Fin4→ℤ)(v:Fin14→R):(expressionAtp).evalRingv=value71(funj=>(pj:R))v:=' in compact,'ring evaluator statement')
r=json.loads((P/'attempt04/result.json').read_text());out=json.loads((P/'attempt04/outer-observation.json').read_text())
need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==251 and out['session_id']==70915 and out['observed_outer_exit']==0,'run receipt')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
need(any(k.endswith('/Carrier94Value.olean') and v and v['sha256']=='a9c320a8e69a693aa869dbb7b272fe642e1bf76420e2602e580abbdfff52e887' for k,v in r['guards_after'].items()),'value provider')
obj=Path('/tmp/current2011-ordinary71-60-literal-check04/OrdinarySphere7160Literal.olean');need(H(obj)==r['object_sha256']=='b4386569a433cc7a0e2033368a9167081bb5e6e50ee8fd867df1938c01ed4e60','object')
log=(P/'attempt04/compile.log').read_text();need(H(P/'attempt04/compile.log')==r['log_sha256'] and log.strip()=="'DiophantineConsistency.OrdinarySphere7160Literal.eval_expression' depends on axioms: [propext]",'log')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'audit_rows.py')],capture_output=True);need(q.returncode==0 and q.stdout==(P/'row-audit.txt').read_bytes(),'row checker rerun')
for n,session,child in ((1,46258,-6),(2,48320,-6),(3,72934,1)):
 folder=P/f'attempt0{n}';x=json.loads((folder/'outer-observation.json').read_text());a=json.loads((folder/'result.json').read_text()); t=(folder/'compile.log').read_text()
 need(x['session_id']==session and x['observed_outer_exit']==1 and a['status']=='FAILED' and a['exit']==child and H(folder/'compile.log')==a['log_sha256'],'failed run '+str(n))
 need(('memory_exception' in t) if n<3 else ('error:' in t),'failed diagnostic '+str(n))
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_LITERAL_AUDIT','rows':71,'witness_aliases':14,'port_aliases':4,'guard_slots':251,'success_session':70915,'scope':'Exact Lean source/JSON rows and commutative-ring evaluator; no Lean replay, graph degree, model or iPRA theorem.'},indent=2,sort_keys=True))
