#!/usr/bin/env python3
"""Independent 69/84 source rows and exact ring-evaluator receipt audit."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/current2011-ordinary69-84-literal';GRAPH=D/'research/current2011-ordinary69-84-candidate/polynomial.json'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={P/'OrdinarySphere6984Literal.lean':'dcf382876f4e7538f19a1a4ce584da76b218e008cd04842226236d31bf7bf71f',P/'check01.py':'1374f5de96b9b1a0305ddfa0a51ca3a1a0170443b787a11deef3074fb07f03f5',P/'audit_rows.py':'0e0f836dfa299dc7e8ab2e1396d5540c42e182684d9ca5f4cb78907524a8033d',P/'row-audit.txt':'dbb44d7748fbe0b51c5a86563ec5d24bccfe9056c841d5787c9607a2cdbcd583',P/'attempt01/result.json':'293474c21cf7a2c060f64178a0980fbcc8b0d412d6ee78c8592b54c5a8c09669',P/'attempt01/compile.log':'aa5d878ef521e7f52191649fe862b1ddf7e528d17efa920bda9d4b5e287ea465',P/'attempt01/outer-observation.json':'59dbfa701925bf59e04447a34b7277d587c5682f8d1dc7ffb3f633fdd53bf901',GRAPH:'c9781e95b9d8e3124afadfe3ee5874eb3eb76ce9f1aaef02c7b3bf49ed93e80a'}
for p,h in pins.items():need(H(p)==h,'pin '+str(p))
g=json.loads(GRAPH.read_bytes());s=(P/'OrdinarySphere6984Literal.lean').read_text();body=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Ring',1)[0];lines=[x.strip() for x in body.splitlines() if x.strip()]
expected=[f'let {x} : Expr (Fin 14) := .var {i}' for i,x in enumerate(g['witnesses'])]+[f'let {x} : Expr (Fin 14) := .constant (p {i})' for i,x in enumerate(g['fixed_numerals'])]+[f'let {n} := {a} {op} {b}' for n,op,a,b in g['source']]+['polynomial']
need(lines==expected and len(g['source'])==69,'literal graph rows and aliases')
cs=re.sub(r'\s+','',s);need('variable{R:Type*}[CommRingR]' in cs,'commutative ring context')
need('theoremeval_expression(p:Fin4→ℤ)(v:Fin14→R):(expressionAtp).evalRingv=value69(funj=>(pj:R))v:=' in cs,'eval theorem')
need('theoremtail_identity(uhx:R):u^2+h^2+x*(x-2)=u^2+(x-1)^2+h^2-1:=' in cs and 'theoremvalue_eq70(p:Fin4→R)(v:Fin14→R):value69pv=OrdinarySphere7084Literal.value70pv:=' in cs,'all-ring identity')
r=json.loads((P/'attempt01/result.json').read_text());o=json.loads((P/'attempt01/outer-observation.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'] and len(r['guards_after'])==273 and o['session_id']==64910 and o['observed_outer_exit']==0,'receipt/exit')
for key,v in r['guards_after'].items():
 p=Path(v.get('path',key.rsplit(':',1)[-1]) if v is not None else key.rsplit(':',1)[-1])
 if v is None:need(not os.path.lexists(p),'unexpected '+str(p))
 else:need(p.is_file() and str(p.resolve())==v['realpath'] and H(p)==v['sha256'],'guard drift '+str(p))
need(any(k.endswith('/OrdinarySphere7084Literal.olean') and v and v['sha256']=='69aea03a50aeb2f6d10a445c5664438771fe668174e45ac456ded02716b50720' for k,v in r['guards_after'].items()),'parent literal provider')
obj=Path('/tmp/current2011-ordinary69-84-literal-check01/OrdinarySphere6984Literal.olean');need(H(obj)==r['object_sha256']=='26e73fcd834d552ef3a24e2b45abadf48442ad964d534bba629f309e1b4794dd','object')
log=(P/'attempt01/compile.log').read_text();need(H(P/'attempt01/compile.log')==r['log_sha256'] and not any(x in log for x in ('error:','warning:','sorryAx')),'log');reports=re.findall(r"'DiophantineConsistency\.OrdinarySphere6984Literal\.(\w+)' depends on axioms: \[([^]]*)\]",log,re.S);need({n:{x.strip() for x in a.split(',')} for n,a in reports}=={'eval_expression':{'propext'},'value_eq70':{'propext','Quot.sound'}},'reports')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'audit_rows.py')],capture_output=True);need(q.returncode==0 and q.stdout==(P/'row-audit.txt').read_bytes(),'author row audit')
for folder in ('current2011-ordinary69-84-candidate-independent','current2011-ordinary70-84-literal-independent'):
 a=D/'reviews'/folder;z=subprocess.run([sys.executable,'-I','-S','-B',str(a/'check.py')],capture_output=True);need(z.returncode==0 and z.stdout==(a/'result.json').read_bytes(),'predecessor audit '+folder)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_LITERAL_AUDIT','rows':69,'witness_aliases':14,'port_aliases':4,'guard_slots':273,'outer_session':64910,'predecessor_reviews':2,'scope':'Exact Lean source/JSON rows and same-value commutative-ring identity; no Lean replay, JSON/file semantics or iPRA theorem.'},indent=2,sort_keys=True))
