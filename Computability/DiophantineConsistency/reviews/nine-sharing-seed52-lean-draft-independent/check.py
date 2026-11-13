#!/usr/bin/env python3
"""Read-only AST transcription audit; no Lean or generator run."""
import pathlib,hashlib,json,re,ast,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-seed52-lean-draft';Q=D/'research/nine-sharing-quartic65-52-candidate';S=P/'SharingSeed52.lean'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(Q/'seed.json')=='db5fc39eb7c8075ff7417b084a0c9a4755b497b1be388fe9d0aa1e65bad356ff';assert sha(S)=='a2a95f161d749985586b859d275b8cbec48b396d74e8bab78f71a28fbf3f1b86'
assert sha(P/'check.py')=='8fe1ceef29b5df3e865fc106da15808ff227acb67919d71ba9885b78824ea379' and sha(P/'generate.py')=='08152c6ac5ba1791bca9dfba0940d30ac421b67e4b48883a3d9bceb7b9f6aac6' and sha(P/'result.json')=='6d3de8fbd6f338bcb479011f24b3a0fe866dbfc13eb8e635a573fdd819cc8ee5'
d=json.loads((Q/'seed.json').read_text());source=S.read_text();assert 'UNVERIFIED DRAFT' in source and 'sorry' not in source and 'admit' not in source
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def expected(t):
 op=t[0]
 if op=='var':return ('var',t[1])
 if op=='port':return ('port',ports[t[1]])
 if op=='num':return ('num',t[1])
 return (op,expected(t[1]),expected(t[2]))
def parse(e):
 e=re.sub(r'\(Expr\.constant \(p ([0-3])\)\)',lambda m:'p'+m[1],e)
 e=re.sub(r'\(Expr\.constant \((\d+) : ℤ\)\)',lambda m:'c'+m[1],e)
 e=re.sub(r'\(Expr\.var (\d+)\)',lambda m:'v'+m[1],e)
 node=ast.parse(e,mode='eval').body
 def go(x):
  if isinstance(x,ast.Name):
   assert x.id[0] in 'pcv' and x.id[1:].isdigit();return ({'p':'port','c':'num','v':'var'}[x.id[0]],int(x.id[1:]))
  if isinstance(x,ast.BinOp):return ({ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul'}[type(x.op)],go(x.left),go(x.right))
  raise ValueError(ast.dump(x))
 return go(node)
first=source.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 53) :=\n  ',1)[1].split('\n',1)[0];body=source.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 53)) :=\n  [\n',1)[1].split('\n  ]',1)[0];lines=[x.strip().removesuffix(',') for x in body.splitlines()];assert len(lines)==38 and len(d['residuals'])==39
assert [parse(x) for x in [first]+lines]==[expected(x['expr']) for x in d['residuals']]
assert parse(first)==('sub',('var',15),('mul',('add',('mul',('port',0),('add',('var',1),('num',1))),('num',1)),('add',('mul',('port',0),('add',('var',1),('num',1))),('num',1))))
for x in ['firstResidual p * firstResidual p +','QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)','theorem seed_weightedDegree','theorem seed_degree','theorem firstResidual_zeroWitness','theorem eval_sumSquares_nonneg','theorem seed_normalized','(hp : 0 < p 0)','-- Unresolved: prove the all-IΣ₁-model zero bridge']:assert x in source,x
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'result.json').read_bytes()
print(json.dumps({'status':'PASS_SOURCE_AUDIT_ONLY','source_sha256':sha(S),'residuals':39,'port_index_mapping':ports,'scope':'Uncompiled source transcription only; no Lean proof, provider replay, all-model bridge or endpoint.'},indent=2))
