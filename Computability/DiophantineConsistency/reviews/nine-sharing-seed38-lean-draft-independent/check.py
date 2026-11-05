#!/usr/bin/env python3
"""Read-only AST transcription audit; no Lean or generator run."""
import pathlib,hashlib,json,re,ast,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-seed38-lean-draft';Q=D/'research/nine-sharing-quartic65-norm38-candidate';S=P/'SharingSeed38.lean'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(Q/'seed.json')=='312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23';assert sha(S)=='7c459d84ce729a11a837c3c85199f0a01311dcdead6c8b6d4625ded386b72cf1'
assert sha(P/'check.py')=='25d7dab9c681e4e99ae3ceeca950ba25bea64f1f84cf59cfed34bd1f601a05a2' and sha(P/'generate.py')=='f18abbeda5f680ae891f6381462271b9b5b6dc2f1d15776ee6d9499f0ca5ab28' and sha(P/'result.json')=='baff77cfcf74e7e260897821d42fc4772cfe1f33bf2006376196c5fad01546eb'
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
first=source.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 39) :=\n  ',1)[1].split('\n',1)[0];body=source.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 39)) :=\n  [\n',1)[1].split('\n  ]',1)[0];lines=[x.strip().removesuffix(',') for x in body.splitlines()];assert len(lines)==28 and len(d['residuals'])==29
assert [parse(x) for x in [first]+lines]==[expected(x['expr']) for x in d['residuals']]
assert [(r['gate'],r['target']) for r in d['residuals'] if r['kind']=='norm']==[('N1',1),('N0',1),('Nt',1),('Na',1),('scaled_Ns','Delta')]
assert parse(first)==('sub',('var',15),('mul',('add',('mul',('port',0),('add',('var',1),('num',1))),('num',1)),('add',('mul',('port',0),('add',('var',1),('num',1))),('num',1))))
for x in ['firstResidual p * firstResidual p +','QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)','theorem seed_weightedDegree','theorem seed_degree','theorem firstResidual_zeroWitness','theorem eval_sumSquares_nonneg','theorem seed_normalized','(hp : 0 < p 0)','-- Unresolved: prove the all-IΣ₁-model zero bridge']:assert x in source,x
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'result.json').read_bytes()
print(json.dumps({'status':'PASS_SOURCE_AUDIT_ONLY','source_sha256':sha(S),'residuals':29,'port_index_mapping':ports,'scope':'Uncompiled source transcription only; no Lean proof, provider replay, all-model bridge or endpoint.'},indent=2))
