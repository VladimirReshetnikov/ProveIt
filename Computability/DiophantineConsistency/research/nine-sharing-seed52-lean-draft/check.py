#!/usr/bin/env python3
"""Check generated Lean term transcription against the frozen residual AST."""
import json,hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];S=D/'research/nine-sharing-quartic65-52-candidate/seed.json';sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest();assert sha(S)=='db5fc39eb7c8075ff7417b084a0c9a4755b497b1be388fe9d0aa1e65bad356ff';d=json.loads(S.read_text());source=(P/'SharingSeed52.lean').read_text();assert 'UNVERIFIED DRAFT' in source and 'sorry' not in source and 'admit' not in source
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def form(t):
 k=t[0]
 if k=='num':return f'(Expr.constant ({t[1]} : ℤ))'
 if k=='port':return f'(Expr.constant (p {ports[t[1]]}))'
 if k=='var':return f'(Expr.var {t[1]})'
 return '('+form(t[1])+' '+{'add':'+','sub':'-','mul':'*'}[k]+' '+form(t[2])+')'
def deg(t):
 if t[0] in ('num','port'):return 0
 if t[0]=='var':return 1
 a,b=map(deg,t[1:]);return a+b if t[0]=='mul' else max(a,b)
r=[form(x['expr']) for x in d['residuals']];first=source.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 53) :=\n  ',1)[1].split('\n',1)[0];block=source.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 53)) :=\n  [\n',1)[1].split('\n  ]',1)[0];tail=[x.strip().removesuffix(',') for x in block.splitlines()];assert first==r[0] and tail==r[1:] and len(r)==39 and max(deg(x['expr']) for x in d['residuals'])==2
for n in ['seed_weightedDegree','seed_degree','firstResidual_zeroWitness','eval_sumSquares_nonneg','seed_normalized']:assert 'theorem '+n in source
print(json.dumps({'status':'PASS_SOURCE_TRANSCRIPTION_ONLY','residuals':len(r),'max_residual_syntactic_degree':2,'source_sha256':sha(P/'SharingSeed52.lean'),'scope':'Generated Lean text matches external AST; no Lean compilation or model bridge proof.'},indent=2,sort_keys=True))
