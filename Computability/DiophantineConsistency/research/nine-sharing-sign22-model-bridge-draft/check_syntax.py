#!/usr/bin/env python3
"""Parse generated Lean residuals independently and compare to the pinned AST."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=D/'research/nine-sharing-sign22-dodecic-ky-candidate/seed.json';assert sha(source)=='3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37';d=json.loads(source.read_text())
lean=P/'SharingSeed22Dodecic.lean';s=lean.read_text();assert 'UNCOMPILED generated syntax' in s and 'sorry' not in s and 'admit' not in s
first=s.split('def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 23) :=\n  ',1)[1].split('\n',1)[0]
block=s.split('def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 23)) :=\n  [\n',1)[1].split('\n  ]',1)[0]
rows=[first]+[x.strip().removesuffix(',') for x in block.splitlines()]
assert len(rows)==len(d['residuals'])==13 and d['witness_count']==22
lex=re.compile(r'\s*(Expr\.constant|Expr\.var|[0-9]+|p|ℤ|[()+*:\-])');port=['beta','K0','MC','MF'];used=set()
def parse(line):
 tokens=[];pos=0
 while pos<len(line):
  m=lex.match(line,pos);assert m,(line[pos:pos+30],pos);tokens.append(m.group(1));pos=m.end()
 i=0
 def take(t=None):
  nonlocal i
  assert i<len(tokens);x=tokens[i];i+=1
  if t is not None:assert x==t,(x,t)
  return x
 def rec(depth=0):
  assert depth<=80;take('(');t=tokens[i]
  if t=='Expr.var':
   take();n=int(take());assert 1<=n<=22;used.add(n);take(')');return ['var',n]
  if t=='Expr.constant':
   take();take('(');v=take()
   if v=='p':
    j=int(take());assert 0<=j<4;out=['port',port[j]]
   else:
    n=int(v);take(':');take('ℤ');out=['num',n]
   take(')');take(')');return out
  a=rec(depth+1);op=take();assert op in ('+','-','*');b=rec(depth+1);take(')');return [{'+':'add','-':'sub','*':'mul'}[op],a,b]
 out=rec();assert i==len(tokens);return out
parsed=[parse(line) for line in rows];assert parsed==[x['expr'] for x in d['residuals']]
def degree(t):
 if t[0] in ('num','port'):return 0
 if t[0]=='var':return 1
 a,b=map(degree,t[1:]);return a+b if t[0]=='mul' else max(a,b)
assert max(map(degree,parsed))==6 and 0 not in used
assert '''def seed (p : Fin 4 → ℤ) : Expr (Fin 23) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)''' in s
assert 'def zeroWitness (x : ℤ) (j : Fin 23) : ℤ := if j = 0 then x else 0' in s
print(json.dumps({'status':'PASS_SOURCE_AST_TRANSCRIPTION_ONLY','source_sha256':sha(lean),'seed_json_sha256':sha(source),'residuals':len(rows),'max_residual_syntactic_degree':6,'coordinate_zero_unused':True,'coordinate_indices':sorted(used),'scope':'Parsed Lean residual syntax matches external candidate AST; no Lean compilation, current-source bridge or iPRA endpoint.'},indent=2,sort_keys=True))
