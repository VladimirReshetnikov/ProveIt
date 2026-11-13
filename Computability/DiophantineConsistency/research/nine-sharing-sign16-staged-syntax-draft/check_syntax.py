#!/usr/bin/env python3
"""Expand staged shared Lean syntax and compare each row to the pinned AST."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;seed=here.parent/'nine-sharing-sign16-degree112-v-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(seed)=='564ac66abad0fb5e286e5c0c05b5c3cbd05de13e68c9c9ac0b7c3a20a0c0b624';d=json.loads(seed.read_text());lex=re.compile(r'\s*(Expr\.constant|Expr\.var|shared[0-9]{2}|[0-9]+|p|ℤ|[()+*:\-])');ports=['beta','K0','MC','MF'];env={}
def parse(line):
 tokens=[];pos=0
 while pos<len(line):
  m=lex.match(line,pos);assert m,(pos,line[pos:pos+30]);tokens.append(m.group(1));pos=m.end()
 i=0
 def take(expected=None):
  nonlocal i
  assert i<len(tokens);t=tokens[i];i+=1
  if expected is not None:assert t==expected,(t,expected)
  return t
 def rec(depth=0):
  assert depth<80;take('(');t=tokens[i]
  if t.startswith('shared'):
   name=take();take('p');take(')');assert name in env;return env[name]
  if t=='Expr.var':
   take();n=int(take());assert 1<=n<=16;take(')');return ['var',n]
  if t=='Expr.constant':
   take();take('(');v=take()
   if v=='p':j=int(take());assert 0<=j<4;out=['port',ports[j]]
   else:out=['num',int(v)];take(':');take('ℤ')
   take(')');take(')');return out
  a=rec(depth+1);op=take();b=rec(depth+1);take(')');assert op in ('+','-','*');return [{'+':'add','-':'sub','*':'mul'}[op],a,b]
 result=rec();assert i==len(tokens);return result
files=[]
for block in range(8):
 p=here/f'SharingSeed16Shared{block:02}.lean';s=p.read_text();expected='DiophantineConsistency.NineFreshJones' if block==0 else f'DiophantineConsistency.SharingSeed16Shared{block-1:02}';assert s.startswith(f'import {expected}\n');assert 'sorry' not in s and 'admit' not in s
 for i in range(block*5,min(block*5+5,37)):
  name=f'shared{i:02}';prefix=f'def {name} (p : Fin 4 → ℤ) : Expr (Fin 17) :=\n  ';assert s.count(prefix)==1;env[name]=parse(s.split(prefix,1)[1].split('\n',1)[0])
 files.append(p)
assert len(d['residuals'])==7
for i,r in enumerate(d['residuals']):
 p=here/f'SharingSeed16Row{i:02}.lean';s=p.read_text();assert s.startswith('import DiophantineConsistency.SharingSeed16Shared07\n');prefix=f'def row{i:02} (p : Fin 4 → ℤ) : Expr (Fin 17) :=\n  ';assert s.count(prefix)==1;assert parse(s.split(prefix,1)[1].split('\n',1)[0])==r['expr'];assert 'sorry' not in s and 'admit' not in s;files.append(p)
p=here/'SharingSeed16Degree112.lean';s=p.read_text();imports='\n'.join(f'import DiophantineConsistency.SharingSeed16Row{i:02}' for i in range(7));assert s.startswith(imports+'\n');items=', '.join(f'row{i:02} p' for i in range(1,7));assert 'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 17) := row00 p' in s;assert f'def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 17)) := [{items}]' in s
assert '''def seed (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)''' in s
assert 'def zeroWitness (x : ℤ) (j : Fin 17) : ℤ := if j = 0 then x else 0' in s;files.append(p)
p=here/'SharingSign16Squares.lean';original=here.parent/'nine-sharing-sign19-model-bridge-draft/SharingSign19Squares.lean';assert p.read_text()==original.read_text().replace('SharingSeed19Degree44','SharingSeed16Degree112').replace('SharingSign19Squares','SharingSign16Squares').replace('sign19','sign16').replace('Fin 20','Fin 17');files.append(p)
print(json.dumps({'status':'PASS_SOURCE_AST_TRANSCRIPTION_ONLY','shared_definitions':len(env),'rows':7,'files':{p.name:sha(p) for p in files},'scope':'Expanded staged source rows match the external AST; no Lean compilation or model bridge.'},indent=2,sort_keys=True))
