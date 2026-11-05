#!/usr/bin/env python3
"""Independent recursive-descent parser and two-sided natural-split counts."""
import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[2];L=D/'Lean/DiophantineConsistency';P=D/'research/nine-current-seed-count-diagnostic'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
for name,pin in [('CurrentEquationSyntax2011.lean','112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9'),('NaturalExpression.lean','0e0923fcc8dde83a1e8099a55e5ec8c804ff2b1648d8376b6c81ac343eac4e4f'),('Representation.lean','1b1a20d42422b0fffe2fb25ad4423c4914a0fcd1a0ccafcd1abdfcf863da92b7'),('QuarticCompilerCore.lean','699d642301db4fd06012f7b1b63f80f6793b5986cc36f285fddf00c63456e610')]:assert sha(L/name)==pin
assert sha(P/'check.py')=='7726f6c6ff671cf20c886f2f81ec73edf5553ef30304cd028d9fe30e28fc19d3' and sha(P/'result.json')=='96fb960586db96e143fddbdaf535b186dcdb773a86e4bdc4a1ce862233f23526'
s=(L/'CurrentEquationSyntax2011.lean').read_text();assert 'e.subst (fun i => Expr.var i + Expr.constant 1)' in s and 'def naturalExpression : Expr (Fin 14) := positiveShift expression' in s
nat=(L/'NaturalExpression.lean').read_text();assert '(a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)' in nat and '(a.1 + b.2, a.2 + b.1)' in nat
rep=(L/'Representation.lean').read_text();assert '| 0 => .constant 1\n  | n + 1 => .mul (e.pow n) e' in rep
quart=(L/'QuarticCompilerCore.lean').read_text();assert 'm + (Gates.count p + (Gates.count q + 1))' in quart
part=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('/-- The current ports',1)[0];head,tail=part.rsplit('\n  P * Q * U * W * Z - delta',1);assert not tail.strip();lets=re.findall(r'\n  let (\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*?)(?=\n  let |$)',head,re.S)
def combine(op,a,b):
 ap,an=a;bp,bn=b
 if op=='+':return ap+bp+1,an+bn+1
 if op=='-':return ap+bn+1,an+bp+1
 if op=='*':return (ap+bp+1)+(an+bn+1)+1,(ap+bn+1)+(an+bp+1)+1
 raise ValueError(op)
env={};indices=[]
def parse(text):
 text=re.sub(r'Expr\.constant\s*\(p\s+[0-3]\)','1',' '.join(text.split()));tokens=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[()+*^\-]',text);assert ''.join(tokens)==''.join(text.split()),text;pos=0
 def atom():
  nonlocal pos
  t=tokens[pos];pos+=1
  if t=='(':
   x=expr();assert tokens[pos]==')';pos+=1;return x
  if t.isdigit():return (1,1)
  return env[t]
 def power():
  nonlocal pos
  a=atom()
  if pos<len(tokens) and tokens[pos]=='^':
   pos+=1;e=int(tokens[pos]);pos+=1;v=(1,1)
   for _ in range(e):v=combine('*',v,a)
   return v
  return a
 def term():
  nonlocal pos
  x=power()
  while pos<len(tokens) and tokens[pos]=='*':pos+=1;x=combine('*',x,power())
  return x
 def expr():
  nonlocal pos
  x=term()
  while pos<len(tokens) and tokens[pos] in ('+','-'):
   op=tokens[pos];pos+=1;x=combine(op,x,term())
  return x
 result=expr();assert pos==len(tokens);return result
for name,e in lets:
 assert name not in env;m=re.fullmatch(r'\.var\s+(\d+)',' '.join(e.split()))
 if m:indices.append((name,int(m.group(1))));env[name]=(3,3)
 else:env[name]=parse(e)
assert indices==list(zip(['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'],range(14)))
left,right=parse('P * Q * U * W * Z - delta');witness=14+(left+(right+1));author=json.loads((P/'result.json').read_text());assert (left,right,witness)==(8446685,8446685,16893385)==(author['left_nodes'],author['right_nodes'],author['quartic_witness_count'])
print(json.dumps({'status':'PASS','left_nodes':left,'right_nodes':right,'quartic_witness_count':witness,'source_lets':len(lets),'scope':'Independent external syntax-structure count; no Lean numeric equality, Jones graph size or degree.'},indent=2))
