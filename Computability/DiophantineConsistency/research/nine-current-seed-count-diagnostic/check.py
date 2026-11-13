#!/usr/bin/env python3
"""External structural count of the current seed's two natural expression trees."""
import ast,re,json,hashlib,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];L=D/'Lean/DiophantineConsistency'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={'CurrentEquationSyntax2011.lean':'112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9','NaturalExpression.lean':'0e0923fcc8dde83a1e8099a55e5ec8c804ff2b1648d8376b6c81ac343eac4e4f','Representation.lean':'1b1a20d42422b0fffe2fb25ad4423c4914a0fcd1a0ccafcd1abdfcf863da92b7','QuarticCompilerCore.lean':'699d642301db4fd06012f7b1b63f80f6793b5986cc36f285fddf00c63456e610'}
for n,h in pins.items():assert sha(L/n)==h
source=(L/'CurrentEquationSyntax2011.lean').read_text();s=source.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('/-- The current ports',1)[0];parts=s.rsplit('\n  P * Q * U * W * Z - delta',1);assert len(parts)==2 and not parts[1].strip();clauses=re.findall(r'\n  let (\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*?)(?=\n  let |$)',parts[0],re.S);env={};indices=[]
# Both split-natural trees have equal node counts: a split leaf gives (1,1),
# add/sub give p+q+1 each, multiplication gives 2p+2q+3 each.
def opmul(a,b):return 2*a+2*b+3
def parse(e):
 e=re.sub(r'Expr\.constant\s*\(p\s+\d+\)','1',e).replace('^','**')
 def go(x):
  if isinstance(x,ast.Constant) and type(x.value)==int:return 1
  if isinstance(x,ast.Name):return env[x.id]
  if isinstance(x,ast.BinOp):
   if isinstance(x.op,ast.Pow):
    assert isinstance(x.right,ast.Constant) and type(x.right.value)==int and 0<=x.right.value<=3
    a=go(x.left);v=1
    for _ in range(x.right.value):v=opmul(v,a)
    return v
   a=go(x.left);b=go(x.right)
   if isinstance(x.op,(ast.Add,ast.Sub)):return a+b+1
   if isinstance(x.op,ast.Mult):return opmul(a,b)
  raise ValueError(ast.dump(x))
 return go(ast.parse(e,mode='eval').body)
for n,e in clauses:
 assert n not in env;e=' '.join(e.split());m=re.fullmatch(r'\.var (\d+)',e)
 if m:
  indices.append((n,int(m.group(1))));env[n]=3 # positiveShift replaces each var by var + 1
 else:env[n]=parse(e)
assert indices==list(zip(['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'],range(14)))
count=parse('P * Q * U * W * Z - delta');nu=14+2*count+1
print(json.dumps({'status':'PASS_EXTERNAL_COUNT','left_nodes':count,'right_nodes':count,'original_witnesses':14,'guard_nodes':1,'quartic_witness_count':nu,'scope':'Source-structural computation only; no Lean equality proof, no Jones graph, coefficient expansion or degree assertion.'},indent=2,sort_keys=True))
