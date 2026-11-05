#!/usr/bin/env python3
"""Compare the current 65-gate graph with the exact current Lean syntax."""
import ast,collections,hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];G=D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';S=D/'Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise RuntimeError(msg)
need(sha(G)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(S)=='112c21a16ddb3d45b311dbe9099ea89619ff6b25f6fb61050d9a7b8f8898d2f9','source pins')
class C:
 def __init__(self):self.nodes=[];self.ids={}
 def node(self,key):
  if key not in self.ids:self.ids[key]=len(self.nodes);self.nodes.append(key)
  return self.ids[key]
 def number(self,n):return self.node(('n',n))
 def plus(self,a,b,sign=1):
  terms=collections.Counter();const=0
  for x,mult in ((a,1),(b,sign)):
   v=self.nodes[x]
   if v[0]=='n':const+=mult*v[1]
   elif v[0]=='sum':
    const+=mult*v[2]
    for term,count in v[1]:terms[term]+=mult*count
   else:terms[x]+=mult
  z=tuple(sorted((key,val) for key,val in terms.items() if val));
  if not z:return self.number(const)
  if len(z)==1 and z[0][1]==1 and const==0:return z[0][0]
  return self.node(('sum',z,const))
 def mul(self,a,b):
  terms=[]
  for x in (a,b):terms.extend(self.nodes[x][1] if self.nodes[x][0]=='mul' else (x,))
  return self.node(('mul',tuple(sorted(terms))))
 def op(self,op,a,b):return self.mul(a,b) if op=='*' else self.plus(a,b,1 if op=='+' else -1)
 def parse(self,expr,env):
  expr=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),expr)
  def go(x):
   if isinstance(x,ast.Name):need(x.id in env,'unknown name '+x.id);return env[x.id]
   if isinstance(x,ast.Constant) and type(x.value)==int:return self.number(x.value)
   if isinstance(x,ast.BinOp):
    if isinstance(x.op,ast.Pow):
     need(isinstance(x.right,ast.Constant) and x.right.value in (2,3),'power');z=go(x.left);out=z
     for _ in range(1,x.right.value):out=self.mul(out,z)
     return out
    op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(x.op));need(op is not None,'op');return self.op(op,go(x.left),go(x.right))
   raise RuntimeError('unsupported AST')
  return go(ast.parse(expr.replace('^','**'),mode='eval').body)
g=json.loads(G.read_text());source=S.read_text().split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('/-- The current ports',1)[0];parts=source.rsplit('\n  P * Q * U * W * Z - delta',1);need(len(parts)==2 and not parts[1].strip(),'source output');clauses=re.findall(r'\n  let (\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*?)(?=\n  let |$)',parts[0],re.S);c=C();env={f'port{i}':c.node(('v',n)) for i,n in enumerate(g['fixed_numerals'])};indices=[]
for n,e in clauses:
 e=' '.join(e.split());m=re.fullmatch(r'\.var (\d+)',e)
 if m:
  i=int(m.group(1));indices.append((n,i));need(i<len(g['witnesses']) and g['witnesses'][i]==n,'source witness');env[n]=c.node(('v',n))
 else:env[n]=c.parse(e,env)
need(len(indices)==14,'witness count');target=c.parse('P * Q * U * W * Z - delta',env);gv={n:c.node(('v',n)) for n in g['witnesses']+g['fixed_numerals']}
for n,op,a,b in g['source']:
 need(n not in gv and all(type(x)==int or x in gv for x in (a,b)),'topology');gv[n]=c.op(op,gv[a] if isinstance(a,str) else c.number(a),gv[b] if isinstance(b,str) else c.number(b))
need(target==gv[g['output']] and len(g['source'])==65,'full source binding');wrong=c.parse('P * Q * U * W * Z + delta',env);need(wrong!=target,'mutation')
print(json.dumps({'status':'PASS_EXTERNAL_SOURCE_BINDING','operations':65,'source_graph_sha256':sha(G),'lean_source_sha256':sha(S),'scope':'Canonical expression DAG modulo associative/commutative multiplication and signed addition; no Lean graph theorem.'},indent=2,sort_keys=True))
