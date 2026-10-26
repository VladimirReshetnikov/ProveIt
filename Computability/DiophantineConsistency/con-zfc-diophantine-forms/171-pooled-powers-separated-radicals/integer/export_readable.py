#!/usr/bin/env python3
"""Export complete residual literals; --check parses text by independent AST arithmetic."""
from pathlib import Path
import argparse,ast,json
ROOT=Path(__file__).resolve().parent
NAMES=['integer217','integer217_sparse','integer218','integer218_sparse']
def mathterm(c,m,tex=False):
 a=abs(c);v=''.join('x_{'+str(i)+'}'for i in m)if tex else '*'.join('x'+str(i)for i in m)
 if not m:s=str(a)
 elif a==1:s=v
 else:s=str(a)+(''if tex else '*')+v
 return ('-'if c<0 else '+')+s

def outputs(eq):
 n=len(eq['variables']);rs=eq['residuals'];txt=[f'All x0,...,x{n-1} range independently over the integers.',f'P = sum(R_i^2, i=0,...,{len(rs)-1}) = 0.','']
 tex=['% All variables are independently unrestricted integers.','\\begingroup\\small']
 for i,r in enumerate(rs):
  ts=[mathterm(c,m)for c,m in r['terms']];s=' '.join(ts);s=s[1:]if s.startswith('+')else s;txt.append(f'R{i} = {s}')
  ts=[mathterm(c,m,True)for c,m in r['terms']];chunks=[ts[j:j+5]for j in range(0,len(ts),5)];tex.append('\\begin{align*}')
  for j,ch in enumerate(chunks):
   s=' '.join(ch)
   if j==0 and s.startswith('+'):s=s[1:]
   line=(f'R_{{{i}}}&={{}}'if j==0 else '&\\quad{}')+s
   tex.append(line+('\\\\'if j<len(chunks)-1 else ''))
  tex.append('\\end{align*}')
 tex.append('\\endgroup')
 var=['index\tname\tkind']+[f"{i}\t{v['name']}\t{v['kind']}"for i,v in enumerate(eq['variables'])]
 return {'residuals.txt':'\n'.join(txt)+'\n','residuals.tex':'\n'.join(tex)+'\n','variables.tsv':'\n'.join(var)+'\n'}
def add(a,b,k=1):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+k*c
 return {m:c for m,c in r.items()if c}
def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   v=tuple(sorted(m+n));r[v]=r.get(v,0)+c*d
 return {m:c for m,c in r.items()if c}
def parse(node):
 if isinstance(node,ast.Constant)and type(node.value)is int:return {():node.value}if node.value else{}
 if isinstance(node,ast.Name)and node.id.startswith('x')and node.id[1:].isdigit():return {(int(node.id[1:]),):1}
 if isinstance(node,ast.UnaryOp)and isinstance(node.op,ast.USub):return {m:-c for m,c in parse(node.operand).items()}
 if isinstance(node,ast.UnaryOp)and isinstance(node.op,ast.UAdd):return parse(node.operand)
 if isinstance(node,ast.BinOp):
  a,b=parse(node.left),parse(node.right)
  if isinstance(node.op,ast.Add):return add(a,b)
  if isinstance(node.op,ast.Sub):return add(a,b,-1)
  if isinstance(node.op,ast.Mult):return mul(a,b)
 raise ValueError('unsupported printed expression')
def main(check=False):
 for name in NAMES:
  p=ROOT/name;eq=json.loads((p/'equation.json').read_text());out=outputs(eq)
  for fn,s in out.items():
   if check:
    if (p/fn).read_text()!=s:raise ValueError('readable export '+name+'/'+fn)
   else:(p/fn).write_text(s)
  for i,line in enumerate(out['residuals.txt'].splitlines()[3:]):
   literal=parse(ast.parse(line.split(' = ',1)[1],mode='eval').body);expected={tuple(m):c for c,m in eq['residuals'][i]['terms']}
   if literal!=expected:raise ValueError('printed polynomial differs')
 print(json.dumps({'status':'PASS','profiles':NAMES,'printed_residuals':sum(len(json.loads((ROOT/n/'equation.json').read_text())['residuals'])for n in NAMES),'independent_AST_parse':True}))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args();main(a.check)
