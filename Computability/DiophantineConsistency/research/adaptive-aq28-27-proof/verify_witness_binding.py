#!/usr/bin/env python3
"""Check draft residuals and witness maps against pinned graphs, without Lean.

This checks syntactic expression trees, not just polynomial equality: the
draft transport uses `change`, which needs definitional alignment. It does not
type-check any Lean source or prove the model/native theorems.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re

D=Path(__file__).resolve().parent
ROOT=D.parents[1]
PINS={29:'894ff6fa3205629c03de826d8984f4959c2be317bf61c46d0f393f770d113a20',
      28:'6ddad50448c27a371e27cd90f860e30ca8632c57d539f91c2f1c08f10ed1fd27',
      27:'1982b2f164b9b72f965050e3a26cec751f7d0839c2da0cbe3cc020b7e6fc0170',
      26:'d8e80e15d74271ba62877e841198a85729c0c4a74a5927927591b9ec2204b1a5'}
DELETED={28:('varphiSquareVariable','varphiSquareDifference'),
         27:('ellProductVariable','ellProductDifference'),
         26:('scaledIndexVariable','scaledIndexDifference')}

class Nodes:
    def __init__(self): self.nodes=[];self.index={}
    def make(self,*key):
        if key not in self.index:self.index[key]=len(self.nodes);self.nodes.append(key)
        return self.index[key]
    def op(self,op,a,b):return self.make(op,a,b)
    def sub(self,node,fill,memo=None):
        memo={} if memo is None else memo
        if node in memo:return memo[node]
        term=self.nodes[node]
        if term[0]=='var':out=fill[term[1]]
        elif term[0] in ('port','const'):out=node
        else:out=self.op(term[0],self.sub(term[1],fill,memo),self.sub(term[2],fill,memo))
        memo[node]=out;return out

def graph(n):
    raw=(D.parent/f'adaptive-square-sums{n}-degree8/candidate.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PINS[n]:raise ValueError(('candidate pin',n))
    return json.loads(raw)

def build(g,nodes):
    env={name:nodes.make('var',i) for i,name in enumerate(g['witnesses'])}
    env.update({name:nodes.make('port',i) for i,name in enumerate(g['fixed_numerals'])})
    def val(a):return nodes.make('const',a) if isinstance(a,int) else env[a]
    for name,op,a,b in g['source']:
        if name in env:raise ValueError(('duplicate graph binding',name))
        env[name]=nodes.op(op,val(a),val(b))
    return env

def residuals(n,g,nodes,source):
    start=source.index('def residuals ');end=source.index('\ndef sum ',start)
    block=source[start:end].splitlines();env={};factors=None
    rows={row[0]:row for row in g['source']}
    for line in block[1:]:
        if m:=re.fullmatch(r'  let (\w+) : Expr \(Fin \d+\) := \.var (\d+)',line):
            name,idx=m.group(1),int(m.group(2))
            if idx>=len(g['witnesses']) or g['witnesses'][idx]!=name:raise ValueError(('witness binding',n,line))
            env[name]=nodes.make('var',idx)
        elif m:=re.fullmatch(r'  let (\w+) : Expr \(Fin \d+\) := \.constant \(p (\d+)\)',line):
            name,idx=m.group(1),int(m.group(2))
            if idx>=len(g['fixed_numerals']) or g['fixed_numerals'][idx]!=name:raise ValueError(('port binding',n,line))
            env[name]=nodes.make('port',idx)
        elif m:=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line):
            name,a,op,b=m.groups()
            if name not in rows or rows[name]!=[name,op,int(a) if a.isdigit() else a,int(b) if b.isdigit() else b]:
                raise ValueError(('residual graph binding',n,line))
            value=lambda x:nodes.make('const',int(x)) if x.isdigit() else env[x]
            env[name]=nodes.op(op,value(a),value(b))
        elif m:=re.fullmatch(r'  !\[(.*)\]',line):factors=m.group(1).split(',')
        else:raise ValueError(('unrecognized residual line',n,line))
    if factors is None or any(x not in env for x in factors):raise ValueError(('residual vector',n))
    vals=[env[x] for x in factors]
    if not vals:raise ValueError('empty residual list')
    if block[0]!=f'def residuals (p : Fin 4 → ℤ) : Fin {len(vals)} → Expr (Fin {n}) :=':
        raise ValueError(('residual signature',n))
    folded=nodes.op('*',vals[0],vals[0])
    for x in vals[1:]:folded=nodes.op('+',folded,nodes.op('*',x,x))
    if folded!=build(g,nodes)[g['output']]:raise ValueError(('sum not definitionally aligned',n))
    line=source[end:].splitlines()[1]
    expected=f'def sum (p : Fin 4 → ℤ) : Expr (Fin {n}) := '+' + '.join(
        f'(residuals p {i})*(residuals p {i})' for i in range(len(vals)))
    if line!=expected:raise ValueError(('sum declaration',n))
    if f'theorem sum_shape (p : Fin 4 → ℤ) : sum p = AdaptiveAQ{n}Literal.literal p := by rfl' not in source:
        raise ValueError(('sum shape assertion',n))
    if (f'InternalZero (AdaptiveAQ{n}Literal.literal p) v ↔ ∀ i : Fin {len(vals)}, InternalZero (residuals p i) v'
            not in source):raise ValueError(('sum-zero statement',n))
    return factors,vals

def parse_expr(text,nodes,kind):
    pattern=r'\.var (\d+)' if kind=='expr' else r'\bv (\d+)'
    normalized=re.sub(pattern,lambda m:'v'+m.group(1),text)
    def visit(x):
        if isinstance(x,ast.Name) and re.fullmatch(r'v\d+',x.id):return nodes.make('var',int(x.id[1:]))
        if isinstance(x,ast.Constant) and isinstance(x.value,int):return nodes.make('const',x.value)
        if isinstance(x,ast.BinOp) and type(x.op) in (ast.Add,ast.Sub,ast.Mult):
            return nodes.op({ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}[type(x.op)],visit(x.left),visit(x.right))
        raise ValueError(('unsupported expression',text))
    return visit(ast.parse(normalized,mode='eval').body)

def positive(node,nodes):
    x=nodes.nodes[node]
    return x[0]=='var' or (x[0] in ('+','*') and positive(x[1],nodes) and positive(x[2],nodes))

def verify(drafts):
    nodes=Nodes();gs={n:graph(n) for n in (29,28,27,26)}
    zs={29:(ROOT/'Lean/DiophantineConsistency/AdaptiveAQ29Zeros.lean').read_text()}
    zs.update({n:(drafts/f'AdaptiveAQ{n}Zeros.lean').read_text() for n in (28,27,26)})
    rs={n:residuals(n,gs[n],nodes,zs[n]) for n in (29,28,27,26)}
    for n in (28,27,26):
        old,new=gs[n+1],gs[n];removed,defining=DELETED[n]
        rindex=old['witnesses'].index(removed)
        if new['witnesses']!=old['witnesses'][:rindex]+old['witnesses'][rindex+1:]:
            raise ValueError(('witness projection',n))
        oldnames,oldres=rs[n+1];newnames,newres=rs[n];index=oldnames.index(defining)
        if newnames!=oldnames[:index]+oldnames[index+1:]:raise ValueError(('residual projection',n))
        maps=(drafts/f'AdaptiveAQ{n}Maps.lean').read_text()
        transport=(drafts/f'AdaptiveAQ{n}Transport.lean').read_text()
        def vector(text,prefix):
            match=re.search(prefix+r'[^\n]*:= !\[([^\n]*)\]',text)
            if not match:raise ValueError(('missing vector',n,prefix))
            return [x.strip() for x in match.group(1).split(',')]
        project=vector(maps,r'def project ');extend=vector(maps,r'def extend ');fill=vector(transport,r'def fill ')
        if project!=[f'v {i}' for i in range(n+1) if i!=rindex] or len(extend)!=n+1 or len(fill)!=n+1:
            raise ValueError(('map dimensions or projection',n))
        fnodes=[parse_expr(x,nodes,'expr') for x in fill]
        vnodes=[parse_expr(x,nodes,'value') for x in extend]
        expected=[nodes.make('var',i if i<rindex else i-1) for i in range(n+1) if i!=rindex]
        if fnodes[:rindex]+fnodes[rindex+1:]!=expected or vnodes!=fnodes:
            raise ValueError(('map/fill mismatch',n))
        oldenv=build(old,nodes);definition=nodes.nodes[oldenv[defining]]
        if definition[0]!='-' or definition[1]!=nodes.make('var',rindex):raise ValueError(('deleted residual shape',n))
        rhs=nodes.sub(definition[2],fnodes)
        if rhs!=fnodes[rindex] or not positive(rhs,nodes):raise ValueError(('reconstruction or positivity shape',n))
        for j,old_node in enumerate(oldres):
            subst=nodes.sub(old_node,fnodes)
            want=nodes.op('-',rhs,rhs) if j==index else newres[j if j<index else j-1]
            if subst!=want:raise ValueError(('residual syntactic mismatch',n,j))
        if f'have h9 := hall {index}' not in transport:raise ValueError(('deleted equation index',n))
        input_block=transport.split('theorem project_inputs ',1)[1].split('#print axioms extend_inputs',1)[0]
        changes=[line.strip() for line in input_block.splitlines() if line.strip().startswith('change InternalZero (')]
        if len(changes)!=1 or not changes[0].endswith(') v at h9'):
            raise ValueError(('deleted equation syntax',n))
        actual_change=changes[0][len('change InternalZero ('):-len(') v at h9')]
        if parse_expr(actual_change,nodes,'expr')!=oldenv[defining]:raise ValueError(('deleted equation expression',n))
        if f'(i : Fin {len(oldres)})' not in transport:raise ValueError(('parent residual range',n))
        extend_block=transport.split('theorem extend_zero ',1)[1].split('theorem project_zero ',1)[0]
        projected=transport.split('theorem project_zero ',1)[1].split('#print axioms',1)[0]
        cases=extend_block.split('  fin_cases i\n',1)[1].split('  · ')[1:]
        if len(cases)!=len(oldres):raise ValueError(('extend branch count',n))
        for j,case in enumerate(cases):
            if j==index:
                if 'simp only [InternalZero]' not in case or 'exact add_comm _ _' not in case:raise ValueError(('deleted branch',n))
                lines=[line.strip() for line in case.splitlines() if line.strip().startswith('change InternalZero (')]
                if len(lines)!=1 or not lines[0].endswith(') v'):
                    raise ValueError(('deleted branch syntax',n))
                expression=lines[0][len('change InternalZero ('):-len(') v')]
                if parse_expr(expression,nodes,'expr')!=nodes.op('-',rhs,rhs):
                    raise ValueError(('deleted branch expression',n))
            else:
                k=j if j<index else j-1
                if f'change InternalZero (AdaptiveAQ{n}Zeros.residuals p {k}) v' not in case or f'exact hall {k}' not in case:
                    raise ValueError(('extend branch',n,j))
        pcases=projected.split('  fin_cases i\n',1)[1].split('  · ')[1:]
        if len(pcases)!=len(newres):raise ValueError(('project branch count',n))
        for j,case in enumerate(pcases):
            k=j if j<index else j+1
            if f'(project_inputs p v hz) {k}).mp (hall {k})' not in case or f'AdaptiveAQ{n}Zeros.residuals p {j}' not in case:
                raise ValueError(('project branch',n,j))
        model=(drafts/f'AdaptiveAQ{n}.lean').read_text()
        child=f'InternalZero (positiveShift (AdaptiveAQ{n}Literal.literal p))'
        parent=f'InternalZero (positiveShift (AdaptiveAQ{n+1}Literal.literal p))'
        if child not in model or parent not in model or 'theorem shifted_no_zero_iff ' not in model:
            raise ValueError(('model endpoint wiring',n))
        native=(drafts/f'IPRAAQ{n}Native.lean').read_text()
        required=[f'import DiophantineConsistency.IPRAAQ{n+1}Native',
                  f'import DiophantineConsistency.AdaptiveAQ{n}',
                  f'AdaptiveAQ{n}.current_no_zero_iff',
                  f'IPRAAQ{n+1}Native.literalNatural',f'IPRAAQ{n+1}Native.bridge{n+1}',
                  f'positiveShift (AdaptiveAQ{n}Literal.literal CurrentWindowCarry2011.ports)',
                  '∼mappedNativeRefutation embedding']
        if any(item not in native for item in required):raise ValueError(('native endpoint wiring',n))
        claim=native.split('theorem literal_equivalence ',1)[1].split('#print axioms',1)[0]
        if (f'positiveShift (AdaptiveAQ{n}Literal.literal CurrentWindowCarry2011.ports)' not in claim
                or '∼mappedNativeRefutation embedding' not in claim):
            raise ValueError(('native theorem statement',n))
        print(f'PASS: AQ{n} residual syntax, positive witness maps and all {len(oldres)} transport indices align; no Lean compilation')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--draft-dir',type=Path,default=D/'draft-src');args=p.parse_args()
    verify(args.draft_dir)
