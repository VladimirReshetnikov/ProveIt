#!/usr/bin/env python3
"""Check 67-row JSON against the historical Lean expression, without Lean."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')

import ast
import gzip
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
TASK = HERE.parents[1]
GRAPH = TASK/'research/fourteen-normalized-product106/polynomial.json'
SOURCE = TASK/'reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081/author/078/ModelCarrierSyntax.lean'
GRAPH_SHA = '0485cd1e884b918d766261b1780be117238f0813a965c6d8ae4d805176a5f6e1'
SOURCE_SHA = '8d40486fd9adf151e905977c01cbc1a2aa7142fbd02c5e4293906c6865e5a43a'

def need(ok,msg):
    if not ok: raise RuntimeError(msg)

def sha(data): return hashlib.sha256(data).hexdigest()

class Terms:
    """Hash-consed exact expression trees modulo commutativity/associativity."""
    def __init__(self): self.nodes=[]; self.index={}
    def intern(self,key):
        if key not in self.index:
            self.index[key]=len(self.nodes); self.nodes.append(key)
        return self.index[key]
    def atom(self,name): return self.intern(('atom',name))
    def num(self,n): return self.intern(('num',n))
    def binary(self,op,a,b):
        if op in ('+','*'):
            args=[]
            for q in (a,b):
                node=self.nodes[q]
                args.extend(node[1] if node[0]==op else [q])
            return self.intern((op,tuple(sorted(args))))
        if op == '-': return self.intern((op,a,b))
        raise RuntimeError('unsupported operation '+op)
    def power(self,a,n):
        need(n in (2,3),'unexpected power')
        x=a
        for _ in range(1,n): x=self.binary('*',x,a)
        return x

def parse_lean(source,variables,terms):
    block=source.split('def expressionAt106 (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)
    need(len(block)==2,'missing expressionAt106')
    block=block[1].split('/-- The 66/118 polynomial:',1)[0]
    lines=block.splitlines(); chunks=[]; output=[]
    for line in lines:
        if line.startswith('  let '): chunks.append([line.strip()])
        elif line.startswith('  P * Q'): output.append(line.strip())
        elif line.strip():
            if output: output.append(line.strip())
            else:
                need(bool(chunks),'orphan Lean continuation')
                chunks[-1].append(line.strip())
    environment={}
    ports=['beta','K0','MC','MF']
    def expr(text):
        text=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),text)
        tree=ast.parse(text.replace('^','**'),mode='eval').body
        def go(node):
            if isinstance(node,ast.Name):
                need(node.id in environment,'unknown name '+node.id);return environment[node.id]
            if isinstance(node,ast.Constant) and isinstance(node.value,int):return terms.num(node.value)
            if isinstance(node,ast.BinOp):
                if isinstance(node.op,ast.Pow):
                    need(isinstance(node.right,ast.Constant) and isinstance(node.right.value,int),'nonliteral exponent')
                    return terms.power(go(node.left),node.right.value)
                op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(node.op))
                need(op is not None,'unsupported operator')
                return terms.binary(op,go(node.left),go(node.right))
            raise RuntimeError('unsupported syntax '+ast.dump(node))
        return go(tree)
    for k,port in enumerate(ports):environment['port'+str(k)]=terms.atom(port)
    seen=[]
    for chunk in chunks:
        item=' '.join(chunk)
        m=re.fullmatch(r'let\s+(\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*)',item)
        need(m is not None,'bad let '+item)
        name,value=m.groups();need(name not in seen,'duplicate Lean let '+name);seen.append(name)
        v=re.fullmatch(r'\.var\s+(\d+)',value)
        if v:
            i=int(v.group(1));need(i < len(variables) and name==variables[i], 'variable index/order')
            environment[name]=terms.atom(name)
        else:environment[name]=expr(value)
    need(len(seen)>=14 and seen[:14]==variables,'missing witness lets')
    need(output,'missing output')
    return environment,expr(' '.join(output))

def graph_terms(graph,terms):
    values={x:terms.atom(x) for x in graph['witnesses']+graph['fixed_numerals']}
    producers={};ops=Counter()
    for name,op,a,b in graph['source']:
        need(name not in values and op in ('+','-','*'),'bad graph row')
        def val(x):
            if isinstance(x,int):return terms.num(x)
            need(x in values,'non-topological graph');return values[x]
        values[name]=terms.binary(op,val(a),val(b));producers[name]=(a,b);ops[op]+=1
    seen=set();leaves=set();todo=[graph['output']]
    while todo:
        name=todo.pop()
        if name in producers and name not in seen:
            seen.add(name);todo.extend(producers[name])
        elif isinstance(name,str) and name not in producers:
            leaves.add(name)
    need(len(seen)==67 and len(graph['source'])==67 and dict(ops)=={'*':38,'+':16,'-':13},'wrong live graph/count')
    need(leaves==set(graph['witnesses']+graph['fixed_numerals']), 'wrong live inputs')
    return values

def main():
    raw=GRAPH.read_bytes();source=SOURCE.read_bytes()
    need(sha(raw)==GRAPH_SHA and sha(source)==SOURCE_SHA,'input hash mismatch')
    graph=json.loads(raw);terms=Terms();g=graph_terms(graph,terms)
    need(graph['witnesses']==['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'], 'unexpected witnesses')
    need(graph['fixed_numerals']==['beta','K0','MC','MF'], 'unexpected port order')
    lean,out=parse_lean(source.decode(),graph['witnesses'],terms)
    cuts={'b':'qm','q':'q','C':'C','X':'X','Y':'Y','E':'E','k':'k','ell':'ell',
          'c':'c','a':'a','H':'H','delta':'Delta','D':'main_root','rank':'R',
          'tau':'tau','V':'V','P':'N0','Q':'N1','W':'Nt'}
    for a,b in cuts.items(): need(lean[a]==g[b],'cut mismatch '+a+' / '+b)
    need(out==g[graph['output']],'output expression mismatch')
    for p,meta in graph['coefficient_binding']['ports'].items():
        compressed=(GRAPH.parent/'coefficients'/meta['file']).read_bytes()
        need(sha(compressed)==meta['gzip_sha256'], 'port compressed hash '+p)
        rawport=gzip.decompress(compressed)
        need(sha(rawport)==meta['raw_sha256'] and len(rawport)==meta['raw_bytes'], 'port raw hash '+p)
    # Each independent corruption must either produce a mismatch or be rejected.
    bad=source.decode().replace('let X := w * q','let X := f * q',1)
    need(bad!=source.decode(),'control patch failed')
    changed=Terms();gg=graph_terms(graph,changed)
    _,wrong=parse_lean(bad,graph['witnesses'],changed)
    need(wrong!=gg[graph['output']],'changed witness control failed')
    print(json.dumps({'status':'PASS','graph_sha256':GRAPH_SHA,'lean_source_sha256':SOURCE_SHA,
        'checker_sha256':sha(Path(__file__).read_bytes()),'live_rows':67,'operation_counts':dict(ops for ops in Counter(r[1] for r in graph['source']).items()),
        'witnesses':graph['witnesses'],'ports':graph['fixed_numerals'],
        'cuts':cuts,'output_equal_mod_ac':True,'changed_witness_control':'rejected',
        'scope':'syntactic expression binding modulo associativity/commutativity; no Lean replay or fixed-port identity proof'},indent=2,sort_keys=True))

if __name__ == '__main__':main()
