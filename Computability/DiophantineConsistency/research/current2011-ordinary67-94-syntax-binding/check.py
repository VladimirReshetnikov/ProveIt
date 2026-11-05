#!/usr/bin/env python3
"""Check current 67/94 graph against Carrier94 syntax modulo exact ring laws, without Lean."""
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
GRAPH = TASK/'research/current2011-ordinary67-94-candidate/polynomial.json'
SOURCE = TASK/'Lean/DiophantineConsistency/Carrier94Syntax.lean'
GRAPH_SHA = 'd76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb'
SOURCE_SHA = 'b68f54257ff1ebab090ed45e83d6c3719be51ccb0f7a7f03822e333bbb43ea8d'

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
    block=source.split('def expressionAt94 (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)
    need(len(block)==2,'missing expressionAt94')
    block=block[1].split('/-- At the maintained current ports.',1)[0]
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
    return environment,' '.join(output),expr

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
    need(len(seen)==67 and len(graph['source'])==67 and dict(ops)=={'*':37,'+':17,'-':13},'wrong live graph/count')
    need(leaves==set(graph['witnesses']+graph['fixed_numerals']), 'wrong live inputs')
    return values

def main():
    raw=GRAPH.read_bytes();source=SOURCE.read_bytes()
    need(sha(raw)==GRAPH_SHA and sha(source)==SOURCE_SHA,'input hash mismatch')
    graph=json.loads(raw);terms=Terms();g=graph_terms(graph,terms)
    need(graph['witnesses']==['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma'], 'unexpected witnesses')
    need(graph['fixed_numerals']==['beta','K0','MC','MF'], 'unexpected port order')
    lean,outtext,parse_output=parse_lean(source.decode(),graph['witnesses'],terms)
    cuts={'b':'qm','q':'q','C':'C','X':'X','Y':'Y','E':'E','k':'k','ell':'ell',
          'c':'c','a':'a','H':'H','delta':'Delta','D':'main_root','rank':'R',
          'tau':'tau','V':'V','P':'N0','Q':'N1','W':'Nt'}
    for a,b in cuts.items(): need(lean[a]==g[b],'cut mismatch '+a+' / '+b)
    # Z has the two exactly equivalent association orders (1+I²)-A and 1+(I²-A).
    def linear(t,nodes=terms):
        tag,*args=nodes.nodes[t]
        if tag=='num':return ({},args[0])
        if tag=='+':
            coeff={};constant=0
            for a in args[0]:
                cc,kk=linear(a,nodes);constant+=kk
                for k,v in cc.items():coeff[k]=coeff.get(k,0)+v
            return ({k:v for k,v in coeff.items() if v},constant)
        if tag=='-':
            left,lc=linear(args[0],nodes);right,rc=linear(args[1],nodes);coeff=left.copy()
            for k,v in right.items():coeff[k]=coeff.get(k,0)-v
            return ({k:v for k,v in coeff.items() if v},lc-rc)
        return ({t:1},0)
    need(linear(lean['Z'])==linear(g['Ns']),'strong additive identity')
    lean['Z']=g['Ns']
    need(parse_output(outtext)==g[graph['output']],'output expression mismatch')
    for p,meta in graph['coefficient_binding']['ports'].items():
        compressed=(TASK/'research/fourteen-nonzero-spheres/coefficients'/meta['file']).read_bytes()
        need(sha(compressed)==meta['gzip_sha256'], 'port compressed hash '+p)
        rawport=gzip.decompress(compressed)
        need(sha(rawport)==meta['raw_sha256'] and len(rawport)==meta['raw_bytes'], 'port raw hash '+p)
    # Each independent corruption must either produce a mismatch or be rejected.
    bad=source.decode().replace('let X := w * q','let X := f * q',1)
    need(bad!=source.decode(),'control patch failed')
    changed=Terms();gg=graph_terms(graph,changed)
    ll,txt,ee=parse_lean(bad,graph['witnesses'],changed)
    if linear(ll['Z'],changed)==linear(gg['Ns'],changed):
        ll['Z']=gg['Ns']
        need(ee(txt)!=gg[graph['output']],'changed witness control failed')
    print(json.dumps({'status':'PASS','graph_sha256':GRAPH_SHA,'lean_source_sha256':SOURCE_SHA,
        'checker_sha256':sha(Path(__file__).read_bytes()),'live_rows':67,'operation_counts':dict(ops for ops in Counter(r[1] for r in graph['source']).items()),
        'witnesses':graph['witnesses'],'ports':graph['fixed_numerals'],
        'cuts':cuts,'output_equal_mod_ring_associativity_commutativity_and_additive_negation':True,'changed_witness_control':'rejected',
        'scope':'external expression binding modulo AC and additive sign normalization; no Lean replay or fixed-port object provenance'},indent=2,sort_keys=True))

if __name__ == '__main__':main()
