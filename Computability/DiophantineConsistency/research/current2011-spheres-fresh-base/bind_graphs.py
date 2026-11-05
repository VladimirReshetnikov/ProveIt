#!/usr/bin/env python3
"""Exact source-to-DAG comparison modulo associativity/commutativity, no Lean."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import ast, hashlib, json, re
from collections import Counter
from pathlib import Path
HERE = Path(__file__).resolve().parent
TASK = HERE.parents[1]
SOURCE = HERE/'FreshCarrierSpheres.lean'
SOURCESHA = 'a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5'
GRAPHS = {71: '937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2', 72: '70d6bd4ab1f4d4a868a4718543502734d250fca6a38eb64a5b90dda8107b3280'}
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


def lean_expr(text, env, terms):
    text=re.sub(r'Expr\.constant\s*\(p\s+(\d+)\)',lambda m:'port'+m.group(1),text)
    tree=ast.parse(text.replace('^','**'),mode='eval').body
    def go(n):
        if isinstance(n,ast.Name):
            need(n.id in env,'unknown name '+n.id);return env[n.id]
        if isinstance(n,ast.Constant) and isinstance(n.value,int): return terms.num(n.value)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Pow):
                need(isinstance(n.right,ast.Constant) and isinstance(n.right.value,int),'nonliteral power')
                return terms.power(go(n.left),n.right.value)
            op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}.get(type(n.op))
            need(op is not None,'unknown operation');return terms.binary(op,go(n.left),go(n.right))
        raise RuntimeError('unexpected AST '+ast.dump(n))
    return go(tree)

def parse(source, witnesses, terms, profile):
    sections=source.split('def frontAt (p : Fin 4 → ℤ)',1)
    need(len(sections)==2,'front missing'); block=sections[1].split('/-- The 14/71/80',1)[0]
    chunks=[];final=[]
    for line in block.splitlines():
        if line.startswith('  let '):chunks.append([line.strip()])
        elif line.startswith('  final '):final.append(line.strip())
        elif final and line.strip():final.append(line.strip())
        elif chunks and line.strip():chunks[-1].append(line.strip())
    env={f'port{i}':terms.atom(x) for i,x in enumerate(['beta','K0','MC','MF'])};names=[]
    for chunk in chunks:
        m=re.fullmatch(r'let\s+(\w+)(?:\s*:\s*Expr\s*\(Fin\s+14\))?\s*:=\s*(.*)',' '.join(chunk))
        need(m is not None,'bad let '+str(chunk)); name,text=m.groups();need(name not in names,'duplicate let');names.append(name)
        v=re.fullmatch(r'\.var\s+(\d+)',text)
        if v:
            i=int(v.group(1));need(i<len(witnesses) and witnesses[i]==name,'witness order');env[name]=terms.atom(name)
        else:env[name]=lean_expr(text,env,terms)
    need(names[:14]==witnesses,'witness prefix')
    actual=' '.join(final)
    expected='final P Q (delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2) W (f ^ 2 - delta * (i * c ^ 2) ^ 2)'
    need(actual==expected,'front final differs')
    env['U']=lean_expr('delta * (f ^ 2 - 1) * (V ^ 2 - y ^ 2) + y ^ 2',env,terms)
    env['S']=lean_expr('f ^ 2 - delta * (i * c ^ 2) ^ 2',env,terms)
    match=re.search(r'def expressionAt'+str(profile)+r' \(p : Fin 4 → ℤ\) : Expr \(Fin 14\) :=\s*frontAt p fun P Q U W S => ([^\n]+)',source)
    need(match is not None,'missing wrapper')
    return env,lean_expr(match.group(1),env,terms)

def graph_terms(graph, terms, profile):
    values={x:terms.atom(x) for x in graph['witnesses']+graph['fixed_numerals']};producers={};counts=Counter()
    for name,op,a,b in graph['source']:
        need(name not in values and op in ('+','-','*'),'bad gate')
        def val(x):
            if isinstance(x,int):return terms.num(x)
            need(x in values,'not topological '+str(x));return values[x]
        values[name]=terms.binary(op,val(a),val(b));producers[name]=(a,b);counts[op]+=1
    seen=set();leaves=set();todo=[graph['output']]
    while todo:
        name=todo.pop()
        if name in producers and name not in seen:seen.add(name);todo.extend(producers[name])
        elif isinstance(name,str) and name not in producers:leaves.add(name)
    need(len(seen)==len(graph['source'])==profile,'row count/liveness')
    need(leaves==set(graph['witnesses']+graph['fixed_numerals']),'dead inputs')
    return values,dict(counts)

def main():
    src=SOURCE.read_bytes();need(sha(src)==SOURCESHA,'source hash')
    out={}
    for profile,digest in GRAPHS.items():
        raw=(TASK/'research/fourteen-nonzero-spheres'/f'polynomial{profile}.json').read_bytes()
        need(sha(raw)==digest,'graph hash');g=json.loads(raw);terms=Terms()
        v,counts=graph_terms(g,terms,profile);env,result=parse(src.decode(),g['witnesses'],terms,profile)
        cuts={'b':'qm','q':'q','C':'C','X':'X','Y':'Y','E':'E','k':'k','ell':'ell',
          'c':'c','a':'a','H':'H','delta':'Delta','D':'main_root','rank':'R',
          'tau':'tau','V':'V','P':'N0','Q':'N1','W':'Nt','U':'U','S':'Z'}
        for a,b in cuts.items():need(env[a]==v[b],f'cut mismatch {a}/{b}')
        need(result==v[g['output']],'output mismatch')
        bad=src.decode().replace('let X := w * q','let X := f * q',1);need(bad!=src.decode(),'no mutation')
        t=Terms();vbad,_=graph_terms(g,t,profile);_,wrong=parse(bad,g['witnesses'],t,profile)
        need(wrong!=vbad[g['output']],'mutation passed')
        out[str(profile)]={'graph_sha256':digest,'live_rows':profile,'operations':counts,'checked_cuts':cuts,'output_equal_mod_ac':True,'mutation_rejected':True}
    print(json.dumps({'status':'PASS','source_sha256':SOURCESHA,'checker_sha256':sha(Path(__file__).read_bytes()),'graphs':out,'scope':'External syntactic comparison modulo associativity/commutativity; no Lean replay, fixed-port byte proof, or degree proof.'},indent=2,sort_keys=True))
if __name__=='__main__':main()
