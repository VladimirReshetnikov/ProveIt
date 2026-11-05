#!/usr/bin/env python3
"""Compare the displayed arithmetic core with expressionAt; not a TeX renderer."""
from pathlib import Path
import hashlib, json, re

D = Path(__file__).resolve().parents[2]
tex = (D / 'equation.tex').read_text()
lean = (D / 'Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean').read_text()

class ParseError(ValueError): pass

def digest(x):
    return hashlib.sha256(repr(x).encode()).hexdigest()

def expression(s, env):
    tokens = re.findall(r'@[A-Za-z]+|[A-Za-z]|[0-9]+|[-+*^()]', s)
    if ''.join(tokens) != re.sub(r'\s+', '', s):
        raise ParseError('unexpected arithmetic character: ' + s)
    i = 0
    def atom():
        nonlocal i
        if i >= len(tokens): raise ParseError('missing atom')
        t = tokens[i]; i += 1
        if t == '(':
            a = add()
            if i >= len(tokens) or tokens[i] != ')': raise ParseError('missing )')
            i += 1
            return a
        if t.isdigit(): return digest(('num', int(t)))
        if t not in env: raise ParseError('unknown symbol ' + t)
        return env[t]
    def power():
        nonlocal i
        a = atom()
        if i < len(tokens) and tokens[i] == '^':
            i += 1
            if i >= len(tokens) or not tokens[i].isdigit(): raise ParseError('nonliteral power')
            a = digest(('pow', a, int(tokens[i]))); i += 1
        return a
    def mul():
        nonlocal i
        a = power()
        while i < len(tokens):
            if tokens[i] == '*': i += 1
            elif tokens[i] not in env and not tokens[i].isdigit() and tokens[i] != '(': break
            a = digest(('mul', a, power()))
        return a
    def add():
        nonlocal i
        a = mul()
        while i < len(tokens) and tokens[i] in ('+', '-'):
            op = tokens[i]; i += 1
            a = digest((op, a, mul()))
        return a
    r = add()
    if i != len(tokens): raise ParseError('trailing tokens in ' + s)
    return r

coords = ['J','F','@alpha','z','f','i','T','s','w','n','@eta','@zeta','y','@gamma']
ports = ['@beta','K','@mu','@omega']
env0 = {name: digest(('var', i)) for i, name in enumerate(coords)}
env0.update({name: digest(('port', i)) for i, name in enumerate(ports)})
greek = {'alpha':'@alpha','beta':'@beta','eta':'@eta','zeta':'@zeta', 'gamma':'@gamma','Delta':'@delta','ell':'@ell','mu':'@mu','omega':'@omega','tau':'@tau'}
def tex_expr(s):
    s = re.sub(r'\\([A-Za-z]+)', lambda m: greek[m[1]] if m[1] in greek else (_ for _ in ()).throw(ParseError('unknown command '+m[0])), s)
    return s.replace('[','(').replace(']',')').replace('{','(').replace('}',')')

def tex_check(t):
    variables = t.split('The only unknowns are', 1)[1].split('\\[', 1)[1].split('\\]', 1)[0]
    variables = variables.split('\\in', 1)
    if len(variables) != 2 or re.sub(r'\s+', '', variables[1]) != r'\mathbbZ_{>0}.':
        raise ParseError('unexpected displayed domain')
    displayed = [tex_expr(x.strip()) for x in variables[0].split(',')]
    if displayed != coords: raise ParseError('displayed variable order differs')
    body = t.split('All other symbols in the equation are polynomial abbreviations:',1)[1].split('\\begin{gathered}',1)[1].split('\\end{gathered}',1)[0]
    body = body.replace('\\\\', ',').replace('\\quad', ',').strip().removesuffix('.')
    env = dict(env0); order=[]
    for decl in body.split(','):
        if not decl.strip(): continue
        if decl.count('=') != 1: raise ParseError('bad declaration: '+decl)
        name,rhs = map(str.strip, decl.split('='))
        name=tex_expr(name)
        if name in env: raise ParseError('repeated declaration: '+name)
        env[name]=expression(tex_expr(rhs),env);order.append(name)
    box=t.split('The single equation is',1)[1].split('\\boxed{',1)[1].split('}',1)[0]
    lhs,rhs=box.split('=')
    if rhs.strip().removesuffix('.')!='0': raise ParseError('equation is not zero')
    return expression(tex_expr(lhs),env),env,order

def lean_check(t):
    body=t.split('def expressionAt (p : Fin 4 → ℤ)',1)[1].split('/-- The current ports',1)[0]
    body=body.split(':=',1)[1]
    env=dict(env0)
    mapping={'alpha':'@alpha','eta':'@eta','zeta':'@zeta','gamma':'@gamma','delta':'@delta','ell':'@ell','tau':'@tau','rank':'R'}
    for i,name in enumerate(['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']):
        if not re.search(r'let\s+'+name+r'\s*:\s*Expr\s*\(Fin 14\)\s*:=\s*\.var\s+'+str(i)+r'\b',body): raise ParseError('variable map mismatch '+name)
    body=re.sub(r'  let \w+ : Expr \(Fin 14\) := \.var \d+[ \t]*\n','',body)
    chunks=re.split(r'\n  let ', body)
    if chunks[0].strip(): raise ParseError('unexpected prelude '+chunks[0])
    final=None;order=[]
    for chunk in chunks[1:]:
        name,rest=chunk.split(' := ',1)
        if name=='Z':
            rhs,final=rest.split('\n  ',1)
        else: rhs=rest
        rhs=re.sub(r'Expr\.constant \(p ([0-3])\)',lambda m: ports[int(m[1])],rhs)
        rhs=re.sub(r'\b(alpha|eta|zeta|gamma|delta|ell|tau|rank)\b',lambda m:mapping[m[1]],rhs)
        name=mapping.get(name,name)
        if name in env: raise ParseError('repeated declaration '+name)
        env[name]=expression(rhs,env);order.append(name)
    if final is None: raise ParseError('missing final expression')
    final=re.sub(r'\b(alpha|eta|zeta|gamma|delta|ell|tau|rank)\b',lambda m:mapping[m[1]],final)
    return expression(final,env),env,order

def run(t,l):
    a,te,to=tex_check(t); b,le,lo=lean_check(l)
    if set(to)!=set(lo): raise ParseError('different declared symbols: '+repr(set(to)^set(lo)))
    bad=[n for n in to if te[n]!=le[n]]
    if bad: raise ParseError('different expression trees: '+repr(bad))
    if a!=b: raise ParseError('different final expression')
    return to,a

order,root=run(tex,lean)
for old,new in [('S=i\\Delta c^2','S=i\\Delta c^3'),('PQUWZ-\\Delta=0','PQUWZ+\\Delta=0'),
                ('J,F,\\alpha,z','F,J,\\alpha,z'), ('\\mu+q\\omega','\\omega+q\\mu')]:
    assert old in tex
    try: run(tex.replace(old,new,1),lean)
    except ParseError: pass
    else: raise AssertionError('negative control passed')
for old,new in [('let J : Expr (Fin 14) := .var 0', 'let J : Expr (Fin 14) := .var 1'),
                ('let S := i * delta * c ^ 2', 'let S := i * delta * c ^ 3')]:
    assert old in lean
    try: run(tex,lean.replace(old,new,1))
    except ParseError: pass
    else: raise AssertionError('Lean negative control passed')
print(json.dumps({'status':'PASS','declarations':order,'count':len(order),'root_digest':root,
                  'tex_sha256':hashlib.sha256(tex.encode()).hexdigest(),
                  'lean_sha256':hashlib.sha256(lean.encode()).hexdigest(),
                  'negative_controls':6,'scope':'external structural comparison of displayed core arithmetic to Lean expressionAt; no formal TeX/PDF semantics or coefficient-recipe verification'},indent=2))
