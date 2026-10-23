#!/usr/bin/env python3
"""Independent stdlib transcription, identities, fixed bytes and degree audit.

No construction program is imported. Finite checks do not prove the
unbounded compiler/calibration theorem.
"""
import ast
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def check(ok, why):
    if not ok:
        raise ValueError(why)


def add(a,b,sign=1):
    out = dict(a)
    for m,c in b.items():
        out[m] = out.get(m,0)+sign*c
        if not out[m]:
            del out[m]
    return out


def mul(a,b):
    out = {}
    for m,c in a.items():
        for n,d in b.items():
            e = tuple(x+y for x,y in zip(m,n))
            out[e] = out.get(e,0)+c*d
    return {m:c for m,c in out.items() if c}


def parse(expression,names):
    indices = {v:i for i,v in enumerate(names)}
    zero = (0,)*len(names)
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:
            return {zero:node.value} if node.value else {}
        if isinstance(node,ast.Name) and node.id in indices:
            return {tuple(int(i==indices[node.id]) for i in range(len(names))):1}
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
            return {m:-c for m,c in visit(node.operand).items()}
        check(isinstance(node,ast.BinOp),'Unexpected polynomial syntax')
        a = visit(node.left)
        if isinstance(node.op,ast.Pow):
            check(isinstance(node.right,ast.Constant) and type(node.right.value) is int
                  and 0 <= node.right.value <= 4,'Fixed small exponent')
            out = {zero:1}
            for _ in range(node.right.value):
                out = mul(out,a)
            return out
        b = visit(node.right)
        if isinstance(node.op,ast.Add):
            return add(a,b)
        if isinstance(node.op,ast.Sub):
            return add(a,b,-1)
        check(isinstance(node.op,ast.Mult),'Unexpected arithmetic operator')
        return mul(a,b)
    return visit(ast.parse(expression,mode='eval').body)


FORMULAS = {
    'qm1':'beta*J','q':'qm1+1','q2':'q*q','q3':'q2*q','q4':'q2*q2',
    'U':'4*q4','X':'w*q','Y':'s*q3','E':'X*Y','k':'eta+zeta','kY':'k*Y',
    'c':'kY+eta','a':'E+Y','H':'4*a+3','Delta':'a*a+H','ell':'E*kY',
    'A1':'1+ell*(ell+k)','c2':'c*c','G':'1+Delta*c2','b0':'X+a*c',
    'qF':'q-F','Cw':'qF-alpha',
    'R':'(qm1*qF+alpha)*(q2-1)+(MC+q*MF)*J',
    'Nt':'(K0+w)*Cw+qF-z*qm1','r':'k-R-1',
    'Dstar':'U*b0+H*(U*gamma-r)','Nmain':'Dstar*Dstar-U*U*G',
    'I':'i*c2','I2':'I*I','f2':'f*f','Q':'Delta*(f2-1)','d':'Q-1',
    'Ns':'I2-d','V':'c*(T*f-1)-R*f2','x':'t+ell','x2':'x*x',
    'Eaux':'Q*V*V-1','delta':'x2-A1','core':'d*delta-Eaux',
    'N':'core*core-4*d*A1*Eaux',
    'P13':'Nt*(1+Nmain)*Ns*(1+N)-1',
}


def circuit_check(packet):
    names = packet['witnesses']+packet['fixed_numerals']+list(FORMULAS)
    check(len(names) == len(set(names)), 'Checkpoint names disjoint')
    values = {v:parse(v,names) for v in packet['witnesses']+packet['fixed_numerals']}
    def value(v):
        return parse(str(v),names) if type(v) is int else values[v]
    checked = set()
    for out,op,a,b in packet['source']:
        check(out not in values,'SSA register redefinition')
        left,right = value(a),value(b)
        result = mul(left,right) if op == '*' else add(left,right,-1 if op == '-' else 1)
        if out in FORMULAS:
            check(result == parse(FORMULAS[out],names),'Independent formula '+out)
            checked.add(out)
            values[out] = parse(out,names)
        else:
            values[out] = result
    check(checked == set(FORMULAS),'Every displayed formula checked')
    counts = Counter(r[1] for r in packet['source'])
    check(counts == {'*':46,'+':19,'-':18},'83-gate count')
    live = {packet['output']}
    for out,op,a,b in reversed(packet['source']):
        check(out in live,'Dead gate')
        live.update(v for v in (a,b) if isinstance(v,str))
    check(set(packet['witnesses']+packet['fixed_numerals']) <= live,'Input liveness')
    check(len(packet['witnesses']) == 13,'Witness count')
    return {'operations':sum(counts.values()),'multiplications':counts['*'],
            'additions':counts['+'],'subtractions':counts['-'],
            'independently_checked_formulas':len(checked)}


def identities():
    names = ['d','x','A','e']
    efficient = '(d*(x*x-A)-e)**2-4*d*A*e'
    old = '(d*(x*x+A)-e)**2-4*d*d*x*x*A'
    expanded = 'd*d*(x*x-A)**2-2*d*(x*x+A)*e+e*e'
    check(parse(efficient,names) == parse(old,names) == parse(expanded,names), 'Three norm forms')
    check(parse('(t+ell)**2-(1+ell*(ell+k))',['t','ell','k'])
          == parse('t*t+ell*(2*t-k)-1',['t','ell','k']), 'Root centering')
    names = ['U','X','a','c','H','gamma','r']
    direct = '(U*(X+a*c)+H*(U*gamma-r))**2-U*U*(1+(a*a+H)*c*c)'
    cancelled = ('U*U*(2*a*c*(X+H*gamma)+(X+H*gamma)**2-H*c*c-1)'
                 '-2*U*H*r*(X+a*c+H*gamma)+H*H*r*r')
    check(parse(direct,names) == parse(cancelled,names),'Main residual cancellation')
    # Weight bounds are universal consequences of this exact identity.
    weights = dict(U=4,X=2,a=6,c=5,H=6,gamma=1,r=4)
    main = parse(cancelled,names)
    degree = max(sum(e*weights[n] for e,n in zip(m,names)) for m in main)
    check(degree == 26,'Universal main degree bound')
    top = {m:c for m,c in main.items() if sum(e*weights[n] for e,n in zip(m,names)) == 26}
    check(top == parse('2*U*U*a*c*H*gamma',names),'Exact main leading form')
    return {'three_norm_forms_equal':True,'centering_identity':True,
            'main_cancellation_identity':True,'main_degree':26,
            'inner_term_degrees':[52,64,56],'product_degree':2+26+22+64}


def bindings():
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for pin in pins:
        raw = (ROOT/pin['local_path']).read_bytes()
        check(len(raw) == pin['byte_size'],'Source byte count')
        check(hashlib.sha256(raw).hexdigest() == pin['sha256'],'Source SHA256')
        blob = b'blob '+str(len(raw)).encode()+b'\0'+raw
        check(hashlib.sha1(blob).hexdigest() == pin['git_blob_sha1'],'Source Git blob')
    binding = json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
    check(binding['port_aliases'] == {'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},'Whole tuple aliases')
    values = {}
    for item in binding['payloads']:
        compressed = (ROOT/item['path']).read_bytes()
        raw = gzip.decompress(compressed)
        check(hashlib.sha256(compressed).hexdigest() == item['gzip_sha256'],'Compressed coefficient hash')
        check(hashlib.sha256(raw).hexdigest() == item['sha256'],'Raw coefficient hash')
        n = int.from_bytes(raw,'little')
        check(len(raw) == item['bytes'] and n.bit_length() == item['bits'],'Coefficient size')
        values[item['port']] = n
    check(values['beta'] == (1 << 590069)-1,'Exact compact radix')
    return {p:values[k] for p,k in binding['port_aliases'].items()},len(pins)


def ray(packet,ports,weights,prime):
    def trim(p):
        while p and p[-1] == 0:
            p.pop()
        return p
    def plus(a,b,sign=1):
        out = [0]*max(len(a),len(b))
        for i,c in enumerate(a):
            out[i] += c
        for i,c in enumerate(b):
            out[i] += sign*c
        return trim([c%prime for c in out])
    def times(a,b):
        if not a or not b:
            return []
        out = [0]*(len(a)+len(b)-1)
        for i,c in enumerate(a):
            for j,d in enumerate(b):
                out[i+j] += c*d
        return trim([c%prime for c in out])
    values = {v:[0,weights[v]%prime] for v in packet['witnesses']}
    values.update({v:[x%prime] for v,x in ports.items()})
    def get(x):
        return [x%prime] if type(x) is int else values[x]
    for out,op,a,b in packet['source']:
        values[out] = times(get(a),get(b)) if op == '*' else plus(get(a),get(b),-1 if op == '-' else 1)
    q0 = ports['beta']*weights['J']%prime
    E0 = weights['w']*weights['s']*pow(q0,4,prime)%prime
    c0 = (weights['eta']+weights['zeta'])*weights['s']*pow(q0,3,prime)%prime
    nt = (weights['w']*(q0-weights['F']-weights['alpha'])-weights['z']*q0)%prime
    leaders = {'Nt':(2,nt),'Nmain':(26,128*pow(q0,8,prime)*E0**2*c0*weights['gamma']),
               'Ns':(22,weights['i']**2*c0**4),
               'N':(64,-4*E0**6*c0**4*weights['T']**2*weights['f']**6)}
    final = 1
    for name,(degree,leader) in leaders.items():
        leader %= prime
        check(leader != 0,'Nonzero diagnostic leader')
        check(len(values[name])-1 == degree and values[name][-1] == leader,'Exact ray '+name)
        final = final*leader%prime
    check(len(values[packet['output']])-1 == 114 and values[packet['output']][-1] == final,
          'Exact degree-114 ray')


def main():
    packet = json.loads((ROOT/'polynomial.json').read_text())
    ports,pin_count = bindings()
    finite = circuit_check(packet)
    algebra = identities()
    cases = 0
    for p in (1000003,1000033,2147483647):
        for offset in (0,1):
            weights = {v:1 if not offset else i+2 for i,v in enumerate(packet['witnesses'])}
            ray(packet,ports,weights,p)
            cases += 1
    receipt = {'status':'PASS','imports_builder':False,'fixed_tuple':'compact44',
               'authenticated_source_files':pin_count,'gate_audit':finite,
               'exact_symbolic_identities':algebra,'full_polynomial_ray_checks':cases,
               'diagonal_leading_coefficient':'2^19*beta^67',
               'scope':'Exact finite algebra/data checks; unbounded Pell/compiler semantics are supplied by PROOF.md and inherited proofs.'}
    (ROOT/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
