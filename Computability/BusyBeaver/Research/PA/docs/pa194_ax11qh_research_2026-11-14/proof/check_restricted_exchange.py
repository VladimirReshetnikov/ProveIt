#!/usr/bin/env python3
"""Extract and check the fixed exchange derivation from the restricted axiom.

This is a finite symbolic proof check, not a Lean invocation.  Every generated
row has the actual dominated rho8 shape and a bound justified by subterm
containment; every modus-ponens edge is checked in the free implication algebra.
The proof therefore instantiates at all natural numbers, including zero aliases.
"""
import argparse, functools, hashlib, json, re
from pathlib import Path


def parse_expression(source):
    toks = re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|⟹|[()]', source)
    if ''.join(toks) != re.sub(r'\s+', '', source):
        raise ValueError('Unexpected syntax in finite proof definition')
    pos = 0
    def atom():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == '(':
            x = implication()
            assert toks[pos] == ')'
            pos += 1
            return x
        assert t not in (')', '⟹')
        return ('name', t)
    def application():
        nonlocal pos
        a = atom(); args = []
        while pos < len(toks) and toks[pos] not in (')', '⟹'):
            args.append(atom())
        return ('app', a, tuple(args)) if args else a
    def implication():
        nonlocal pos
        a = application()
        if pos < len(toks) and toks[pos] == '⟹':
            pos += 1
            return ('imp', a, implication())
        return a
    result = implication()
    assert pos == len(toks)
    return result


def definitions(source):
    source = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
    found = list(re.finditer(r'^(?:private )?def (\w+)\b', source, re.M))
    defs = {}
    for j, m in enumerate(found):
        name = m.group(1)
        if name == 's':
            break
        piece = source[m.end():found[j+1].start() if j+1 < len(found) else len(source)]
        head, body = piece.split(':=', 1)
        params = []
        for q in re.finditer(r'\(([\w\s]+)\s*:\s*A\)', head):
            params += q.group(1).split()
        defs[name] = (params, parse_expression(body.strip()))
    assert 'exchange' in defs
    return defs


def check(source):
    defs = definitions(source)
    terms = [['v', 'a'], ['v', 'b'], ['v', 'c']]
    term_ids = {tuple(t):i for i,t in enumerate(terms)}
    proofs = []
    proof_ids = {}
    def imp(a,b):
        t = ('i', a, b)
        if t not in term_ids:
            term_ids[t] = len(terms); terms.append(list(t))
        return term_ids[t]
    @functools.lru_cache(None)
    def subterm(a,b):
        return a == b or (terms[b][0] == 'i' and
               (subterm(a,terms[b][1]) or subterm(a,terms[b][2])))
    def put(proof):
        key = tuple(proof)
        if key not in proof_ids:
            proof_ids[key] = len(proofs); proofs.append(proof)
        return proof_ids[key]
    def row(a,b,c,u):
        assert subterm(u,a), ('unproved domination', a,u)
        conclusion = imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
        return put(['row',conclusion,a,b,c,u])
    def mp(major,minor):
        mm,nn = proofs[major][1],proofs[minor][1]
        assert terms[mm][0] == 'i' and terms[mm][1] == nn, ('bad MP',major,minor)
        return put(['mp',terms[mm][2],major,minor])
    def term(e,env):
        if e[0] == 'name': return env[e[1]]
        assert e[0] == 'imp', e
        return imp(term(e[1],env),term(e[2],env))
    def proof(e,env):
        assert e[0] == 'app' and e[1][0] == 'name', e
        name,args = e[1][1],e[2]
        if name == 'rules.row':
            assert len(args) == 5
            return row(*(term(a,env) for a in args[:4]))
        if name == 'rules.mp':
            assert len(args) == 2
            return mp(proof(args[0],env),proof(args[1],env))
        assert name in defs and args[0] == ('name','rules'), name
        n = len(defs[name][0])
        assert len(args) in (n+1,n+2), (name,len(args),n)
        return instantiate(name, tuple(term(a,env) for a in args[1:n+1]))
    @functools.lru_cache(None)
    def instantiate(name,args):
        params,body = defs[name]
        assert len(params) == len(args)
        return proof(body,dict(zip(params,args)))
    final = instantiate('exchange',(0,1,2))
    want = imp(imp(0,imp(1,2)),imp(1,imp(0,2)))
    assert proofs[final][1] == want
    # Second pass over data only: no Lean parser or definition evaluator.
    for i,p in enumerate(proofs):
        if p[0] == 'row':
            _,con,a,b,c,u = p
            assert subterm(u,a)
            assert con == imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
        else:
            _,con,major,minor = p
            assert major < i and minor < i
            f,g = proofs[major][1],proofs[minor][1]
            assert terms[f] == ['i',g,con]
    return {'format':'dominated-rho8-exchange-DAG-v1','terms':terms,'proofs':proofs,
            'final':final,'variables':['a','b','c'],
            'bound_rule':'u is a syntactic subterm of the first rho8 parameter',
            'conclusion':'(a -> (b -> c)) -> (b -> (a -> c))'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    cert=check(a.source.read_text())
    a.out.mkdir(parents=True,exist_ok=True)
    data=(json.dumps(cert,separators=(',',':'))+'\n').encode()
    (a.out/'restricted_exchange_certificate.json').write_bytes(data)
    receipt={'status':'PASS','terms':len(cert['terms']),'proof_rows':len(cert['proofs']),
             'rho8_leaves':sum(p[0]=='row' for p in cert['proofs']),
             'modus_ponens_nodes':sum(p[0]=='mp' for p in cert['proofs']),
             'source_sha256':hashlib.sha256(a.source.read_bytes()).hexdigest(),
             'certificate_sha256':hashlib.sha256(data).hexdigest(),
             'uses_K_or_S_as_axioms':False,'all_domination_side_conditions_checked':True,
             'kernel_checked':False}
    (a.out/'restricted_exchange_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__': main()
