#!/usr/bin/env python3
"""A complete self-delimiting binary format for finite universal clauses.

This measures fixed input data, not Turing-machine states. Symbols are
anonymous; all function/predicate arities and the equality-predicate index
are stored in the header. Variables are local to each universally closed
clause and renamed by first occurrence. Unused high term/predicate codes
are rejected. The header uses Elias gamma positive integers.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

from ground_resolution import freeze, thaw, variables, validate_clause, parse_clause

MAGIC = '11000101'


def gamma(n):
    if n < 1:
        raise ValueError('Gamma codes require positive integers')
    b = bin(n)[2:]
    return '0'*(len(b)-1)+b


def width(n):
    return (n-1).bit_length() if n>1 else 0


def fixed(n,bits):
    if n<0 or n>=2**bits:
        raise ValueError('Field outside range')
    return format(n,f'0{bits}b') if bits else ''


def ordered_variables(clause):
    out=[]
    def visit(t):
        if isinstance(t,str):
            if t not in out:
                out.append(t)
        else:
            for a in t[1:]:
                visit(a)
    for l in clause['literals']:
        for t in l['args']:
            visit(t)
    return out


def encode(kernel):
    fs,ps=kernel['functions'],kernel['predicates']
    if not fs or not ps:
        raise ValueError('At least one function and predicate are required')
    if any(type(n) is not int or n<0 for n in [*fs.values(),*ps.values()]):
        raise ValueError('Invalid arity')
    fn,pn=list(fs),list(ps)
    rows=kernel['clauses']
    for row in rows:
        validate_clause(parse_clause(row['literals']),fs,ps)
    nv=max(1,max((len(ordered_variables(c)) for c in rows),default=0))
    ma=max([*fs.values(),*ps.values()])
    tw,pw,aw=width(nv+len(fn)),width(len(pn)),width(ma+1)
    eqindex=pn.index('eq')+1 if 'eq' in pn else 0
    if eqindex and ps['eq']!=2:
        raise ValueError('Equality must be binary')
    header=MAGIC+''.join(gamma(v) for v in (nv,len(fn),len(pn),len(rows)+1,ma+1))
    header+=fixed(eqindex,width(len(pn)+1))
    header+=''.join(fixed(a,aw) for a in [*fs.values(),*ps.values()])
    bits=header
    literal_count=term_count=length_bits=0
    for row in rows:
        varmap={v:i for i,v in enumerate(ordered_variables(row))}
        def term(t):
            nonlocal term_count
            term_count+=1
            if isinstance(t,str):
                return fixed(varmap[t],tw)
            return fixed(nv+fn.index(t[0]),tw)+''.join(term(a) for a in t[1:])
        b=gamma(len(row['literals'])+1)
        bits+=b
        length_bits+=len(b)
        for l in row['literals']:
            literal_count+=1
            bits+=str(int(l['positive']))+fixed(pn.index(l['predicate']),pw)
            bits+=''.join(term(t) for t in l['args'])
    padding=(-len(bits))%8
    padded=bits+'0'*padding
    # This format deliberately bounds declared header quantities by file
    # length, including unused arities. Match the decoder's allocation guard.
    if any(n>len(padded) for n in (nv,len(fn),len(pn),len(rows),ma)):
        raise ValueError('Header quantity exceeds this format\'s file-length bound')
    raw=bytes(int(padded[i:i+8],2) for i in range(0,len(padded),8))
    return raw,{'format':'FCK-clause-v1','meaningful_bits':len(bits),'storage_bytes':len(raw),
        'padding_bits':padding,'header_bits':len(header),'clause_length_bits':length_bits,
        'literal_fields_bits':literal_count*(1+pw),'term_fields_bits':term_count*tw,
        'term_token_width':tw,'term_node_occurrences':term_count,
        'literal_occurrences':literal_count,'variable_slots':nv,
        'function_symbols_including_constants':len(fn),'predicate_symbols_including_equality':len(pn),
        'maximum_arity':ma,'clauses':len(rows),'sha256':hashlib.sha256(raw).hexdigest()}


def decode(raw):
    bits=''.join(f'{b:08b}' for b in raw)
    pos=0
    def take(n):
        nonlocal pos
        if n<0 or pos+n>len(bits):
            raise ValueError('Truncated code')
        r=bits[pos:pos+n]
        pos+=n
        return int(r,2) if r else 0
    def readgamma():
        n=0
        while take(1)==0:
            n+=1
        return (1<<n)+take(n)
    if take(8)!=int(MAGIC,2):
        raise ValueError('Wrong magic/version')
    nv,nf,np,nc,ma=[readgamma() for _ in range(5)]
    nc-=1
    ma-=1
    # The format bounds these quantities by file length. In particular an
    # unused symbol of enormous declared arity is intentionally not accepted.
    if any(n>len(bits) for n in (nv,nf,np,nc,ma)):
        raise ValueError('Impossible header for file length')
    eqindex=take(width(np+1))
    if eqindex>np:
        raise ValueError('Unknown equality predicate')
    aw=width(ma+1)
    arities=[take(aw) for _ in range(nf+np)]
    if any(a>ma for a in arities):
        raise ValueError('Invalid arity code')
    fns=[f'f{i}' for i in range(nf)]
    pns=['eq' if i+1==eqindex else f'r{i}' for i in range(np)]
    fs=dict(zip(fns,arities[:nf]));ps=dict(zip(pns,arities[nf:]))
    if eqindex and ps['eq']!=2:
        raise ValueError('Nonbinary equality')
    tw,pw=width(nv+nf),width(np)
    def term():
        tag=take(tw)
        if tag<nv:
            return '?v'+str(tag)
        tag-=nv
        if tag>=nf:
            raise ValueError('Unknown term token')
        return [fns[tag],*(term() for _ in range(arities[tag]))]
    rows=[]
    for c in range(nc):
        n=readgamma()-1
        if n>len(bits):
            raise ValueError('Impossible literal count')
        ls=[]
        for _ in range(n):
            sign=bool(take(1));p=take(pw)
            if p>=np:
                raise ValueError('Unknown predicate token')
            ls.append({'positive':sign,'predicate':pns[p],
                       'args':[term() for _ in range(arities[nf+p])]})
        rows.append({'name':f'c{c}','literals':ls})
    if len(bits)-pos>=8 or any(x!='0' for x in bits[pos:]):
        raise ValueError('Noncanonical trailing data')
    return {'functions':fs,'predicates':ps,'clauses':rows},pos


def canonical(kernel):
    fs,ps=kernel['functions'],kernel['predicates']
    fm={f:f'f{i}' for i,f in enumerate(fs)}
    pm={p:('eq' if p=='eq' else f'r{i}') for i,p in enumerate(ps)}
    rows=[]
    for i,row in enumerate(kernel['clauses']):
        vm={v:f'?v{k}' for k,v in enumerate(ordered_variables(row))}
        def tr(t):
            return vm[t] if isinstance(t,str) else [fm[t[0]],*(tr(a) for a in t[1:])]
        rows.append({'name':f'c{i}','literals':[{'positive':l['positive'],
            'predicate':pm[l['predicate']],'args':[tr(t) for t in l['args']]} for l in row['literals']]})
    return {'functions':{fm[f]:a for f,a in fs.items()},
            'predicates':{pm[p]:a for p,a in ps.items()},'clauses':rows}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('kernel',type=Path);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();k=json.loads(a.kernel.read_text())
    raw,metrics=encode(k);decoded,n=decode(raw)
    if decoded!=canonical(k) or n!=metrics['meaningful_bits']:
        raise AssertionError('Round-trip failure')
    a.output.write_bytes(raw)
    a.output.with_suffix('.codec.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))


if __name__=='__main__':
    main()
