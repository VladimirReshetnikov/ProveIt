#!/usr/bin/env python3
"""FC15/FC17 finite clause payload and arithmetic Herbrand reference.

This is a reference specification, not a binary Turing-machine compiler.
The practical solver uses sparse atom names and DPLL. The report also gives
the equivalent, much slower integer-bit valuation algorithm.
All source equality is translated to an explicit congruence predicate.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import json
from math import isqrt
from pathlib import Path

FUNCS = [('V',2),('C',3),('N',2),('A',2),('Q',2),('W',3),
         ('Y',3),('Z',3),('H',2),('D',1)]
PREDICATES = ['E','Inc','G','Eq']
RADIX = 16

def pair(a: int, b: int) -> int:
    return (a+b)*(a+b+1)//2+b

def unpair(n: int) -> tuple[int,int]:
    w=(isqrt(8*n+1)-1)//2
    b=n-w*(w+1)//2
    return w-b,b

def tuple_code(xs) -> int:
    if len(xs)==1:
        return xs[0]
    return pair(xs[0],tuple_code(xs[1:]))

def tuple_decode(n: int, k: int) -> tuple[int,...]:
    if k==1:
        return (n,)
    a,b=unpair(n)
    return (a,)+tuple_decode(b,k-1)

def signature(extensional=False,member_witness=False):
    return [(f,k) for f,k in FUNCS if not (member_witness and f=='D')] + ([('X',2)] if extensional else [])

def construct(tag: int, args) -> int:
    return 1+tag+RADIX*tuple_code(tuple(args))

def decode(n: int, extensional=False,member_witness=False):
    """Bijection from N to ground terms in the padded 16-constructor signature."""
    if n==0:
        return ('d',)
    fs=signature(extensional,member_witness)
    tag,payload=(n-1)%RADIX,(n-1)//RADIX
    name,k=fs[tag] if tag<len(fs) else ('junk'+str(tag),1)
    return (name,)+tuple(decode(x,extensional,member_witness) for x in tuple_decode(payload,k))

def encode(tree, extensional=False,member_witness=False):
    if tree==('d',):
        return 0
    fs=signature(extensional,member_witness)
    tags={n:i for i,(n,k) in enumerate(fs)}
    name=tree[0]
    tag=tags[name] if name in tags else int(name[4:])
    return construct(tag,[encode(x,extensional,member_witness) for x in tree[1:]])

def f(name,*args):
    return (name,)+args

d=('d',)
q=f('N',d,d)

def lit(sign,pred,a,b):
    return (bool(sign),pred,a,b)

def E(a,b,sign=True):
    return lit(sign,'E',a,b)

def I(a,b,sign=True):
    return lit(sign,'Inc',a,b)

def G(a,b,sign=True):
    return lit(sign,'G',a,b)

def Eq(a,b,sign=True):
    return lit(sign,'Eq',a,b)

def R(b,t,x,y,sign=True):
    return I(f('C',f('C',b,d,x),q,y),t,sign)

def source_clauses(extensional=False,member_witness=False):
    s,j,z,k,a,b,t,x,y,u='s j z k a b t x y u'.split()
    n=f('N',a,b)
    atom=f('A',j,k)
    h=f('H',b,t)
    clauses=[
      [Eq(f('V',f('C',s,j,z),j),z)],
      [Eq(k,j),Eq(f('V',f('C',s,j,z),k),f('V',s,k))],
      [I(s,n),I(s,a)],
      [I(s,n),I(s,b)],
      [I(s,n,False),I(s,a,False),I(s,b,False)],
      [I(s,atom,False),E(f('V',s,j),f('V',s,k))],
      [I(s,atom),E(f('V',s,j),f('V',s,k),False)],
      [I(f('C',s,j,z),a,False),I(s,f('Q',j,a))],
      [I(s,f('Q',j,a),False),I(f('C',s,j,f('W',s,j,a)),a)],
      [G(b,t),R(b,t,h,f('Y',b,t,u))],
      [G(b,t),E(f('Z',b,t,u),f('Y',b,t,u))],
      [G(b,t),E(f('Z',b,t,u),u,False)],
      [G(b,t,False),E(x,h,False),R(b,t,x,y,False),E(y,h)],
      [G(b,t,False),E(f('D',x),x),R(b,t,x,y,False),E(y,h)],
      [G(b,t,False),E(y,h,False),R(b,t,f('Y',b,t,y),y)],
    ]
    if member_witness:
        def replace(term):
            if isinstance(term,str) or term==d:
                return term
            if term[0]=='D':
                return f('W',f('C',d,q,term[1]),d,f('A',d,q))
            return (term[0],)+tuple(replace(t) for t in term[1:])
        clauses=[[(sign,pred,replace(a),replace(b)) for sign,pred,a,b in c] for c in clauses]
    if extensional:
        witness=f('X',a,b)
        clauses += [[Eq(a,b),E(witness,a),E(witness,b)],
                    [Eq(a,b),E(witness,a,False),E(witness,b,False)]]
    return clauses

def equality_clauses(extensional=False,functions=None):
    """Quotient only the retained-language reduct; no junk congruence needed."""
    clauses=[[Eq('x','x')],
             [Eq('x','y',False),Eq('x','z',False),Eq('y','z')]]
    for name,k in (signature(extensional) if functions is None else functions):
        xs=tuple('x'+str(i) for i in range(k))
        ys=tuple('y'+str(i) for i in range(k))
        clauses.append([Eq(x,y,False) for x,y in zip(xs,ys)]+
                       [Eq(f(name,*xs),f(name,*ys))])
    for pred in PREDICATES[:-1]:
        clauses.append([Eq('x0','y0',False),Eq('x1','y1',False),
                        lit(False,pred,'x0','x1'),lit(True,pred,'y0','y1')])
    return clauses

def variables(tree):
    if isinstance(tree,str):
        return {tree}
    return set().union(*(variables(x) for x in tree[1:])) if len(tree)>1 else set()

def clause_variables(clause):
    return sorted(set().union(*(variables(x) for l in clause for x in l[2:])))

def ground_term(tree,env,extensional=False,member_witness=False):
    if isinstance(tree,str):
        return env[tree]
    if tree[0]=='d':
        return 0
    tags={name:i for i,(name,k) in enumerate(signature(extensional,member_witness))}
    return construct(tags[tree[0]],[ground_term(x,env,extensional,member_witness) for x in tree[1:]])

def atom_code(pred,a,b):
    return PREDICATES.index(pred)+4*pair(a,b)

def ground_clause(clause,env,extensional=False,member_witness=False):
    return tuple((1 if sign else -1)*(1+atom_code(pred,
          ground_term(a,env,extensional,member_witness),ground_term(b,env,extensional,member_witness)))
          for sign,pred,a,b in clause)

def instances(clauses,bound,extensional=False,member_witness=False):
    """All local variables take every value 0..bound; collisions are included."""
    for clause in clauses:
        vs=clause_variables(clause)
        for vals in product(range(bound+1),repeat=len(vs)):
            yield ground_clause(clause,dict(zip(vs,vals)),extensional,member_witness)

def normalize(cnf):
    out=set()
    for clause in cnf:
        c=frozenset(clause)
        if any(-l in c for l in c):
            continue
        out.add(c)
    return tuple(sorted(out,key=lambda c:(len(c),tuple(sorted(c)))))

def simplify(cnf,literal):
    return tuple(c-{ -literal } for c in cnf if literal not in c)

def solve(cnf):
    """Exact iterative DPLL. Return a satisfying partial valuation or None.

    Unassigned atoms may be set false. Every input clause is independently
    reevaluated before a SAT result is returned by the command-line runner.
    """
    pending=[(normalize(cnf),{})]
    while pending:
        work,assignment=pending.pop()
        while True:
            if not work:
                return assignment
            if any(not c for c in work):
                break
            unit=next((next(iter(c)) for c in work if len(c)==1),None)
            if unit is not None:
                assignment[abs(unit)]=unit>0
                work=simplify(work,unit)
                continue
            signs=set().union(*work)
            pure=next((l for l in sorted(signs,key=lambda x:(abs(x),x)) if -l not in signs),None)
            if pure is not None:
                assignment[abs(pure)]=pure>0
                work=simplify(work,pure)
                continue
            shortest=min(work,key=lambda c:(len(c),tuple(sorted(c))))
            literal=min(shortest,key=lambda x:(abs(x),x))
            other=dict(assignment)
            other[abs(literal)]=literal<0
            pending.append((simplify(work,-literal),other))
            assignment[abs(literal)]=literal>0
            work=simplify(work,literal)
    return None

def valuation_satisfies(cnf,valuation):
    return all(any(valuation.get(abs(l),False)==(l>0) for l in c) for c in cnf)

def exhaustive_sat(cnf):
    atoms=sorted({abs(l) for c in cnf for l in c})
    for values in product((False,True),repeat=len(atoms)):
        a=dict(zip(atoms,values))
        if valuation_satisfies(cnf,a):
            return a
    return None

def term_nodes(tree):
    return 1 if isinstance(tree,str) else 1+sum(term_nodes(x) for x in tree[1:])

def term_depth(tree):
    return 0 if isinstance(tree,str) or len(tree)==1 else 1+max(term_depth(x) for x in tree[1:])

def payload_bits(clauses,extensional=False,functions=None):
    """Static prefix template stream, with 4- or 5-bit term opcodes.

    Clause length:3 bits, zero terminates. Literal sign:1 bit, predicate:2.
    Terms: variables0..5, d=6, retained constructor i=7+i, known arities.
    The length and constructor code are data costs, not TM state estimates.
    """
    fs=signature(extensional) if functions is None else functions
    width=(6+len(fs)).bit_length()
    tags={name:7+i for i,(name,k) in enumerate(fs)}
    out=''
    for clause in clauses:
        vs={v:i for i,v in enumerate(clause_variables(clause))}
        if len(vs)>6 or not 1<=len(clause)<=7:
            raise ValueError('template exceeds format')
        def term(t):
            if isinstance(t,str):
                return format(vs[t],'0'+str(width)+'b')
            opcode=6 if t[0]=='d' else tags[t[0]]
            return format(opcode,'0'+str(width)+'b')+''.join(term(x) for x in t[1:])
        out+=format(len(clause),'03b')
        for sign,pred,a,b in clause:
            out+=str(int(sign))+format(PREDICATES.index(pred),'02b')+term(a)+term(b)
    return out+'000'

def unpack_payload(bits,extensional=False,member_witness=False):
    fs=signature(extensional,member_witness)
    width=(6+len(fs)).bit_length()
    cursor=0
    def read(n):
        nonlocal cursor
        if cursor+n>len(bits):
            raise ValueError('truncated template')
        v=int(bits[cursor:cursor+n],2)
        cursor+=n
        return v
    def term():
        op=read(width)
        if op<6:
            return 'v'+str(op)
        if op==6:
            return d
        if op-7>=len(fs):
            raise ValueError('undefined template constructor')
        name,k=fs[op-7]
        return f(name,*(term() for _ in range(k)))
    clauses=[]
    while True:
        n=read(3)
        if n==0:
            if cursor!=len(bits):
                raise ValueError('trailing template bits')
            return clauses
        c=[]
        for _ in range(n):
            sign,pred=bool(read(1)),PREDICATES[read(2)]
            c.append(lit(sign,pred,term(),term()))
        clauses.append(c)

def metrics(clauses,extensional=False,functions=None):
    return {'clauses':len(clauses),'literals':sum(map(len,clauses)),
        'max_variables':max(map(lambda c:len(clause_variables(c)),clauses)),
        'term_nodes':sum(term_nodes(x) for c in clauses for l in c for x in l[2:]),
        'max_term_depth':max(term_depth(x) for c in clauses for l in c for x in l[2:]),
        'template_bits':len(payload_bits(clauses,extensional,functions)),
        'term_opcode_bits':(6+len(signature(extensional) if functions is None else functions)).bit_length(),
        'clause_lengths':dict(sorted(Counter(map(len,clauses)).items()))}

def generate(output):
    output=Path(output)
    output.mkdir(parents=True,exist_ok=True)
    report={}
    for ext,name in [(False,'fc15'),(True,'fc17')]:
        native=source_clauses(ext)
        full=native+equality_clauses(ext)
        report[name]={'native':metrics(native,ext),'equality_free':metrics(full,ext),
                      'functions':signature(ext),'predicates':PREDICATES,
                      'term_radix':RADIX,'padding_constructors':RADIX-len(signature(ext))}
        for suffix,cs in [('native',native),('equality_free',full)]:
            stem=output/(name+'_'+suffix)
            stem.with_suffix('.json').write_text(json.dumps(cs,indent=2)+'\n')
            bits=payload_bits(cs,ext)
            stem.with_suffix('.bits').write_text(bits+'\n')
            stem.with_suffix('.bin').write_bytes(int(bits.ljust((len(bits)+7)//8*8,'0'),2).to_bytes((len(bits)+7)//8,'big'))
        derived_functions=signature(ext,True)
        derived=source_clauses(ext,member_witness=True)
        derived_full=derived+equality_clauses(ext,derived_functions)
        report[name]['derived_member_variant']={
            'native':metrics(derived,ext,derived_functions),
            'equality_free':metrics(derived_full,ext,derived_functions),
            'functions':derived_functions,
            'scope':'exact logical variant; use --derived-member for stage engine'}
        (output/(name+'_derived_member.json')).write_text(json.dumps(derived_full,indent=2)+'\n')
        bits=payload_bits(derived_full,ext,derived_functions)
        (output/(name+'_derived_member.bits')).write_text(bits+'\n')
        (output/(name+'_derived_member.bin')).write_bytes(int(bits.ljust((len(bits)+7)//8*8,'0'),2).to_bytes((len(bits)+7)//8,'big'))
    (output/'kernel_metrics.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--generate',type=Path)
    p.add_argument('--stage',type=int)
    p.add_argument('--extensional',action='store_true')
    p.add_argument('--derived-member',action='store_true',help='use the recommended nine-function FC15* kernel')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    if args.generate:
        result=generate(args.generate)
    elif args.stage is not None:
        if args.stage<0:
            p.error('stage must be nonnegative')
        fs=signature(args.extensional,args.derived_member)
        cs=source_clauses(args.extensional,args.derived_member)+equality_clauses(args.extensional,fs)
        cnf=list(instances(cs,args.stage,args.extensional,args.derived_member))
        valuation=solve(cnf)
        if valuation is not None and not valuation_satisfies(cnf,valuation):
            raise RuntimeError('solver returned invalid assignment')
        result={'stage':args.stage,'extensional':args.extensional,'derived_member':args.derived_member,
            'ground_instances':len(cnf),'distinct_atoms':len({abs(l) for c in cnf for l in c}),
            'max_atom_code_bits':max(abs(l).bit_length() for c in cnf for l in c),
            'satisfiable':valuation is not None,
            'scope':'one finite ground stage, not a model or consistency proof'}
    else:
        p.error('select --generate or --stage')
    text=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':
    main()
