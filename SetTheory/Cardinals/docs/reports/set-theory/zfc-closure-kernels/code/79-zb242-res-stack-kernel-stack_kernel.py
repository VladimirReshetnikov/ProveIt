#!/usr/bin/env python3
"""Environment-stack finite EPSC kernel and an explicit equational packet.

New frontend built for the ProveIt sub-243 investigation (2026-10-18).
The raw EPSC schema and shared exclusive-branch Skolems are inherited from
ProveIt source 40.  The packet format and Boolean basis follow source 70;
this file independently implements serialization and truth-table checking.
No binary Turing machine or proof-assistant theorem is asserted here.
"""
from __future__ import annotations

if not __debug__:
    raise SystemExit("Verification requires Python assertions; rerun without -O or -OO.")
import argparse
import itertools
import json
from pathlib import Path

D = ('d',)
TOP = ('top',)

def t(f, *args): return (f, *args)
def nodes(x): return 1 if isinstance(x, str) else 1 + sum(nodes(a) for a in x[1:])
def variables(x):
    if isinstance(x, str): return {x}
    return set().union(*(variables(a) for a in x[1:])) if len(x) > 1 else set()
def pretty(x):
    if isinstance(x, str): return x
    return x[0] if len(x) == 1 else x[0]+'('+','.join(pretty(a) for a in x[1:])+')'
def B(a, b): return t('N', a, b)
def neg(a): return B(TOP, a)
def meet(a, b): return neg(B(a, b))
def atom(lit): return t('p_'+lit[1], *lit[2:])
def lit(sign, r, *args): return (sign, r, *args)
def canonical(eq):
    names = sorted(variables(eq[0]) | variables(eq[1]))
    rename = {x: 'v'+str(i) for i,x in enumerate(names)}
    def go(x): return rename[x] if isinstance(x,str) else (x[0], *(go(a) for a in x[1:]))
    return go(eq[0]), go(eq[1])

def build(derived_pick=False):
    v = lambda s,i: t('V',s,i)
    p = lambda x,s: t('P',x,s)
    a = lambda i,j: t('A',i,j)
    n = lambda x,y: t('J',x,y)
    q = lambda x: t('Q',x)
    w = lambda s,c: t('W',s,c)
    rho = lambda sign,x,y: lit(sign,'eps',p(y,p(x,'b')),v('b',D))
    target = t('Target','b')
    nxt = lambda z: t('Next','b',z)
    member = lambda z: t('Mem','b',z)
    pick = lambda x: w(p(x,D),a(D,a(D,D))) if derived_pick else t('Pick',x)
    native = [
        (v(p('x','s'),D),'x'),
        (v(p('x','s'),a('j',D)),v('s','j')),
    ]
    groups = [
      ('class NAND', [
          [lit(False,'eps','s',n('a','b')),lit(False,'eps','s','a'),lit(False,'eps','s','b')],
          [lit(True,'eps','s',n('a','b')),lit(True,'eps','s','a')],
          [lit(True,'eps','s',n('a','b')),lit(True,'eps','s','b')],
      ], (t('p_eps','s',n('a','b')), B(t('p_eps','s','a'),t('p_eps','s','b')))),
      ('atomic membership', [
          [lit(False,'eps','s',a('i','j')),lit(True,'E',v('s','i'),v('s','j'))],
          [lit(True,'eps','s',a('i','j')),lit(False,'E',v('s','i'),v('s','j'))],
      ], (t('p_eps','s',a('i','j')), t('p_E',v('s','i'),v('s','j')))),
    ]
    # Two propositional clauses force an existential value to equal its chosen
    # witness value.  The arbitrary-candidate implication gives completeness.
    selected = t('p_eps',p(w('s','a'),'s'),'a')
    quantified = t('p_eps','s',q('a'))
    groups += [
      ('existential selected witness', [
          [lit(False,'eps','s',q('a')),lit(True,'eps',p(w('s','a'),'s'),'a')],
          [lit(True,'eps','s',q('a')),lit(False,'eps',p(w('s','a'),'s'),'a')],
      ], (quantified, selected)),
      ('existential arbitrary witness', [
          [lit(False,'eps',p('z','s'),'a'),lit(True,'eps','s',q('a'))],
      ], None),
    ]
    bad = [rho(True,target,nxt('z')),lit(True,'E',member('z'),nxt('z')),lit(False,'E',member('z'),'z')]
    hull = [
      [lit(True,'E',pick('x'),'x'),rho(False,'x','y'),lit(True,'E','y',target)],
      [lit(False,'E','x',target),rho(False,'x','y'),lit(True,'E','y',target)],
      [lit(False,'E','y',target),rho(True,nxt('y'),'y')],
    ]
    for index,l in enumerate(bad): groups.append(('closure bad '+str(index+1),[[lit(True,'G','b'),l]],None))
    for index,cl in enumerate(hull): groups.append(('closure hull '+str(index+1),[[lit(False,'G','b'),*cl]],None))
    for index,(label, clauses, eq) in enumerate(groups):
        if eq is None:
            assert len(clauses)==1
            # Clause truth is the complement of the conjunction of falsifying
            # values.  Each potentially large predicate atom is printed once.
            falsifying = [neg(atom(l)) if l[0] else atom(l) for l in clauses[0]]
            if len(falsifying)==1: eq=(falsifying[0],neg(TOP))
            else:
                rhs=falsifying[-1]
                for val in reversed(falsifying[1:-1]): rhs=meet(val,rhs)
                eq=(TOP,B(falsifying[0],rhs))
        groups[index]=(label,clauses,eq)
    sheffer = (B(B('x',B(B('y','x'),'x')),B('y',B('z','x'))),'y')
    truth = (TOP,B(D,B(D,D)))
    equations=[sheffer,truth,*native,*[eq for _,_,eq in groups]]
    signature={}
    def visit(x):
        if isinstance(x,str):return
        old=signature.setdefault(x[0],len(x)-1)
        assert old==len(x)-1
        for c in x[1:]: visit(c)
    for eq in equations:
        for side in eq:visit(side)
    # Stable explicit declaration order is serialized, including all arities.
    order=['d','top','N','V','P','A','J','Q','W','Target','Next','Mem','Pick','p_E','p_eps','p_G']
    signature={s:signature[s] for s in order if s in signature}
    return {'name':'stack_epsc_derived_pick' if derived_pick else 'stack_epsc_explicit_pick',
            'native_equations':native,'groups':groups,'equations':equations,
            'signature':signature,'start':B(TOP,TOP),'target':TOP}

def check_boolean_group(clauses, eq):
    ats=sorted({atom(l) for c in clauses for l in c},key=repr)
    checked=0
    for bits in itertools.product((False,True),repeat=len(ats)):
        assignment=dict(zip(ats,bits))
        def value(x):
            if x==TOP:return True
            if x in assignment:return assignment[x]
            assert x[0]=='N'
            return not(value(x[1]) and value(x[2]))
        lhs=all(any(assignment[atom(l)]==l[0] for l in c) for c in clauses)
        rhs=value(eq[0])==value(eq[1])
        assert lhs==rhs,(clauses,eq,bits)
        checked+=1
    return checked

def encode(data):
    eqs=list(map(canonical,data['equations']))
    cap=max(len(variables(a)|variables(b)) for a,b in eqs)
    syms=list(data['signature'])
    width=max(1,(cap+len(syms)-1).bit_length())
    def prefix(x):
        if isinstance(x,str):return format(int(x[1:]),f'0{width}b')
        return format(cap+syms.index(x[0]),f'0{width}b')+''.join(prefix(a) for a in x[1:])
    header=format(len(syms),'08b')+''.join(format(data['signature'][s],'03b') for s in syms)+format(cap,'08b')
    rules=''.join('1'+prefix(a)+prefix(b) for a,b in eqs)+'0'
    endpoints=prefix(data['start'])+prefix(data['target'])
    bits=header+rules+endpoints
    return bits,{'signature_symbols':len(syms),'variable_capacity':cap,'opcode_width':width,
       'header_bits':len(header),'equation_bits':len(rules),'endpoint_bits':len(endpoints),
       'complete_packet_bits':len(bits),'equations':len(eqs),'both_side_tree_nodes':sum(nodes(x) for e in eqs for x in e)}

def decode(bits):
    pos=0
    def read(n):
        nonlocal pos
        if pos+n>len(bits):raise ValueError('truncated packet')
        s=bits[pos:pos+n];pos+=n
        if any(c not in '01' for c in s):raise ValueError('nonbinary packet')
        return int(s,2)
    count=read(8);arities=[read(3) for _ in range(count)];cap=read(8)
    width=max(1,(count+cap-1).bit_length())
    def term():
        tag=read(width)
        if tag<cap:return 'v'+str(tag)
        if tag>=cap+count:raise ValueError('invalid tag')
        return (tag-cap,*(term() for _ in range(arities[tag-cap])))
    eqs=[]
    while read(1):eqs.append((term(),term()))
    start,target=term(),term()
    if pos!=len(bits):raise ValueError('trailing data')
    if variables(start)|variables(target):raise ValueError('nonground endpoint')
    return arities,cap,eqs,start,target

def verify_stack():
    # This is a finite induction-rule regression, not a finite model of EPSC.
    # A(i,d) realizes successor in the distinguished numeral family.
    def numeral(n):
        ans=D
        for _ in range(n):ans=t('A',ans,D)
        return ans
    def environment(vals,base=('opaque',)): 
        s=base
        for v in reversed(vals):s=t('P',v,s)
        return s
    def rewrite_lookup(s,i):
        if s[0]!='P':return t('V',s,i)
        if i==D:return s[1]
        if isinstance(i,tuple) and i[0]=='A' and i[2]==D:return rewrite_lookup(s[2],i[1])
        return t('V',s,i)
    checks=0
    for n in range(1,65):
        xs=tuple('x'+str(i) for i in range(n))
        env=environment(xs)
        for i,x in enumerate(xs):
            assert rewrite_lookup(env,numeral(i))==x;checks+=1
    return checks

def verify_reification():
    # Finite-carrier formula-semantics regression, NOT a model of the one-sorted
    # kernel.  The formula language and class syntax are compared independently.
    import random
    rng=random.Random(1169)
    free_slots=(1,0,3,4)  # x,y,p1,p2; descriptor code occupies unused slot 2.
    def numeral(i):
        ans=D
        for _ in range(i):ans=t('A',ans,D)
        return ans
    def generate(fuel,depth):
        if fuel==0 or rng.randrange(4)==0:
            return ('rel',rng.randrange(depth+4),rng.randrange(depth+4))
        if rng.randrange(2):return ('nand',generate(fuel-1,depth),generate(fuel-1,depth))
        return ('exists',generate(fuel-1,depth+1))
    def compile_formula(f,depth=0):
        if f[0]=='rel':
            def slot(i):return i if i<depth else free_slots[i-depth]+depth
            return t('A',numeral(slot(f[1])),numeral(slot(f[2])))
        if f[0]=='nand':return t('J',compile_formula(f[1],depth),compile_formula(f[2],depth))
        return t('Q',compile_formula(f[1],depth+1))
    def direct(f,env,relation):
        if f[0]=='rel':return (env[f[1]],env[f[2]]) in relation
        if f[0]=='nand':return not(direct(f[1],env,relation) and direct(f[2],env,relation))
        return any(direct(f[1],(z,*env),relation) for z in range(2))
    def lookup(s,i):
        while i!=D:
            assert s[0]=='P' and i[0]=='A' and i[2]==D
            s=s[2];i=i[1]
        assert s[0]=='P'
        return s[1]
    def incidence(s,c,relation):
        if c[0]=='A':return (lookup(s,c[1]),lookup(s,c[2])) in relation
        if c[0]=='J':return not(incidence(s,c[1],relation) and incidence(s,c[2],relation))
        assert c[0]=='Q'
        return any(incidence(t('P',z,s),c[1],relation) for z in range(2))
    formulas=[generate(3,0) for _ in range(64)]
    checks=0
    for mask in range(16):
        relation={(x,y) for x in range(2) for y in range(2) if mask>>(2*x+y)&1}
        for f in formulas:
            c=compile_formula(f)
            for x,y,p1,p2 in itertools.product(range(2),repeat=4):
                b=t('P',c,t('P',p1,t('P',p2,D)))
                env=t('P',y,t('P',x,b))
                code=lookup(b,D)
                assert incidence(env,code,relation)==direct(f,(x,y,p1,p2),relation)
                checks+=1
    return checks

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'generated')
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    summary={'status':'ordinary finite frontend; no binary machine and no kernel-checked calibration',
             'stack_projection_regressions':verify_stack(),'formula_reification_regressions':verify_reification(),'variants':[]}
    for derived in (False,True):
        data=build(derived);truth_checks=sum(check_boolean_group(cs,eq) for _,cs,eq in data['groups'])
        bits,metrics=encode(data);decoded=decode(bits)
        def erase(x):return x if isinstance(x,str) else (list(data['signature']).index(x[0]),*(erase(a) for a in x[1:]))
        assert decoded==(list(data['signature'].values()),metrics['variable_capacity'],
                         [tuple(map(erase,canonical(e))) for e in data['equations']],erase(data['start']),erase(data['target']))
        for bad in (bits[:-1],bits+'0'):
            try:decode(bad)
            except ValueError:pass
            else:raise AssertionError('malformed packet accepted')
        data['metrics']=metrics;data['boolean_truth_table_rows']=truth_checks
        (args.out/(data['name']+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        (args.out/(data['name']+'.bits')).write_text(bits+'\n')
        (args.out/(data['name']+'.equations')).write_text('\n'.join(f'{i:02}: {pretty(a)} = {pretty(b)}' for i,(a,b) in enumerate(data['equations']))+'\n')
        summary['variants'].append({'name':data['name'],'boolean_truth_table_rows':truth_checks,**metrics})
    (args.out/'verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
