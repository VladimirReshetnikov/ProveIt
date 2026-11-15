#!/usr/bin/env python3
"""Swap the U/E constructor residues in an AX grammar, with exact free-term checks.

Research experiment only: this script does not certify any literal TM.
The arithmetic operation contracts are those of the attributed AX11H/GDH
source engines.  The evaluator here has no import from their builders.
"""
from pathlib import Path
import argparse, collections, functools, hashlib, json, math

HERE = Path(__file__).resolve().parent
INC = ('leaf', 'inc', 1)
BREAK = ('leaf', 'breakTo', 1)
MACRO = {
    'node49': 'push', 'node55': 'copyD', 'node58': 'copyH',
    'node70': 'copyA', 'node65': 'cons', 'node72': 'readH',
    'node75': 'readDCons', 'node142': 'copyGuard',
    'node150': 'compareGuard', INC: 'incT', BREAK: 'close',
}

def require(ok, message):
    if not ok:
        raise AssertionError(message)

def read_tree(path):
    data = json.loads(Path(path).read_text())
    def visit(x):
        if x == 'node60':
            return (INC, INC)
        if x == 'node61':
            return ((INC, INC), (INC, INC))
        if isinstance(x, str) and x in data['rules']:
            return visit(data['rules'][x])
        if isinstance(x, list):
            return tuple(visit(y) for y in x)
        return x
    return visit(data['root'])

def isnode(t):
    return isinstance(t, tuple) and len(t) == 2

def flatten(t):
    return flatten(t[0]) + flatten(t[1]) if isnode(t) else [t]

def grammar(t):
    ids, rules = {}, {}
    def visit(t):
        if not isnode(t):
            return t
        if t not in ids:
            key = 'g' + str(len(ids))
            ids[t] = key
            rules[key] = [visit(t[0]), visit(t[1])]
        return ids[t]
    root = visit(t)
    return {'root': root, 'rules': rules}

def tagged_runs(w):
    runs = []
    for i, x in enumerate(w):
        if x not in ('node65', 'node75'):
            continue
        j = i + 1
        while j < len(w) and w[j] == INC:
            j += 1
        require(j-i-1 in (0, 1, 2, 3), ('unexpected constructor tail', i, j))
        runs.append((i, j-i-1))
    return runs

def swapped_tree(t, double_index=1, remove_index=2):
    w = flatten(t)
    edits = {}
    for i, tag in tagged_runs(w):
        if tag == 2:
            edits[i + 1 + double_index] = (INC, INC)
        elif tag == 3:
            edits[i + 1 + remove_index] = None
    n = 0
    def visit(t):
        nonlocal n
        if not isnode(t):
            out = edits.get(n, t)
            n += 1
            return out
        a, b = visit(t[0]), visit(t[1])
        if a is None:
            return b
        if b is None:
            return a
        return (a, b)
    result = visit(t)
    expected = []
    i = 0
    while i < len(w):
        x = w[i]
        expected.append(x)
        i += 1
        if x in ('node65', 'node75'):
            j = i
            while j < len(w) and w[j] == INC:
                j += 1
            tag = j-i
            expected.extend([INC] * ({2:3, 3:2}.get(tag, tag)))
            i = j
    require(flatten(result) == expected, 'edited grammar differs from specified word')
    return result

# Exact free arithmetic terms, without constructor-injectivity assumptions.
ZERO = ('zero',)
def succ(t): return ('S', t)
ONE = succ(ZERO)
def add(a,b): return ('+',a,b)
def pair(a,b): return ('p',a,b)
def imp(a,b): return ('I',a,b)
def incs(t,n):
    for _ in range(n): t=succ(t)
    return t
def head(w): return w[1] if w[0]=='p' else ('hd',w)
def tail(w): return w[2] if w[0]=='p' else ('tl',w)
def guard(a,b,t): return ('zero_if_equal',a,b,t)

def evaluate_and_check(w, family, swapped):
    require(family in ('H','GDH'), 'unknown family')
    tag_u, tag_e = (3,2) if swapped else (2,3)
    def mem(a,b): return succ(imp(a,b))
    def all_(a,b): return incs(imp(b,a),tag_u)
    def eq(a,b): return incs(imp(a,b),tag_e)
    def neg(a): return imp(a,ONE)
    def conj(a,b): return neg(imp(a,neg(b)))
    def exists(a,b): return neg(all_(a,neg(b)))
    n,t,w0,a,d,h,x,y,z,l=[('v',k) for k in ('n','t','w','a','d','h','x','y','z','l')]
    r = dict(N=n,T=t,W=w0,A=a,D=d,H=h,X=ZERO,Y=ZERO,L=pair(y,pair(x,pair(z,l))))
    def push():
        r['W']=pair(r['T'],r['W']);r['T']=ZERO
    for i, token in enumerate(w):
        name=MACRO[token]
        if name=='compareGuard':
            require(r['A']==ZERO and r['X']==r['Y'], ('guard inputs',i))
        else:
            require(r['X']==r['Y']==ZERO, ('scratch inputs',i))
        if name=='incT': r['T']=succ(r['T'])
        elif name=='push': push()
        elif name in ('copyA','copyD','copyH'):
            push();r['T']=r[name[-1]]
        elif name=='cons':
            r['T']=imp(head(r['W']),r['T']);r['W']=tail(r['W'])
        elif name=='readH':
            r['H']=add(r['H'],head(r['L']));r['L']=tail(r['L'])
        elif name=='readDCons':
            r['D']=add(r['D'],head(r['L']));r['L']=tail(r['L'])
            r['T']=imp(r['T'],r['D'])
        elif name=='copyGuard':
            r['X']=r['Y']=r['A'];r['A']=ZERO
        elif name=='compareGuard':
            r['T']=guard(r['X'],r['H'],r['T']);r['H']=r['X']=ZERO
            r['X']=r['Y'];r['Y']=ZERO;r['H']=r['D'];r['D']=ZERO
            r['T']=guard(r['X'],r['H'],r['T']);r['H']=r['X']=ZERO
        elif name=='close': pass
        else: raise AssertionError(name)
    D,H=add(d,x),add(h,y)
    hs=[imp(exists(D,all_(D,H)),H),
        imp(all_(D,all_(a,H)),all_(a,all_(D,H))),
        imp(mem(H,D),imp(eq(H,a),mem(a,D))),
        imp(eq(H,D),imp(mem(a,H),mem(a,D))),
        exists(D,eq(H,D)),
        imp(all_(D,a),imp(all_(D,imp(a,H)),all_(D,H)))]
    rho=imp(imp(imp(H,d),D),imp(imp(D,H),imp(a,H)))
    diagonal_argument=D if family=='GDH' else a
    gamma=imp(diagonal_argument,all_(diagonal_argument,diagonal_argument))
    point=imp(a,mem(a,D))
    vac=imp(mem(H,D),all_(a,mem(H,D)))
    sep=all_(D,conj(imp(mem(H,D),point),imp(mem(a,D),a)))
    q=all_(a,imp(sep,neg(point)))
    gate=guard(a,D,guard(a,H,neg(imp(vac,q))))
    gen=all_(a if family=='GDH' else d,h)
    stack=w0
    for item in [t,gen,rho]+hs+[gamma,gate]: stack=pair(item,stack)
    expected=dict(N=n,T=ZERO,W=stack,A=ZERO,D=ZERO,H=ZERO,X=ZERO,Y=ZERO,L=pair(z,l))
    require(r==expected, 'complete free-term AX equation failed')
    return {'status':'PASS','family':family,'U_tag':tag_u,'E_tag':tag_e,
            'all_nine_endpoint_registers':True,'all_scratch_preconditions':True,
            'axiom_entries':11,'actual_fourth_operand_retained':True,
            'failed_guard_top':0,'command_protocol_unchanged':True}

def pair_num(a,b): return (a+b)*(a+b+1)//2+b
def unpair_num(n):
    s=(math.isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b

@functools.cache
def recode(n):
    if n==0:return 0
    tag=n%4
    a,b=unpair_num(n//4)
    require(a<n and b<n,'strict recoding arguments')
    return 4*pair_num(recode(a),recode(b))+{0:0,1:1,2:3,3:2}[tag]

def run(out):
    out.mkdir(parents=True,exist_ok=True)
    result={'scope':'source experiment only; no machine size or consistency theorem asserted by execution',
            'families':[],'finite_recode_checks':10000}
    for family,name in [('H','h_parent.grammar.json'),('GDH','gdh_parent.grammar.json')]:
        original=read_tree(HERE/name);ow=flatten(original)
        base=evaluate_and_check(ow,family,False)
        variants=[]
        for d in range(2):
            for e in range(3):
                child=swapped_tree(original,d,e)
                f=out/(family+'_U3E2_d'+str(d)+'e'+str(e)+'.grammar.json')
                f.write_text(json.dumps(grammar(child),indent=2)+'\n')
                variants.append(f.name)
        nw=flatten(swapped_tree(original))
        algebra=evaluate_and_check(nw,family,True)
        (out/(family+'_U3E2.word.json')).write_text(json.dumps(nw,indent=2)+'\n')
        result['families'].append({'family':family,'old_tokens':len(ow),'new_tokens':len(nw),
             'constructor_tag_counts':dict(collections.Counter(tag for _,tag in tagged_runs(ow))),
             'old_algebra':base,'new_algebra':algebra,'grammar_seeds':variants,
             'source_sha256':hashlib.sha256((HERE/name).read_bytes()).hexdigest()})
    for n in range(10000): require(recode(recode(n))==n, ('involution',n))
    result['recode_first_16']=[recode(n) for n in range(16)]
    (out/'source_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=HERE/'seeds')
    args=p.parse_args();run(args.output)
