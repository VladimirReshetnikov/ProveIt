#!/usr/bin/env python3
"""Verify optional negative-Gamma PA195N using the primary package's inherited baseline.
Usage: python3 verify.py PATH_TO_PA195DC/baseline195
No search is needed. This is an executable certificate, not a kernel theorem.
"""
from pathlib import Path
import hashlib, importlib.util, json, sys
HERE=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit(__doc__)
BASE=Path(sys.argv[1]).resolve()
spec=importlib.util.spec_from_file_location('baseline_verifier',BASE/'build_verify.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
c=b.c;need=b.need;word=b.word;original_blocks=b.original_blocks
need(__debug__,'Run without Python -O')
for name,digest in json.loads((BASE/'vendor_hashes.json').read_text()).items():
 need(hashlib.sha256((BASE/name).read_bytes()).hexdigest()==digest,'vendor hash '+name)

def emitter_new(t):
    """A free-algebra computation, not numeric formula-code sampling."""
    ww = word(t)
    old = [op for op, a, b in original_blocks()]
    expected = old[:121] + ['copyA', 'copyA', 'copyA', 'cons', 'incT', 'incT', 'cons'] + old[138:]
    expected = expected[:121] + ['copyA','push','incT','cons','copyA','push','incT','cons','copyA','cons','incT','incT','cons'] + expected[128:]
    need(ww == expected, 'negative-Gamma emitter word differs')
    ZERO = ('zero',)
    succ = lambda x: ('succ', x)
    ONE = succ(ZERO)
    add = lambda x, y: ('add', x, y)
    I = lambda a, b: ('im', a, b)
    M = lambda a, b: succ(I(a, b))
    U = lambda a, b: succ(succ(I(b, a)))
    E = lambda a, b: succ(succ(succ(I(a, b))))
    N = lambda a: I(a, ONE)
    And = lambda a, b: N(I(a, N(b)))
    Ex = lambda a, b: N(U(a, N(b)))
    oldt, A, d, h, Y, X = [('atom', z) for z in ['t', 'a', 'd', 'h', 'y', 'x']]
    T, D, H, stack, fields = oldt, d, h, [], [Y, X]
    for op in ww[:-3]:
        if op == 'push':
            stack.append(T); T = ZERO
        elif op in ('copyD', 'copyH', 'copyA'):
            stack.append(T); T = {'copyD': D, 'copyH': H, 'copyA': A}[op]
        elif op == 'cons':
            T = I(stack.pop(), T)
        elif op == 'incT':
            T = succ(T)
        elif op == 'readH':
            H = add(H, fields.pop(0))
        elif op == 'readDCons':
            D = add(D, fields.pop(0)); T = I(T, D)
        else:
            raise ValueError(op)
    need(not fields, 'argument reads')
    heads = [I(Ex(D, U(D, H)), H), I(U(D, U(A, H)), U(A, U(D, H))),
             I(M(H, D), I(E(H, A), M(A, D))),
             I(E(H, D), I(M(A, H), M(A, D))), Ex(D, E(H, D)),
             I(U(D, A), I(U(D, I(A, H)), U(D, H)))]
    rho = I(I(I(H, d), D), I(I(D, H), I(A, H)))
    gamma = I(N(A), U(A, N(A)))
    V = I(M(H, D), U(A, M(H, D)))
    B = I(A, M(A, D))
    S = U(D, And(I(M(H, D), B), I(M(A, D), A)))
    Q = U(A, I(S, N(B)))
    need(stack == [oldt, U(d, h), rho] + heads, 'emitted complete stack')
    need(T == N(I(gamma, I(V, Q))), 'emitted gate')
    need(ww[-3:] == ['copyGuard', 'compareGuard', 'close'], 'guard and cleanup')
    return {'macro_tokens': len(ww), 'complete_stack_free_algebra_identity': True,
            'complete_top_free_algebra_identity': True, 'head_parameters_unchanged': True}

tree=c.read_grammar(HERE/'grammar.json')
raw,index,shape=c.build(tree)
folds=json.loads((HERE/'folds.json').read_text())
folded,aliases=b.quotient(raw,folds)
need(folded==b.table(HERE/'machine.native.tm'),'native table')
labels=json.loads((HERE/'labels.json').read_text())
dense=b.table(HERE/'machine.tm')
need(set(dense)=={(q,bit) for q in range(195) for bit in (0,1)},'dense binary domain')
need(len(labels)==196 and labels[0]==74 and labels[-1]==254 and len(set(labels))==196,'labels')
need({(labels[q],bit):(w,d,labels[n]) for (q,bit),(w,d,n) in dense.items()}==folded,'dense conjugacy')
cert=b.quotient_certificate(raw,folded,folds,aliases)
need(json.loads(json.dumps(cert))==json.loads((HERE/'local_fold_certificate.json').read_text()),'local certificate')
need(len(shape)==71 and len(raw)//2==205 and len(folds)==10 and cert['local_cases']==40,'census')
emission=emitter_new(tree)
sites,cfg,contracts=c.source(tree)
need(cfg==b.interval_cfg(sites),'independent CFG')
checks={}
for name,rows in [('raw',raw),('folded',folded)]:
 checks[name]=c.validate(rows,contracts);need(checks[name]['ok'],'runtime '+name)
old,_=c.machine()
need(all(folded[q,bit]==old[q,bit] for q in c.BOXSTATES for bit in (0,1)),'unchanged box rows')
startup=b.startup(dense,labels)
need(startup==json.loads((HERE/'startup.json').read_text()),'startup')
print(json.dumps(dict(states=195,raw_readers=71,folds=10,local_cases=40,
 source_sites=len(sites),contracts=len(contracts),checks=checks,
 emitter=emission,startup=startup['literal_steps'],new_kernel_checked_endpoint=False),indent=2))
