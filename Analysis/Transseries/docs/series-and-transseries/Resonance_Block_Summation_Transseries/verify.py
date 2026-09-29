#!/usr/bin/env python3
"""Reproduce symbolic and high-precision checks for the accompanying article.

The output is numerical corroboration, NOT directed-rounding interval arithmetic.
Run: python verify.py --stage all   (or symbolic, numeric, tables).
Only local results/ files are written. No network access is used.
"""
from __future__ import annotations
import argparse
import json
import platform
from pathlib import Path
from typing import Any
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results'
OUT.mkdir(exist_ok=True)

def dump(name: str, obj: Any) -> None:
    (OUT / name).write_text(json.dumps(obj, indent=2) + '\n', encoding='utf-8')

def s(x: Any, digits: int = 35) -> str:
    return mp.nstr(x, digits)

def symbolic() -> None:
    t, a, x, u, y, lam = sp.symbols('t a x u y lam', positive=True)
    checks: list[str] = []
    def eq(name: str, lhs: Any, rhs: Any) -> None:
        assert sp.simplify(lhs-rhs) == 0, name
        checks.append(name)
    # Local Borel coefficients, independently expanded as two factors.
    inv1 = sp.series(t/sp.sin(sp.pi*t), t, 0, 10).removeO()
    inv2 = sp.series(t/sp.sin(sp.pi*a*t), t, 0, 10).removeO()
    coeff = sp.expand(inv1*inv2)
    eq('Borel coefficient b0', coeff.coeff(t,0), 1/(sp.pi**2*a))
    eq('Borel coefficient b2', coeff.coeff(t,2), (1+a*a)/(6*a))
    eq('Borel coefficient b4', coeff.coeff(t,4), sp.pi**2*(7*a**4+10*a*a+7)/(360*a))
    for k in range(1,10,2):
        eq(f'vanishing odd coefficient {k}', coeff.coeff(t,k), 0)
    # Confluent residues: expanding the regular factor suffices for the residue.
    double = sp.series(sp.exp(-x*u)*(y+u)**2 * (u/sp.sin(sp.pi*u)) *
                       (u/sp.sin(sp.pi*a*u)), u, 0, 2).removeO().expand().coeff(u,1)
    eq('double-pole residue', double, (2*y-y*y*x)/(sp.pi**2*a))
    triple = sp.series(sp.exp(-x*u)*(y+u)**3*(u/sp.sin(sp.pi*u))**3,
                       u,0,3).removeO().expand().coeff(u,2)
    eq('triple-pole residue', triple,
       (3*y-3*y*y*x+y**3*(x*x+sp.pi**2)/2)/sp.pi**3)
    # Bernoulli formula for z/sin z.
    cseries = sp.series(t/sp.sin(t), t, 0, 20).removeO().expand()
    for k in range(1,10):
        ck = (-1)**(k+1)*(2**(2*k)-2)*sp.bernoulli(2*k)/sp.factorial(2*k)
        eq(f'cosecant Bernoulli coefficient {k}', cseries.coeff(t,2*k), ck)
    # Rational resonance generating functions.
    q = sp.symbols('q')
    geom = q/(1-q)
    eq('sum n q^n', q*sp.diff(geom,q), q/(1-q)**2)
    eq('sum n^2 q^n', q*sp.diff(q/(1-q)**2,q), q*(1+q)/(1-q)**3)
    # Classical inversion formula in a nonlinear core; exact solution known.
    phi = y+y*y
    j = 1+y
    exact = -lam/(1+lam) + (-lam/(1+lam))**2
    expanded = sp.series(exact,lam,0,13).removeO().expand()
    for n in range(1,13):
        predicted = (-1)**n*sp.diff(sp.diff(phi,y)*j**n,y,n-1).subs(y,0)/sp.factorial(n)
        eq(f'nonlinear inverse coefficient {n}', expanded.coeff(lam,n), predicted)
    # Divided differences of exp for low distinct rational nodes.
    for nodes in ([0,1], [0,1,3], [-2,0,1,4]):
        z = sp.symbols('z')
        residue_sum = sum(sp.exp(-v)/sp.prod(v-w for w in nodes if w != v) for v in nodes)
        # Newton recursion as an independent algebraic evaluation.
        dd = [sp.exp(-v) for v in nodes]
        for order in range(1,len(nodes)):
            dd = [(dd[k+1]-dd[k])/(nodes[k+order]-nodes[k]) for k in range(len(dd)-1)]
        eq(f'divided difference nodes {nodes}', residue_sum, dd[0])
    dump('symbolic.json', {'assertions_passed':len(checks), 'checks':checks,
                          'sympy_version':sp.__version__})
    print(f'Symbolic: {len(checks)} exact assertions passed.')

def exprel(v: mp.mpf) -> mp.mpf:
    return mp.mpf(1) if v == 0 else mp.expm1(v)/v

def kfun(alpha: mp.mpf, eps: mp.mpf) -> mp.mpf:
    if eps == 0 or alpha == 1:
        return mp.mpf(0)
    if max(1,abs(alpha))*abs(eps) >= mp.mpf('0.02'):
        return (1/mp.sinc(mp.pi*eps)-1/mp.sinc(mp.pi*alpha*eps))/eps
    total = mp.mpf(0)
    # Taylor series avoids subtracting two quantities nearly equal to one.
    for k in range(1,150):
        ck = (-1)**(k+1)*(2**(2*k)-2)*mp.bernoulli(2*k)/mp.factorial(2*k)
        term = ck*mp.pi**(2*k)*(-mp.expm1(2*k*mp.log(alpha)))*eps**(2*k-1)
        total += term
        if k>1 and abs(term) < mp.eps*max(abs(total),mp.mpf('1e-1000')):
            return total
    raise ArithmeticError('cosecant series did not meet the precision target')

def pair(alpha: mp.mpf, n: int, m: int, x: mp.mpf) -> mp.mpf:
    aa = mp.mpf(n)
    bb = mp.mpf(m)/alpha
    eps = bb-aa
    return ((-1)**(n+m)*mp.exp(-x*aa)/(mp.pi**2*alpha) *
            ((2*aa+eps-x*bb*bb*exprel(-x*eps))/mp.sinc(mp.pi*eps)
             +aa*aa*kfun(alpha,eps)))

def raw_pair(alpha: mp.mpf, n: int, m: int, x: mp.mpf) -> mp.mpf:
    aa = mp.mpf(n); bb = mp.mpf(m)/alpha
    return ((-1)**n*aa*aa*mp.exp(-x*aa)/(mp.pi*mp.sin(mp.pi*alpha*aa)) +
            (-1)**m*bb*bb*mp.exp(-x*bb)/(mp.pi*alpha*mp.sin(mp.pi*bb)))

def block_sum(alpha: mp.mpf, x: mp.mpf, cutoff: mp.mpf,
              delta: mp.mpf = mp.mpf(1)/16) -> tuple[mp.mpf,int,int]:
    """The d=2 partition on the fixed period box [1/2,2]."""
    if not (mp.mpf('.5') <= alpha <= 2):
        raise ValueError('this implementation uses the period box [1/2,2]')
    nodes: list[tuple[mp.mpf,int,int]] = []
    for label,omega in ((0,mp.mpf(1)),(1,alpha)):
        for n in range(1,int(mp.ceil(omega*(cutoff+1)))+1):
            nodes.append((mp.mpf(n)/omega,label,n))
    nodes.sort()
    blocks: list[list[tuple[mp.mpf,int,int]]] = []
    for node in nodes:
        if not blocks or node[0]-blocks[-1][-1][0] >= delta:
            blocks.append([node])
        else:
            blocks[-1].append(node)
    values=[]; used=0; pairs=0
    for block in blocks:
        if block[0][0]>=cutoff:
            break
        assert len(block)<=2
        used+=1
        if len(block)==2:
            indices={label:n for _,label,n in block}
            assert len(indices)==2
            values.append(pair(alpha,indices[0],indices[1],x)); pairs+=1
        else:
            aa,label,n=block[0]
            if label==0:
                values.append((-1)**n*aa*aa*mp.exp(-x*aa)/(mp.pi*mp.sin(mp.pi*alpha*aa)))
            else:
                values.append((-1)**n*aa*aa*mp.exp(-x*aa)/(mp.pi*alpha*mp.sin(mp.pi*aa)))
    return mp.fsum(values),used,pairs

def tail_bound(x: mp.mpf, cutoff: mp.mpf) -> mp.mpf:
    # d=2, m0=1/2, M0=2: K=1296, D0=8, rho=1/64, P2(x)=65+x.
    return 1296*8*2*(cutoff+2)**2*(65+x)*mp.exp(-cutoff*x)/(1-mp.exp(-x))**3

def contour_sum(alpha: mp.mpf, x: mp.mpf) -> mp.mpf:
    theta=mp.mpf('.4'); direction=mp.exp(1j*theta)
    def integrand(r: mp.mpf) -> mp.mpc:
        if not r:
            return direction/(mp.pi**2*alpha)
        t=direction*r
        return direction*mp.exp(-x*t)*t*t/(mp.sin(mp.pi*t)*mp.sin(mp.pi*alpha*t))
    value=mp.quad(integrand,[0,mp.mpf('.5'),1,2,4,8,16,mp.inf])
    return -mp.im(value)/mp.pi

def numeric() -> None:
    mp.mp.dps=90
    rows=[]; checks=0
    for label,alpha in [('1',mp.mpf(1)), ('sqrt(2)',mp.sqrt(2)),
                        ('3/2',mp.mpf(3)/2),
                        ('3/2 + 10^-30',mp.mpf(3)/2+mp.mpf('1e-30'))]:
        x=mp.mpf(3); cutoff=mp.mpf(25)
        blocks,count,npairs=block_sum(alpha,x,cutoff)
        integral=contour_sum(alpha,x)
        err=abs(blocks-integral); bound=tail_bound(x,cutoff)
        assert err<bound, (label,s(err),s(bound)); checks+=1
        rows.append({'alpha':label,'x':s(x),'cutoff':s(cutoff),
                     'block_sum':s(blocks),'contour_value':s(integral),
                     'absolute_discrepancy':s(err),'proved_tail_bound_evaluated':s(bound),
                     'blocks':count,'two_node_blocks':npairs})
        if alpha==1:
            q=mp.exp(-x)
            exact=(2*q/(1-q)**2-x*q*(1+q)/(1-q)**3)/mp.pi**2
            assert abs(integral-exact)<mp.mpf('1e-75'); checks+=1
    # Stable formula at increasingly close resonances.
    pair_rows=[]
    for digits in (4,10,25,40,60):
        with mp.workdps(200):
            alpha=1+mp.mpf(10)**(-digits)
            ref=raw_pair(alpha,1,1,mp.mpf(3))
            st=pair(alpha,1,1,mp.mpf(3))
            assert abs(st-ref)<mp.mpf(10)**(-190+2*digits); checks+=1
        with mp.workdps(90):
            low=pair(+alpha,1,1,mp.mpf(3))
        with mp.workdps(200):
            rel=abs((low-ref)/ref)
            assert rel<mp.mpf('1e-80'); checks+=1
            pair_rows.append({'separation_parameter':f'10^-{digits}',
                              'relative_error_stable_90dps':s(rel)})
    # A deliberate precision-loss demonstration (not an assertion of failure).
    with mp.workdps(200):
        alpha=1+mp.mpf('1e-40'); ref=pair(alpha,1,1,mp.mpf(3))
    with mp.workdps(50):
        raw=raw_pair(+alpha,1,1,mp.mpf(3)); stable=pair(+alpha,1,1,mp.mpf(3))
    with mp.workdps(200):
        loss={'working_dps':50,'alpha':'1 + 10^-40',
              'raw_relative_error':s(abs((raw-ref)/ref)),
              'stable_relative_error':s(abs((stable-ref)/ref))}
    dump('numeric.json',{'assertions_passed':checks,'working_dps':90,
                         'reference_dps':200,'contour_checks':rows,
                         'pair_checks':pair_rows,'cancellation_example':loss,
                         'mpmath_version':mp.__version__,
                         'interval_certificates':False})
    print(f'Numerical: {checks} assertions passed; contour/residue and stable-pair comparisons completed.')

def tables() -> None:
    mp.mp.dps=90
    rows=[]
    for lam in [-2,mp.mpf('-.5'),0,mp.mpf('.5'),2]:
        limit=-exprel(mp.mpf(lam))
        vals=[]
        for xx in (20,80,320,1280):
            x=mp.mpf(xx); alpha=1+mp.mpf(lam)/x
            scaled=mp.pi**2*mp.exp(x)*pair(alpha,1,1,x)/x
            vals.append(s(scaled,18))
        rows.append({'lambda':s(lam,4),'x_values':[20,80,320,1280],
                     'scaled_pair':vals,'limit':s(limit,18)})
    dump('coalescence.json',rows)
    lines=[r'\begin{tabular}{r r r r r r}',r'\toprule',
           r'$\lambda$ & $x=20$ & $x=80$ & $x=320$ & $x=1280$ & Limit\\',r'\midrule']
    for r in rows:
        vals=[mp.nstr(mp.mpf(v),8) for v in r['scaled_pair']]
        lines.append(' & '.join([r['lambda']]+vals+[mp.nstr(mp.mpf(r['limit']),8)])+r'\\')
    lines += [r'\bottomrule',r'\end{tabular}']
    (OUT/'coalescence_table.tex').write_text('\n'.join(lines)+'\n')
    print('Coalescence table generated.')

def summary() -> None:
    paths=[OUT/'symbolic.json',OUT/'numeric.json',OUT/'coalescence.json']
    if not all(p.exists() for p in paths):
        return
    data={p.stem:json.loads(p.read_text()) for p in paths}
    data['python_version']=platform.python_version()
    data['total_assertions_passed']=data['symbolic']['assertions_passed']+data['numeric']['assertions_passed']
    dump('verification.json',data)
    num=data['numeric']
    text=[f"Python {platform.python_version()}; SymPy {sp.__version__}; mpmath {mp.__version__}.",
          f"Exact assertions: {data['symbolic']['assertions_passed']}.",
          f"Numerical assertions: {num['assertions_passed']}.",
          'These checks are not interval-arithmetic certificates.', '', 'Contour checks:']
    for r in num['contour_checks']:
        text.append(f"alpha={r['alpha']}: discrepancy={r['absolute_discrepancy']}; tail bound={r['proved_tail_bound_evaluated']}")
    text += ['', 'Cancellation demonstration:',json.dumps(num['cancellation_example'],indent=2)]
    (OUT/'verification.txt').write_text('\n'.join(text)+'\n')
    print(f"Total assertions: {data['total_assertions_passed']}.")

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage',choices=['all','symbolic','numeric','tables'],default='all')
    args=parser.parse_args()
    for name,fn in [('symbolic',symbolic),('numeric',numeric),('tables',tables)]:
        if args.stage in ('all',name):
            fn()
    summary()
