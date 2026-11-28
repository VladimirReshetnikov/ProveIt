#!/usr/bin/env python3
"""Independent finite enumeration and reproducible critical-window experiments.

Exact checks enumerate all two-planes and all alternating forms on F_2^4 and
F_3^4. A binary subspace dynamic program computes the complete finite-n nullity
laws without using the asymptotic theorem. Monte Carlo is explicitly labelled.
Run from any directory. Output is written to ../results and ../figures.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import comb, prod, sqrt
from pathlib import Path
import argparse
import json
import random

ROOT = Path(__file__).resolve().parents[1]


def rank_mod(rows, q):
    a = [list(row) for row in rows]
    if not a:
        return 0
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j] % q), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][j], -1, q)
        a[r] = [x * inv % q for x in a[r]]
        for i in range(r + 1, len(a)):
            v = a[i][j]
            if v:
                a[i] = [(x - v*y) % q for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def form_matrix(g, n, q):
    a = [[0]*n for _ in range(n)]
    for c, (i, j) in zip(g, ((i,j) for i in range(n) for j in range(i+1,n))):
        a[i][j] = c
        a[j][i] = -c % q
    return a


def standard_form(n):
    return tuple(int(j == i+1 and i % 2 == 0)
                 for i in range(n) for j in range(i+1,n))


def plane_rows(n, q):
    vectors = list(product(range(q), repeat=n))
    rows = set()
    for u in vectors[1:]:
        for v in vectors[1:]:
            w = tuple((u[i]*v[j]-u[j]*v[i]) % q
                      for i in range(n) for j in range(i+1,n))
            first = next((x for x in w if x), None)
            if first is not None:
                inv = pow(first, -1, q)
                rows.add(tuple(inv*x % q for x in w))
    return sorted(rows)


def dot(u, v, q):
    return sum(a*b for a,b in zip(u,v)) % q


def exact_fourier(q):
    n = 4
    D = comb(n, 2)
    planes = plane_rows(n, q)
    H = standard_form(n)
    planted = [w for w in planes if dot(w, H, q) == 0]
    delta = Fraction(q+1, q**n)-Fraction(q, q**(2*n))
    denom = (1-Fraction(1,q**n))*(1-Fraction(q*q,q**n))
    checked = 0
    for G in product(range(q), repeat=D):
        rk = rank_mod(form_matrix(G,n,q), q)
        observed = Fraction(q*sum(dot(w,G,q)==0 for w in planes), len(planes))
        observed = (observed-1)/(q-1)
        theory = (Fraction(1,q**rk)-delta)/(1-delta)
        assert observed == theory, (q,G,'null',observed,theory)
        observed_p = (Fraction(q*sum(dot(w,G,q)==0 for w in planted),len(planted))-1)/(q-1)
        pencil = [rank_mod(form_matrix(tuple((g+a*h)%q for g,h in zip(G,H)),n,q),q)
                  for a in range(q)]
        theory_p = (sum(Fraction(1,q**r) for r in pencil)-q*delta)/denom
        assert observed_p == theory_p, (q,G,'planted',observed_p,theory_p)
        checked += 1
    return {'q':q,'n':n,'planes':len(planes),'isotropic_planes':len(planted),
            'forms':checked,'fourier_identities_checked':2*checked,'passed':True}


def canonical_add(basis, x):
    """Reduced binary rowspace; basis has descending leading positions."""
    for b in basis:
        if x & (1 << (b.bit_length()-1)):
            x ^= b
    if x == 0:
        return basis
    pivot = 1 << (x.bit_length()-1)
    out = [b ^ x if b & pivot else b for b in basis]
    out.append(x)
    return tuple(sorted(out, reverse=True))


def binary_exact(max_t=12):
    n, D = 4, 6
    all_rows = [sum(x << i for i,x in enumerate(w)) for w in plane_rows(n,2)]
    H = sum(x << i for i,x in enumerate(standard_form(n)))
    out = {}
    for name,rows in [('null',all_rows),('planted',[w for w in all_rows if (w&H).bit_count()%2==0])]:
        states = {():1}
        transitions = {}
        laws = []
        for t in range(max_t+1):
            counts = Counter()
            for b,c in states.items():
                counts[D-len(b)] += c
            denom = len(rows)**t
            assert sum(counts.values()) == denom
            laws.append({'t':t,'probabilities':{str(k):str(Fraction(v,denom)) for k,v in sorted(counts.items())},
                         'reachable_rowspaces':len(states)})
            if t == max_t:
                break
            nxt = defaultdict(int)
            for b,c in states.items():
                if b not in transitions:
                    transitions[b] = Counter(canonical_add(b,w) for w in rows)
                for dest,mult in transitions[b].items():
                    nxt[dest] += c*mult
            states = nxt
        out[name] = laws
    return out


def gamma(q, j):
    return prod(1-q**(-r) for r in range(1,j+1))


def pi(q, a, k):
    if k < max(0,-a):
        return 0.0
    return q**(-k*(k+a))*gamma(q,300)/(gamma(q,k)*gamma(q,k+a))


def profiles():
    out = []
    for q in (2,3,4,5):
        for a in range(-5,9):
            null = [pi(q,a-1,k) for k in range(40)]
            planted = [0.0]+[pi(q,a,k) for k in range(39)]
            assert abs(sum(null)-1) < 1e-13
            assert abs(sum(planted)-1) < 1e-13
            tv = sum(abs(x-y) for x,y in zip(null,planted))/2
            closed = gamma(q,300)/gamma(q,a-1) if a>=1 else q**(a-1)*gamma(q,300)/gamma(q,1-a)
            assert abs(tv-closed) < 1e-13
            for k in range(max(1,1-a),15):
                assert abs(planted[k]-q**(a-1)*(q**k-1)*null[k]) < 1e-13
            out.append({'q':q,'a':a,'linear_recovery':gamma(q,300)/gamma(q,a) if a>=0 else 0.,
                        'nullity_testing_tv':closed})
    return out


def binary_wedge(u,v,n):
    # Pack rows lexicographically (i,j), i<j, exactly as in the manuscript.
    w, shift = 0, 0
    for i in range(n-1):
        mask = (1 << (n-i-1))-1
        block = (((v >> (i+1)) if (u >> i)&1 else 0) ^
                 ((u >> (i+1)) if (v >> i)&1 else 0)) & mask
        w |= block << shift
        shift += n-i-1
    return w


def binary_draw(n, planted, rng):
    u = rng.randrange(1,1<<n)
    while True:
        v = rng.randrange(1,1<<n)
        if v == u:
            continue
        if planted:
            Hu = 0
            for i in range(0,n,2):
                Hu |= ((u >> i)&1) << (i+1)
                Hu |= ((u >> (i+1))&1) << i
            if (Hu & v).bit_count() % 2:
                continue
        return binary_wedge(u,v,n)


def monte_carlo(repetitions):
    rng = random.Random(20261127)
    out = []
    for n in (6,10,14):
        D = comb(n,2)
        for planted in (False,True):
            hist = {a:Counter() for a in range(-2,6)}
            for rep in range(repetitions):
                pivots = {}
                for t in range(1,D+5):
                    x = binary_draw(n,planted,rng)
                    while x:
                        p = x.bit_length()-1
                        if p not in pivots:
                            pivots[p] = x
                            break
                        x ^= pivots[p]
                    a = t-(D-1)
                    if a in hist:
                        hist[a][D-len(pivots)] += 1
            for a,counts in hist.items():
                assert sum(counts.values()) == repetitions
                theory = {k:(pi(2,a,k-1) if k>=1 else 0.) if planted else pi(2,a-1,k)
                          for k in range(D+1)}
                tv = sum(abs(counts[k]/repetitions-theory[k]) for k in range(D+1))/2
                out.append({'n':n,'model':'planted' if planted else 'null','a':a,'samples':repetitions,
                            'nullity_counts':dict(sorted(counts.items())),
                            'empirical_tv_to_limit':tv,
                            'note':'Monte Carlo comparison, not a proof or deterministic error bound.'})
    return out


def figures(data):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,axs = plt.subplots(1,2,figsize=(10,3.5),constrained_layout=True)
    for q,color in [(2,'#125E8A'),(3,'#D67A24'),(4,'#52886F')]:
        ds = [x for x in data if x['q']==q and -3<=x['a']<=6]
        for ax,key in zip(axs,['linear_recovery','nullity_testing_tv']):
            ax.plot([x['a'] for x in ds],[x[key] for x in ds],marker='o',lw=1.8,color=color,label=f'q = {q}')
    axs[0].set_title('Certified linear recovery')
    axs[1].set_title('Optimal test using solution dimension')
    for ax in axs:
        ax.set_xlabel('Extra samples a beyond d = n(n - 1)/2 - 1')
        ax.set_ylim(-.02,1.03)
        ax.set_xticks(range(-3,7))
        ax.grid(alpha=.18)
        ax.legend(frameon=False)
    axs[0].set_ylabel('Limiting success probability')
    axs[1].set_ylabel('Limiting total variation distance')
    (ROOT/'figures').mkdir(exist_ok=True)
    fig.savefig(ROOT/'figures/critical_profiles.pdf')
    fig.savefig(ROOT/'figures/critical_profiles.png',dpi=180)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--repetitions',type=int,default=5000)
    args=parser.parse_args()
    out=ROOT/'results'
    out.mkdir(exist_ok=True)
    exact=[exact_fourier(2),exact_fourier(3)]
    prof=profiles()
    (out/'fourier_exact.json').write_text(json.dumps(exact,indent=2)+'\n')
    (out/'critical_profiles.json').write_text(json.dumps(prof,indent=2)+'\n')
    (out/'binary_exact_nullity.json').write_text(json.dumps(binary_exact(),indent=2)+'\n')
    sim=monte_carlo(args.repetitions)
    (out/'binary_monte_carlo.json').write_text(json.dumps(sim,indent=2)+'\n')
    figures(prof)
    summary={'exact_fourier_checks':sum(x['fourier_identities_checked'] for x in exact),
             'exact_cases_passed':True,'profile_identities_passed':True,
             'monte_carlo_trials_per_model':args.repetitions,
             'monte_carlo_max_empirical_tv':max(x['empirical_tv_to_limit'] for x in sim),
             'monte_carlo_note':'Finite-size differences and sampling error are both included.'}
    (out/'verification_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
