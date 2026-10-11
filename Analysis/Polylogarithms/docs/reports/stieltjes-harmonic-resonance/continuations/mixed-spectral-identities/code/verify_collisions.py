"""Independent ambient cutoff quadratures for a triple collision.

Computes one-sided Hadamard finite parts of products of -digamma.
No Tornheim kernels or spectral completion formula are used.
"""

import argparse
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 70

def gamma0(x):
    return -mp.digamma(x)

def singular_interval(etas, length):
    """Current first factor singular at t=0; all other arguments eta+t."""
    residue = mp.fprod(gamma0(x) for x in etas)
    # Exact first derivative determines the continuous value of the
    # subtracted quotient at the origin. Values below 1e-45 are irrelevant
    # at the requested residual tolerance and are evaluated by this limit.
    derivative = mp.fsum(-mp.polygamma(1, etas[i]) *
                        mp.fprod(gamma0(etas[j]) for j in range(len(etas)) if j != i)
                        for i in range(len(etas)))
    limit = derivative + mp.euler * residue
    def regular(t):
        if t == 0 or abs(t) < mp.mpf('1e-45'):
            return limit
        smooth = mp.fprod(gamma0(x+t) for x in etas)
        return (smooth-residue)/t + gamma0(1+t)*smooth
    # Geometric splits capture changes of scale when one eta is small.
    pts = [mp.mpf(0), length/16, length/4, length/2, length]
    return mp.quad(regular, pts) + residue * mp.log(length)

def separated(shifts):
    boundaries = sorted([(mp.frac(-a), i) for i,a in enumerate(shifts)])
    result = mp.mpf(0)
    for n,(point,idx) in enumerate(boundaries):
        following = boundaries[n+1][0] if n+1<len(boundaries) else boundaries[0][0]+1
        etas = [mp.frac(point+shifts[j]) for j in range(3) if j!=idx]
        result += singular_interval(etas, following-point)
    return result

def convolve(a,b):
    out=[mp.mpf(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out

def merged(split=mp.mpf(1)/8, count=100):
    # gamma0(x) = x^-1 (1 + gamma*x + sum_{k>=1}(-1)^k*zeta(k+1)*x^(k+1)).
    terms=[mp.mpf(1),mp.euler]+[(-1)**k*mp.zeta(k+1) for k in range(1,count)]
    coeff=convolve(convolve(terms,terms),terms)
    local=mp.fsum(c*split**(j-2)/(j-2) if j!=2 else c*mp.log(split)
                  for j,c in enumerate(coeff))
    return local+mp.quad(lambda x: gamma0(x)**3,[split,mp.mpf('0.4'),1])

def singular_part(eps,a,b):
    L=mp.log(eps)
    part2=(L/(a*b)+mp.log(a)/(a*(b-a))-mp.log(b)/(b*(b-a)))/eps**2
    part1=mp.euler*(mp.log(a*eps)/a+mp.log(b*eps)/b+mp.log((b-a)*eps)/(b-a))/eps
    part0=mp.zeta(2)*((a-b)/a*mp.log(a*eps)+(b-a)/b*mp.log(b*eps)+b/(b-a)*mp.log((b-a)*eps))
    return part2+part1+part0

def run(output_path):
    q=merged()
    q_other=merged(mp.mpf(1)/10,110)
    rows=[]
    for a,b in [(mp.mpf(1),mp.mpf(2)),(mp.mpf(1),mp.mpf(3)),(mp.mpf(2),mp.mpf(5))]:
        for power in ([2,3,4,5,6,8,10] if (a,b)==(1,2) else [2,3,4,5,6]):
            eps=mp.mpf(10)**(-power)
            value=separated([mp.mpf(0),a*eps,b*eps])
            residual=value-singular_part(eps,a,b)-q
            rows.append({'a':str(a),'b':str(b),'epsilon':str(eps),
                         'finite_part':mp.nstr(value,55),'residual':mp.nstr(residual,40),
                         'residual_div_epsilon_log':mp.nstr(residual/(eps*mp.log(eps)),30)})
            print(a,b,eps,' residual ',mp.nstr(residual,24),flush=True)
    data={'precision':mp.mp.dps,'merged_gamma0_cube':mp.nstr(q,65),
          'merged_split_residual':mp.nstr(q-q_other,40),
          'zeta2_log2_over_2':mp.nstr(mp.zeta(2)*mp.log(2)/2,50),
          'collision_checks':rows,
          'note':'Floating-point diagnostics, not certified interval enclosures.'}
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(data, indent=2) + '\n')

if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        '--output', type=Path,
        default=Path(__file__).resolve().parents[1] / 'results' / 'collisions.json',
        help='Destination JSON record (relative paths use the current directory).')
    args = parser.parse_args()
    run(args.output)
