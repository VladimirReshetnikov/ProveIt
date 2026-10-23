#!/usr/bin/env python3
"""Independent exact Sidon and direct-system source diagnostics.

Run from any working directory. The only optional write is the explicitly
requested --output receipt. No archive files or original source directories
are changed. These finite checks do not prove the semantic compiler or
settle Con(ZFC).
"""
import argparse
import json
from itertools import combinations_with_replacement, product
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run_checks():
    WEIGHTS = [0,10,35,55,62,105,144,145,159,168,232,245,306,323,325,353,
               371,374,382,494,499,525,566,578,610,647,681,685,741,777,783,799]


    def field_mul(a,b):
        out=0
        while b:
            if b&1: out ^= a
            b >>= 1
            a <<= 1
            if a&1024: a ^= 1033 # x^10+x^3+1
        return out


    def field_power(a,n):
        out=1
        while n:
            if n&1: out=field_mul(out,a)
            a=field_mul(a,a)
            n >>= 1
        return out


    seen=set()
    raw=[]
    value=1
    for exponent in range(1023):
        require(value not in seen,'GF primitive cycle repeats')
        seen.add(value)
        shifted=value^2
        if field_power(shifted,32)==shifted:
            raw.append(exponent)
        value=field_mul(value,2)
    require(value==1 and len(seen)==1023 and len(raw)==32,'GF construction')
    rotations=[sorted((a-offset)%1023 for a in raw) for offset in raw]
    intermediate=min(rotations,key=lambda a:(max(a),sum(a),a))
    require(max(intermediate)==901,'Intermediate rotation diameter')
    reconstructed=sorted((47*a-342)%1023 for a in intermediate)
    require(reconstructed==WEIGHTS,'Affine Bose--Chowla reconstruction')
    pairs = list(combinations_with_replacement(range(32), 2))
    sums = [(WEIGHTS[i]+WEIGHTS[j]) % 1023 for i,j in pairs]
    require(len(sums) == len(set(sums)) == 528, 'Sidon certificate failed')
    M = max(WEIGHTS)
    K = 2*M+22*(2*M+1)-1
    require((M,K,M+K+2)==(799,36775,37576), 'Exponents incorrect')

    # Toy system n1+n2-3=0, 2-n1*n2=0, with B2 weights 0,1,3.
    # Top residual has positive constant; its simultaneous roots in [0,4)^2
    # are (1,2),(2,1).
    b=4
    base=65536*b*b
    toy_weights=(1,3)
    mt=3
    stride=2*mt+1
    centres=(2*mt,2*mt+stride)
    Kt=2*mt+2*stride-1
    mass=6+1+1+4+1
    require(65536>4096*mass, 'Toy coefficient bound')
    D=(-6*base**centres[0]+base**(centres[0]-1)
       +base**(centres[0]-3)+4*base**centres[1]
       -base**(centres[1]-4))
    N0=base**(mt+1)
    N1=4*base**(Kt+1)
    N=N0*N1
    ell=sum(base**a for a in toy_weights)
    low=N0-1-(b-1)*ell
    high=sum((base-2)*base**e for e in centres)
    T=low+N0*high
    pad=sum(base**(i+1) for i in range(Kt+1))
    cap=b*base**mt


    def evaluate(g):
        require(0<=g<2*cap,'Toy g exceeds declared interval')
        J=2*(1+g)**2*D+pad
        S=g+N0*J
        require(0<S<N and 0<T<N,'Pre-recovery positivity/bounds failed')
        X=(N-1)*((S+T+1)*N+T+1)
        require(X%3==0,'Bridge normalization 3 divides X')
        require(X==(S+T)*N*N+(N-1-S)*N+(N-1-T),'Block identity')
        u=N.bit_length()-1
        require(N==1<<u,'N not a power of two')
        valuation=X.bit_count()
        require((valuation>=2*u)==((S&T)==0),'Kummer/no-carry identity')
        decoded=(g%base==0 and (g//base**2)%base==0
                 and (g//base)%base<b and g//base**3<b)
        n1=(g//base)%base
        n2=g//base**3
        expected=decoded and n1+n2==3 and n1*n2==2
        require(((S&T)==0)==expected,'Source equivalence failed')
        return expected

    fixtures=[]
    for n1,n2 in product(range(8),repeat=2):
        g=n1*base+n2*base**3
        if g<2*cap:
            fixtures.append(g)
    for n1,n2 in product(range(4),repeat=2):
        for bad_position in (0,2):
            for bad_digit in (1,2,3):
                fixtures.append(n1*base+n2*base**3+bad_digit*base**bad_position)
    accepted=sum(evaluate(g) for g in fixtures)
    require(accepted==2,'Unexpected toy solution count')
    result={
     'sidon_modulus':1023,'sidon_weights':WEIGHTS,'distinct_pairs':528,
     'provenance':{'field_polynomial':'x^10+x^3+1','primitive_cycle':1023,
                   'Bose_Chowla_size':32,'first_rotation_diameter':901,
                   'affine_multiplier':47,'affine_translation':-342},
     'M':M,'block_stride':2*M+1,'last_target':2*M+21*(2*M+1),
     'K':K,'N_base_exponent':M+K+2,
     'toy_fixtures':len(fixtures),'toy_acceptances':accepted,
     'status':'PASS; finite diagnostics only'
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Optional JSON receipt path; relative paths use the current working directory.')
    args = parser.parse_args()
    result = run_checks()
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')


if __name__ == '__main__':
    main()
