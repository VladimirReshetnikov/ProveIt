#!/usr/bin/env python3
"""Fresh finite rational checks of the new Markov-mask matrix lift only."""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json

def need(value, message):
    if not value:
        raise ValueError(message)

def multiply(matrix, vector):
    return [sum(a*b for a,b in zip(row, vector)) for row in matrix]

def transfer(mask, dilation, vector):
    out = {}
    for n, value in vector.items():
        for j, weight in mask.items():
            if (n+j) % dilation == 0:
                k = (n+j)//dilation
                out[k] = out.get(k, Fraction(0)) + value*weight
    return {k:v for k,v in out.items() if v}

def encoded(vector, scale=1):
    return {sign*(i+1): Fraction(v, 2*scale)
            for i,v in enumerate(vector) if v for sign in [-1,1]}

def receipt():
    cases=[]
    basis_checks=0
    word_checks=0
    for r in range(1,7):
        matrices=[[[0 for m in range(r)] for k in range(r)],
                  [[int(k==m) for m in range(r)] for k in range(r)],
                  [[(3*k+5*m+r)%7-3 for m in range(r)] for k in range(r)],
                  [[int(m==k+1)-2*int(k==m+1) for m in range(r)] for k in range(r)]]
        S=max(sum(abs(x) for row in M for x in row) for M in matrices)
        q=2*S+1
        b=2*r+1
        D=b*r-1
        masks=[]
        for M in matrices:
            mask={0:Fraction(1)}
            for k in range(1,r+1):
                for m in range(1,r+1):
                    j=b*k-m
                    need(j not in mask and -j not in mask, 'frequency collision')
                    if M[k-1][m-1]:
                        mask[j]=mask[-j]=Fraction(M[k-1][m-1],q)
            need(all(abs(j)<=D for j in mask), 'degree bound')
            need(all(j==0 or j%b!=0 for j in mask), 'Markov normalization')
            margin=1-sum(abs(v) for j,v in mask.items() if j)
            need(margin>=Fraction(1,q)>0, 'strict positivity certificate')
            need(D//(b-1)==r, 'declared core')
            for m in range(-r,r+1):
                actual=transfer(mask,b,{m:Fraction(1)})
                expected={0:Fraction(1)} if m==0 else {
                    (1 if m>0 else -1)*(k+1):Fraction(M[k][abs(m)-1],q)
                    for k in range(r) if M[k][abs(m)-1]}
                need(actual==expected, 'basis block')
                basis_checks+=1
            masks.append(mask)
            cases.append({'r':r,'dilation':b,'degree_bound':D,'q':q,'integer_matrix':M,
                          'fourier_mask':[[j,str(v)] for j,v in sorted(mask.items())],
                          'positive_lower_bound':str(margin)})
        for i,M in enumerate(matrices):
            for j,N in enumerate(matrices):
                for m in range(r):
                    v=[int(k==m) for k in range(r)]
                    actual=transfer(masks[j],b,transfer(masks[i],b,encoded(v)))
                    expected=encoded(multiply(N,multiply(M,v)),q*q)
                    need(actual==expected, 'two-step word order/scale')
                    word_checks+=1
    # A separate wholly zero family has q=1, beyond zero members of nonzero families.
    for r in range(1,7):
        b=2*r+1
        for m in range(1,r+1):
            need(transfer({0:Fraction(1)},b,encoded([int(k==m-1) for k in range(r)]))=={},
                 'all-zero family')
    return {'schema':'markov-mask-integer-matrix-lift-finite-checks-v1',
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'cases':cases,'basis_images':basis_checks,'two_step_cosine_images':word_checks,
            'all_zero_family_dimensions':list(range(1,7)),
            'scope':'Fresh finite rational checks of the proved matrix lift; no supplied or predecessor code, unbounded history, spectral theorem or universal compiler evaluated.'}

def main():
    p=argparse.ArgumentParser()
    group=p.add_mutually_exclusive_group(required=True)
    group.add_argument('--output')
    group.add_argument('--expect')
    args=p.parse_args()
    data=receipt()
    raw=(json.dumps(data,indent=2,sort_keys=True)+'\n').encode()
    if args.output:
        with open(args.output,'xb') as f:
            f.write(raw)
    else:
        need(Path(args.expect).read_bytes()==raw,'exact receipt')
    print('PASS',len(data['cases']),'matrix masks;',data['basis_images'],
          'basis images;',data['two_step_cosine_images'],'two-step images')

if __name__=='__main__':
    main()
