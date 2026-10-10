#!/usr/bin/env python3
"""Reconstruct the Cayley projector audit and frozen S6 normal form.

All coefficients are exact rational numbers.  The consecutive-cut
Eulerian implementation below is independent of the core permutation
implementation.  No numerical period evaluator or rank solver is used.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import time

import cayley_projection as C


def eulerian_by_cuts(w):
    out = {}
    n = len(w)
    if n == 0:
        return out
    for mask in range(1 << (n-1)):
        positions = [0]+[j for j in range(1,n) if mask >> (j-1) & 1]+[n]
        p = {():1}
        for a,b in zip(positions,positions[1:]):
            p = C.multiply(p,{w[a:b]:1})
        blocks = len(positions)-1
        C.add(out,p,Q((-1)**(blocks-1),blocks))
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-weight',type=int,default=4)
    parser.add_argument('--output-dir',type=Path,
                        default=Path(__file__).resolve().parents[1]/'data')
    args=parser.parse_args()
    if args.max_weight < 1:
        raise ValueError('max-weight must be positive')
    start=time.monotonic()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    independent_cases=[]
    for n in range(1,6):
        w=tuple(range(-1,n-1))
        assert C.eulerian(w)==eulerian_by_cuts(w)
        independent_cases.append(list(w))
    words={}
    for n in range(1,args.max_weight+1):
        total=0
        for w in product(range(-1,4),repeat=n):
            r=C.regularize(w)
            assert C.apply(C.cayley,r)==C.apply(C.regularize,C.cayley(w))
            p=C.projection(w)
            assert p==C.apply(C.projection,p)
            assert p==C.apply(C.projection,C.cayley(w))
            assert p==C.apply(C.cayley,p)
            assert p==C.apply(C.projection,r)
            k={C.conjugate(v):c for v,c in p.items()}
            assert k==C.projection(C.conjugate(w))
            if C.admissible(w):
                assert r=={w:1}
            total+=1
        words[n]=total
        print(json.dumps({'weight':n,'checked_words':total}),flush=True)
    pairs=0
    for n in range(2,args.max_weight+1):
        for k in range(1,n):
            for u in product(range(-1,4),repeat=k):
                for v in product(range(-1,4),repeat=n-k):
                    assert (C.apply(C.projection,C.shuffle(u,v))==
                            C.multiply(C.projection(u),C.projection(v)))
                    pairs+=1
    witness=(C.Z,)*5+(1,1)
    atoms={
        'g61':{C.word(((6,1),(1,0))):1},
        'K61':{C.word(((6,1),(1,2))):1},
        'g43':{C.word(((4,1),(3,0))):1},
        'g25':{C.word(((2,1),(5,0))):1},
        'beta7':{C.word(((7,1),)):1},
        'G_zeta5':C.shuffle(C.word(((2,1),)),C.word(((5,0),))),
        'beta4_zeta3':C.shuffle(C.word(((4,1),)),C.word(((3,0),))),
        'negative_beta6_log2':C.shuffle(C.word(((6,1),)),C.word(((1,2),))),
    }
    expected={'g61':Q(1,4),'K61':Q(-1,4),'g43':0,'g25':0,
              'beta7':0,'G_zeta5':0,'beta4_zeta3':0,
              'negative_beta6_log2':0}
    table={}
    for name,p in atoms.items():
        value=C.odd(C.apply(C.projection,p)).get(witness,0)
        assert value==expected[name],(name,value)
        table[name]=str(value)
    coordinate_families={}
    for weight in range(3,8):
        coordinate=(C.Z,)*(weight-2)+(1,1)
        doubles=[]
        for first in range(1,weight):
            second=weight-first
            value=C.odd(C.projection(C.word(((first,1),(second,0))))).get(coordinate,0)
            assert value==(Q(1,4) if second==1 else 0)
            doubles.append(str(value))
        mixed=C.odd(C.projection(C.word(((weight-1,1),(1,2))))).get(coordinate,0)
        assert mixed==Q(-1,4)
        coordinate_families[weight]={'single_color_doubles':doubles,
                                     'mixed_endpoint':str(mixed)}
    normal=C.odd(C.apply(C.projection,C.s6_target()))
    assert len(normal)==3444
    assert normal[witness]==-166348800
    payload={
        'schema':'proveit.cayley-normal-form.v1',
        'weight':7,
        'letter_codes':{'-1':'z','0':'c','1':'a','2':'b','3':'abar'},
        'conventions':'Outer first; shuffle; imaginary projection uses coefficient differences, not halves.',
        'target':'Equation cay:eq:target in sections/05_cayley.tex; Im H(target) is the frozen integer-normalized S6 residual.',
        'nonzero_terms':len(normal),
        'terms':[[list(w),str(c)] for w,c in sorted(normal.items())],
    }
    encoded=(json.dumps(payload,indent=2)+'\n').encode()
    path=args.output_dir/'cayley_s6_normal_form.json'
    path.write_bytes(encoded)
    report={
        'schema':'proveit.cayley-projection-audit.v1',
        'exact_arithmetic':True,
        'independent_eulerian_cut_cases':independent_cases,
        'words_checked_by_weight':words,
        'total_words_checked':sum(words.values()),
        'shuffle_pairs_checked':pairs,
        'identities_checked':['R C = C R','Pi^2 = Pi','Pi C = Pi',
                              'C Pi = Pi','Pi R = Pi','K Pi = Pi K',
                              'R fixes admissible words','Pi respects shuffle products'],
        'separating_word':list(witness),
        'separating_atom_values':table,
        'all_weight_coordinate_formula_audit':coordinate_families,
        'target_separating_value':str(normal[witness]),
        'target_normal_form_terms':len(normal),
        'normal_form_sha256':hashlib.sha256(encoded).hexdigest(),
        'elapsed_seconds':round(time.monotonic()-start,4),
        'scope':'The full Cayley shuffle ideal only; no S6 equality or arithmetic nonmembership claim.',
    }
    (args.output_dir/'cayley_projection_verification.json').write_text(
        json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__=='__main__':
    main()
