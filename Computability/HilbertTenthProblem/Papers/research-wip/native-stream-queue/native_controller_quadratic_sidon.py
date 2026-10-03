"""Typed counterexamples to a periodic Sidon square's local interpretation."""
import argparse
from itertools import product
import json
from pathlib import Path

B=256
MASK=177


def payload(a,b):
    return sum((2*x+8*y)*B**i for i,(x,y) in enumerate(zip(a,b)))


def module_map(U,N):
    q=B**N;J=(q-1)//(B-1);n=2**(4*N)
    assert n*n==q and MASK.bit_count()==4 and MASK%2==1
    assert 0<U<q and U%2==0 and U&(MASK*J)==0
    r=(q-U)*(q-1)+MASK*J
    assert q<=r<q*q and r%2==1 and r.bit_count()==12*N
    return dict(N=N,word_bits=U.bit_length(),q_bits=q.bit_length(),packed_index_bits=r.bit_length(),
                packed_population=r.bit_count(),required_valuation=12*N,
                full_positive_kernel_extension='Reviewed one-field51 converse applies parametrically')


def family():
    rows=[]
    for p in range(1,10):
        N=4*p+1;q=B**N;J=(q-1)//(B-1)
        good=2+8*B**(2*p);bad=10*B**p
        good_map=module_map(good,N);bad_map=module_map(bad,N)
        expected=32*B**(2*p)
        assert good*good==4+32*B**(2*p)+64*B**(4*p)
        assert bad*bad==100*B**(2*p)
        assert good*good<q and bad*bad<q
        assert good*good&(32*J)==bad*bad&(32*J)==expected
        assert good*good&(MASK*J)==bad*bad&(MASK*J)==expected
        good_local=all(not((good//B**i% B)&2 and (good//B**i%B)&8) for i in range(N))
        bad_local=all(not((bad//B**i%B)&2 and (bad//B**i%B)&8) for i in range(N))
        assert good_local and not bad_local
        rows.append(dict(p=p,good_module=good_map,bad_module=bad_map,flag_cell=2*p,flag_bit=5,
                         good_local_predicate=True,bad_local_predicate=False,identical_nonzero_square_flags=True))
    return dict(fixed_cell_radix=B,fixed_half_mask=MASK,counterexample_pairs=len(rows),domains=rows)


def rotated():
    cases=0
    for p in range(1,6):
        for h in range(0,8):
            N=4*p+h+1;q=B**N;J=(q-1)//(B-1)
            good=2+8*B**(2*p);bad=10*B**p
            flags=[]
            for U in (good,bad):
                V=B**h*U
                assert 0<V<q and V==(B**h*U)%(q-1)
                assert U*V<q
                module_map(U,N)
                flags.append(U*V&(32*J))
            assert flags==[32*B**(2*p+h)]*2
            cases+=1
    return dict(no_wrap_rotated_pairs=cases,maximum_rotation_cells=7)


def convolution():
    cases=0
    for N in range(1,7):
        for a,b in product(product((0,1),repeat=N),repeat=2):
            U=payload(a,b)
            coefficients=[]
            mixed=[]
            for k in range(2*N-1):
                aa=sum(a[i]*a[k-i] for i in range(N) if 0<=k-i<N)
                ab=sum(a[i]*b[k-i] for i in range(N) if 0<=k-i<N)
                bb=sum(b[i]*b[k-i] for i in range(N) if 0<=k-i<N)
                coefficients.append(4*aa+32*ab+64*bb)
                mixed.append(ab)
            assert U*U==sum(c*B**k for k,c in enumerate(coefficients))
            # This is a polynomial identity even when a displayed coefficient
            # exceeds B; no false native-digit bound is asserted here.
            cases+=1
    return dict(arbitrary_payload_pairs=cases,maximum_cells=6,
                scope='Exact polynomial convolution; native coefficient bounds are claimed only for the explicit sparse pairs')


def verify():
    return dict(status='PASS_QUADRATIC_SIDON_COLLISION',family=family(),rotated=rotated(),convolution=convolution(),
                scope='Refutes the mixed-band local interpretation, not arbitrary quadratic compilers',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],pairs=result['family']['counterexample_pairs'],
                         rotations=result['rotated']['no_wrap_rotated_pairs'],
                         convolution_cases=result['convolution']['arbitrary_payload_pairs']),indent=2))
