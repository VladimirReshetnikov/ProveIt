"""Independent local audit. Read upstream JSON as data; import no upstream code."""

import sys
sys.dont_write_bytecode = True
import argparse
from pathlib import Path
import hashlib
import json
import math

ROOT = Path(__file__).resolve().parent
INPUT = ROOT.parent/'inherited-source'/'three_mass_unbounded_interface.json'
PIN = 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e'
CHANGED = {'native__j', 'native__o', 'native__y_aux'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def mul(a, b, mod=None):
    ans = (a[0]*b[0]+a[1]*b[2], a[0]*b[1]+a[1]*b[3],
           a[2]*b[0]+a[3]*b[2], a[2]*b[1]+a[3]*b[3])
    return tuple(x % mod for x in ans) if mod else ans


def power(a, n):
    ans = (1, 0, 0, 1)
    while n:
        if n & 1:
            ans = mul(ans, a)
        a = mul(a, a)
        n //= 2
    return ans


def apply(a, v):
    return (a[0]*v[0]+a[1]*v[1], a[2]*v[0]+a[3]*v[1])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check",action="store_true",help="Recompute and compare without writing; also the default")
    parser.parse_args()
    raw = INPUT.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == PIN, 'Check failed: hashlib.sha256(raw).hexdigest() == PIN')
    receipt = json.loads(raw)
    reports = []
    blocks = []
    for fixture in receipt['fixtures']:
        native_rows = [row for row in fixture['source'] if row[0].startswith('native__')]
        native_coords = [x for x in fixture['auxiliaries'] if x.startswith('native__')]
        native_comparisons = fixture['comparisons'][2:18]
        require(len(native_rows) == 64, 'Check failed: len(native_rows) == 64')
        require(len(native_coords) == 22, 'Check failed: len(native_coords) == 22')
        require(len(native_comparisons) == 16, 'Check failed: len(native_comparisons) == 16')
        deps = {x: {x} for x in CHANGED}
        for name, op, a, b in fixture['source']:
            deps[name] = deps.get(a, set()) | deps.get(b, set())
        affected = [i+1 for i, (a,b) in enumerate(native_comparisons)
                    if deps.get(a,set()) | deps.get(b,set())]
        require(affected == [13,14], 'Check failed: affected == [13,14]')
        all_affected = [i+1 for i, (a,b) in enumerate(fixture['comparisons'])
                        if deps.get(a,set()) | deps.get(b,set())]
        require(all_affected == [15,16], 'Check failed: all_affected == [15,16]')
        descendants = [row[0] for row in native_rows if deps.get(row[0],set())]
        require(descendants == ['native__of','native__aux_u_rhs','native__jc','native__H17',
                               'native__H2','native__aux_y2','native__aux_square_gap',
                               'native__L17','native__P17'], "Check failed: descendants == ['native__of','native__aux_u_rhs','native__jc','native__H17',                                'native__H2','native__aux_y2','native__aux_square_gap',                                'native__L17','native__P17']")
        reports.append({'fixture': fixture['name'], 'native_gates':64,
                        'native_coordinates':22, 'native_comparisons':16,
                        'changed_coordinates':sorted(CHANGED),
                        'affected_native_comparisons_one_based':affected,
                        'affected_full_comparisons_one_based':all_affected,
                        'derived_native_gates_that_can_change':descendants})
        blocks.append({'fixture':fixture['name'], 'auxiliaries':native_coords,
                       'source':native_rows, 'comparisons':native_comparisons})

    # This small seed satisfies the three auxiliary norm/congruence equations,
    # but is NOT a complete 22-coordinate native witness (its p=1 is too small).
    # It numerically checks the matrix mechanism, not inherited completeness.
    a,c,f,i,p,U,y = 1,2,3,2,1,1,1
    R = i*c*c
    D = R*R-1
    N = R*c*f
    require(R*R == (a*a+4*a+3)*(f*f-1), 'Check failed: R*R == (a*a+4*a+3)*(f*f-1)')
    require((R*U)**2-D*y*y == 1, 'Check failed: (R*U)**2-D*y*y == 1')
    require((U+p)%c == 0 and (U+c)%f == 0, 'Check failed: (U+p)%c == 0 and (U+c)%f == 0')
    B = (R,D,1,R)
    reduced = (1,0,0,1)
    for L in range(1,N**4+1):
        reduced = mul(reduced,B,N)
        if reduced == (1,0,0,1):
            break
    else:
        raise AssertionError('Finite invertible matrix has no order')
    require(L == 12, 'Check failed: L == 12')
    period = power(B,L)
    require(tuple(x%N for x in period) == (1,0,0,1), 'Check failed: tuple(x%N for x in period) == (1,0,0,1)')
    V,Y = R*U,y
    trials = []
    for n in range(5):
        require(V%R == 0, 'Check failed: V%R == 0')
        Un = V//R
        require((Un-U)%(c*f) == 0, 'Check failed: (Un-U)%(c*f) == 0')
        require((Un+p)%c == 0 and (Un+c)%f == 0, 'Check failed: (Un+p)%c == 0 and (Un+c)%f == 0')
        jn,on = (Un+p)//c,(Un+c)//f
        require(min(jn,on,Y) > 0, 'Check failed: min(jn,on,Y) > 0')
        require(jn*c-p == on*f-c == Un, 'Check failed: jn*c-p == on*f-c == Un')
        require(R*R*(Un*Un-Y*Y) == 1-Y*Y, 'Check failed: R*R*(Un*Un-Y*Y) == 1-Y*Y')
        trials.append({'n':n,'U':str(Un),'j':str(jn),'o':str(on),'y_aux':str(Y)})
        nxt = apply(period,(V,Y))
        require(nxt[0]>V and nxt[1]>Y, 'Check failed: nxt[0]>V and nxt[1]>Y')
        V,Y = nxt

    # The integer identity used in the proof can also be coefficient-checked.
    # Coefficients of V^2, VY, Y^2 after one matrix step:
    for r in range(2,25):
        d = r*r-1
        require((r*r-d, 2*r*d-2*d*r, d*d-d*r*r) == (1,0,-d), 'Check failed: (r*r-d, 2*r*d-2*d*r, d*d-d*r*r) == (1,0,-d)')

    result = {'status':'PASS', 'input_sha256':PIN, 'fixtures':reports,
              'toy_auxiliary_example':{'scope':'Not a complete native witness',
                  'a':a,'c':c,'f':f,'i':i,'p':p,'R':R,'D':D,'N':N,'matrix_order':L,
                  'checked_terms':trials},
              'evidence_boundary':'Finite arithmetic and dependency checks supplement THEOREM.md; no complete native Pell tuple was materialized.'}
    require((ROOT/'source'/'native_blocks.json').read_bytes() == (json.dumps(blocks,indent=2)+'\n').encode(), 'Native block receipt differs')
    require((ROOT/'CHECK-RECEIPT.json').read_bytes() == (json.dumps(result,indent=2)+'\n').encode(), 'Native family receipt differs')
    print(json.dumps({'status':'PASS','fixtures':len(reports),'native_dependency_checks':4,
                      'auxiliary_family_terms':len(trials),'matrix_order':L}))


if __name__ == '__main__':
    main()
