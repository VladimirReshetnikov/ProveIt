#!/usr/bin/env python3
"""Fresh finite probes of the proved packing; no builder or upstream execution.

The fixed matrix arrays are read from authenticated inert JSON. Saved accepting
trace fields are never read. All tested words and histories are generated here.
This tests semantic macro interfaces, not gigantic complete Pell witnesses.
"""
import hashlib
import itertools
import json
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
RECEIPT_SHA = 'f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0'


def check(value, message):
    if not value: raise ValueError(message)


def pack(values, base):
    answer = 0
    for v in reversed(values): answer = answer*base+v
    return answer


def subset(mask, value): return value >= 0 and (mask & value) == value


def fixed_data():
    raw = (HERE/'sources/matrix193_countdown_rows.json').read_bytes()
    check(hashlib.sha256(raw).hexdigest()==RECEIPT_SHA,'source hash')
    a = json.loads(raw)
    initial = a['initial_state']['X']+a['initial_state']['Y']
    pairs = [([1,0,0,1],a['transitions']['loader']['Y_matrix'])]
    pairs += [(t['K'],t['G']) for t in a['transitions']['tiles']]
    matrices = []
    for K,G in pairs:
        matrices.append([[K[0],K[2],0,0],[K[1],K[3],0,0],
                         [0,0,G[0],G[2]],[0,0,G[1],G[3]]])
    threshold = max([128]+[2+sum(map(abs,row))+abs(1-sum(row))
                           for matrix in matrices for row in matrix])
    C = 2**((threshold-1).bit_length())
    check(len(matrices)==97 and C==2**104,'fixed fixture')
    return initial,matrices,C


def apply(matrix, row): return [sum(a*z for a,z in zip(r,row)) for r in matrix]


def affine_sides(matrix, offset, q, next_q):
    left,right = [],[]
    for row,new in zip(matrix,next_q):
        correction = 1-sum(row)
        left.append(new+sum(-a*z for a,z in zip(row,q) if a<0)
                    +offset*max(-correction,0))
        right.append(sum(a*z for a,z in zip(row,q) if a>0)
                     +offset*max(correction,0))
    return left,right


def probe_masks():
    cases = 0
    for D in (2,4,8):
        b = 128*D
        for length in range(1,5):
            for flags in itertools.product((0,1),repeat=length):
                E = pack(flags,b)
                mask = (D-1)*E
                for _ in range(16):
                    digits = [RNG.randrange(D+2) for _ in range(length)]
                    candidate = pack(digits,b)
                    expected = all(0<=d<D and (f or d==0) for d,f in zip(digits,flags))
                    check(subset(mask,candidate)==expected,'mask equivalence')
                    cases += 1
                check(not subset(mask,b**length),'above-horizon digit')
    return cases


def probe_selectors():
    cases = 0
    for h in (1,2,3):
        b = 512
        R = pack([1]*h,b)
        for bits in itertools.product((0,1),repeat=3*h):
            E = [pack(bits[i*h:(i+1)*h],b) for i in range(3)]
            actual = sum(E)==R
            expected = all(sum(bits[i*h+t] for i in range(3))==1 for t in range(h))
            check(actual==expected,'selector exactness')
            cases += 1
    # Without the radix hypothesis a carry can fake a missing next-time choice.
    check(1+1+1==pack([1,1],2),'small-radix selector counterexample')
    return cases


def probe_partition():
    cases = 0
    for h in range(1,5):
        D,b = 8,1024
        for choices in itertools.product(range(3),repeat=h):
            E = [pack([int(c==i) for c in choices],b) for i in range(3)]
            for _ in range(8):
                digits = [RNG.randrange(D) for _ in range(h)]
                slices = [pack([d if c==i else 0 for d,c in zip(digits,choices)],b)
                          for i in range(3)]
                for i in range(3):
                    check(subset((D-1)*E[i],slices[i]),'slice support')
                    check(slices[i] == (pack(digits,b)&((b-1)*E[i])),'slice equals AND')
                check(sum(slices)==pack(digits,b),'slice reconstruction')
                cases += 1
    return cases


def probe_chronology():
    cases = 0
    D,b = 2,256
    for h in range(1,5):
        digits = list(itertools.product(range(D),repeat=h))
        for pre,post,first,last in itertools.product(digits,digits,range(D),range(D)):
            equation = b*pack(post,b)+first == pack(pre,b)+(b**h)*last
            intended = pre[0]==first and pre[1:]==post[:-1] and post[-1]==last
            check(equation==intended,'literal chronology')
            cases += 1
    return cases


def probe_actual_local(matrices,C):
    cases = 0
    for matrix in matrices:
        for _ in range(32):
            z = [RNG.randrange(-20,21) for _ in range(4)]
            next_z = apply(matrix,z)
            H = 1 << max(2,max(abs(v) for v in z+next_z).bit_length()+1)
            D,b = 2*H,2*H*C
            q,nq = [zv+H for zv in z],[zv+H for zv in next_z]
            left,right = affine_sides(matrix,H,q,nq)
            check(left==right,'actual local affine transition')
            check(all(0<=v<b for v in left+right),'actual local carry bound')
            mutant = list(nq)
            mutant[RNG.randrange(4)] += 1
            ml,mr = affine_sides(matrix,H,q,mutant)
            check(ml!=mr,'wrong local transition accepted')
            # Independently check arbitrary pre/post offsets, including extremal digits.
            q2 = [RNG.choice((0,D-1,RNG.randrange(D))) for _ in range(4)]
            nq2 = [RNG.choice((0,D-1,RNG.randrange(D))) for _ in range(4)]
            ll,rr = affine_sides(matrix,H,q2,nq2)
            check(all(0<=v<b for v in ll+rr),'arbitrary candidate carry bound')
            decoded = apply(matrix,[v-H for v in q2]) == [v-H for v in nq2]
            check((ll==rr)==decoded,'offset signed equivalence')
            cases += 1
    return cases


def probe_actual_histories(initial,matrices,C):
    cases = 0
    maximum_bits = 0
    # These are new random branch words, never the receipt's accepting schedules.
    for x in (1,2,3):
        for tiles in range(5):
            for _ in range(8):
                choices = [0]*x+[RNG.randrange(1,97) for _ in range(tiles)]
                h = len(choices)
                rows = [list(initial)]
                for c in choices: rows.append(apply(matrices[c],rows[-1]))
                counters = [x-min(t,x) for t in range(h+1)]
                magnitude = max(abs(v) for row in rows for v in row)
                H = 1 << (max(magnitude,x,35426321).bit_length()+1)
                D,b,W = 2*H,2*H*C,(2*H*C)**h
                maximum_bits = max(maximum_bits,magnitude.bit_length())
                R = pack([1]*h,b)
                E = [pack([int(c==i) for c in choices],b) for i in range(97)]
                U = [pack([row[r]+H for row in rows[:-1]],b) for r in range(4)]
                V = [pack([row[r]+H for row in rows[1:]],b) for r in range(4)]
                Q = [[pack([row[r]+H if c==i else 0 for row,c in zip(rows,choices)],b)
                      for r in range(4)] for i in range(97)]
                N,Vn = pack(counters[:-1],b),pack(counters[1:],b)
                check((b-1)*R+1==W and sum(E)==R,'history controls')
                check(all(subset(R,e) for e in E),'selector masks')
                for i in range(97):
                    check(all(subset((D-1)*E[i],q) for q in Q[i]),'history slices')
                for r in range(4):
                    check(sum(Q[i][r] for i in range(97))==U[r],'history reconstruction')
                    check(subset((D-1)*R,V[r]),'post mask')
                    check(b*V[r]+H+initial[r]==U[r]+W*(rows[-1][r]+H),'history chronology')
                    left,right = V[r],0
                    for i,matrix in enumerate(matrices):
                        for s,a in enumerate(matrix[r]):
                            if a<0: left += (-a)*Q[i][s]
                            else: right += a*Q[i][s]
                        correction = 1-sum(matrix[r])
                        if correction<0: left += H*(-correction)*E[i]
                        else: right += H*correction*E[i]
                    check(left==right,'packed affine identity')
                check(subset((D-1)*E[0],N),'loader-only counter mask')
                check(subset((D-1)*R,Vn),'post-counter mask')
                check(b*Vn+x==N and N==Vn+E[0],'counter chronology/update')
                check((rows[-1][0]+H==rows[-1][2]+H)==(rows[-1][0]==rows[-1][2]),'endpoint0')
                check((rows[-1][1]+H==rows[-1][3]+H)==(rows[-1][1]==rows[-1][3]),'endpoint1')
                cases += 1
    return dict(cases=cases,maximum_row_bits=maximum_bits)


def probe_counter():
    cases,accepted = 0,0
    D,b = 8,1024
    # Arbitrary natural pre/post histories and arbitrary branch words, not just valid paths.
    for h in (1,2,3):
        for x in (1,2,3):
            for choices in itertools.product((0,1),repeat=h):
                E0 = pack([int(c==0) for c in choices],b)
                R = pack([1]*h,b)
                for state in itertools.product(range(4),repeat=h-1):
                    values = (x,)+state+(0,)
                    N,V = pack(values[:-1],b),pack(values[1:],b)
                    conditions = (subset((D-1)*E0,N) and subset((D-1)*R,V)
                                  and b*V+x==N and N==V+E0)
                    intended = all((a==a1+1 if c==0 else a==a1==0)
                                   for a,a1,c in zip(values,values[1:],choices))
                    check(conditions==intended,'counter exactness')
                    if conditions:
                        check(choices==(0,)*x+(1,)*(h-x),'wrong countdown phase')
                        accepted += 1
                    cases += 1
    return dict(cases=cases,accepted=accepted)


if __name__=='__main__':
    RNG = random.Random(20261004)
    initial,matrices,C = fixed_data()
    receipt = dict(mask_cases=probe_masks(),selector_cases=probe_selectors(),
                   partition_cases=probe_partition(),chronology_cases=probe_chronology(),
                   actual_local_cases=probe_actual_local(matrices,C),
                   actual_fresh_histories=probe_actual_histories(initial,matrices,C),
                   counter_cases=probe_counter(),
                   predecessor_code_executed=False,saved_schedules_executed=False,
                   complete_Pell_witnesses_materialized=False,
                   source_receipt_sha256=RECEIPT_SHA,
                   checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'evidence/semantic-checks.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps(receipt,sort_keys=True,indent=2))
