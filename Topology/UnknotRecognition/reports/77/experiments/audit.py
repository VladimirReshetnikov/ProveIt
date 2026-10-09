"""Reproducible finite exhaustive and randomized mathematical audits."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import random
from boundary_kernel.binary import symplectic, rank, optimal_characters


def cover_audit(g):
    # For g=2,3 every proper symplectic splitting has a side of dimension 2.
    planes=set()
    for u in range(1,1<<(2*g)):
        for v in range(u+1,1<<(2*g)):
            if symplectic(u,v,g): planes.add(tuple(sorted((0,u,v,u^v))))
    splits=set()
    for u in planes:
        w=tuple(x for x in range(1<<(2*g)) if all(not symplectic(x,y,g) for y in u))
        splits.add(tuple(sorted((u,w))))
    splits=sorted(splits)
    full=(1<<len(splits))-1
    masks={}
    for a in range(1,1<<(2*g)):
        masks[a]=sum(1<<j for j,(u,w) in enumerate(splits) if a not in u and a not in w)
    counts=[]
    for m in range(g+1):
        tested=0
        for family in itertools.combinations(masks,m):
            cover=0
            for a in family: cover |= masks[a]
            assert cover != full, (g,family)
            tested+=1
        counts.append(tested)
    optimal=optimal_characters(g)
    cover=0
    for a in optimal: cover |= masks[a]
    assert cover == full
    # A completely independent rank criterion: a nonzero component on each side.
    incidence_checks=0
    for a,mask in masks.items():
        for j,(u,w) in enumerate(splits):
            mixed=any(symplectic(a,x,g) for x in u) and any(symplectic(a,x,g) for x in w)
            assert mixed == bool((mask>>j)&1)
            incidence_checks+=1
    return dict(genus=g, symplectic_planes=len(planes), unordered_splittings=len(splits),
                families_checked_by_size=counts, families_checked=sum(counts),
                all_families_of_size_at_most_g_fail=True,
                supplied_optimal_family=optimal, optimal_family_covers_all=True,
                independent_incidence_checks=incidence_checks)


def transvection(x,v,g): return x ^ (v if symplectic(x,v,g) else 0)


def random_splittings():
    rng=random.Random(20261009)
    cases=0; pairs=0; ranks=0
    for g in range(2,13):
        for _ in range(100):
            basis=[1<<j for j in range(2*g)]
            for __ in range(4*g):
                v=rng.randrange(1,1<<(2*g))
                basis=[transvection(x,v,g) for x in basis]
            for i in range(2*g):
                for j in range(2*g):
                    assert symplectic(basis[i],basis[j],g) == int((i^1)==j)
                    pairs+=1
            h=rng.randrange(1,g)
            u,w=basis[:2*h],basis[2*h:]
            assert any(any(symplectic(a,x,g) for x in u) and any(symplectic(a,x,g) for x in w)
                       for a in optimal_characters(g))
            # Wedge matrix of a symplectic h-plane, and the complementary matrix.
            matrix=[0]*(2*g)
            for a,b in zip(u[::2],u[1::2]):
                for i in range(2*g):
                    matrix[i] ^= (b if (a>>i)&1 else 0) ^ (a if (b>>i)&1 else 0)
            assert rank(matrix)==2*h
            assert rank([row^(1<<(i^1)) for i,row in enumerate(matrix)])==2*(g-h)
            ranks+=2; cases+=1
    return dict(seed=20261009,cases=cases,symplectic_pair_checks=pairs,
                genus_rank_checks=ranks,all_optimal_families_detect=True)


def complete_bank_audit():
    from boundary_kernel.cover_bank import analyze_bank
    g=2
    planes=set()
    for u in range(1,16):
        for v in range(u+1,16):
            if symplectic(u,v,g): planes.add(tuple(sorted((0,u,v,u^v))))
    splits=set()
    for u in planes:
        w=tuple(x for x in range(16) if all(not symplectic(x,y,g) for y in u))
        splits.add(tuple(sorted((u,w))))
    splits=sorted(splits)
    masks={a:sum(1<<i for i,(u,w) in enumerate(splits) if a not in u and a not in w)
           for a in range(1,16)}
    full=(1<<len(splits))-1
    universal_counts=[0]*16
    for bankmask in range(1<<15):
        bank=[j+1 for j in range(15) if (bankmask>>j)&1]
        coverage=0
        for a in bank: coverage|=masks[a]
        expected=coverage==full
        got=analyze_bank(2,bank)['universal_for_separating_simple_curves']
        assert got==expected,(bank,got,expected)
        universal_counts[len(bank)]+=int(got)
    return dict(genus=2,all_banks_checked=1<<15,
                universal_banks_by_cardinality=universal_counts,
                comparison='coisotropic interaction criterion vs literal coverage of all 10 splittings')


def run(output):
    data={'schema':'boundary-kernel-audit-v1','exhaustive_covers':[cover_audit(2),cover_audit(3)],
          'random_splittings':random_splittings(), 'bank_criterion':complete_bank_audit(),
          'scope':'Exact finite algebra audits, not native knot diagrams or a proof assistant.'}
    Path(output).write_text(json.dumps(data,indent=2)+'\n')
    return data


if __name__ == '__main__':
    import argparse
    p=argparse.ArgumentParser(); p.add_argument('--output',default='results/audit.json')
    args=p.parse_args(); print(json.dumps(run(args.output),indent=2))
