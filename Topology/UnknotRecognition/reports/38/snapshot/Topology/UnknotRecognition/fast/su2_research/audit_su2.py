"""Reproduce finite-group, independent-cube, and compressed-formula audits."""
import argparse
from itertools import permutations, product
import json
from pathlib import Path
import random
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT.parent/'reports/26'))
from fastunknot.diagram import Diagram
from fastunknot.su2 import (bridge_presentation, wirtinger_presentation,
    simplify_presentation, su2_decide)
from detshadow.diagram import Diagram as CubeDiagram
from detshadow.cube import reduced_homology


def group_count(generators, relators):
    elements = tuple(permutations(range(3)))
    index = {p:i for i,p in enumerate(elements)}
    multiply = [[index[tuple(a[b[i]] for i in range(3))] for b in elements] for a in elements]
    inverse = [index[tuple(p.index(i) for i in range(3))] for p in elements]
    count = 0
    for values in product(range(6), repeat=len(generators)):
        images = dict(zip(generators,values))
        valid = True
        for word in relators:
            value = 0
            for letter in word:
                image = images[abs(letter)]
                value = multiply[value][inverse[image] if letter < 0 else image]
            if value:
                valid = False
                break
        count += valid
    return count


def fox_nullity(generators, relators, prime=3):
    # Reflection multiplication in Dih(F_p) gives the alternating color sum
    # on every even-length relator. Inverses of reflections are themselves.
    columns = {g:i for i,g in enumerate(generators)}
    rows = []
    for word in relators:
        if len(word) % 2:
            raise ValueError('reflection relator has odd length')
        row = [0]*len(generators)
        for i,letter in enumerate(word):
            row[columns[abs(letter)]] += 1 if i % 2 == 0 else -1
        rows.append([x % prime for x in row])
    rank = 0
    for col in range(len(generators)):
        pivot = next((i for i in range(rank,len(rows)) if rows[i][col]),None)
        if pivot is None:
            continue
        rows[rank],rows[pivot] = rows[pivot],rows[rank]
        inverse = pow(rows[rank][col],-1,prime)
        rows[rank] = [x*inverse % prime for x in rows[rank]]
        for i in range(rank+1,len(rows)):
            factor = rows[i][col]
            rows[i] = [(x-factor*y) % prime for x,y in zip(rows[i],rows[rank])]
        rank += 1
    return len(generators)-rank


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=ROOT/'results/su2_audit.json')
    parser.add_argument('--count',type=int,default=48)
    parser.add_argument('--seconds',type=float,default=0.3)
    args = parser.parse_args()
    randomizer = random.Random(20261008)
    inputs = []
    while len(inputs) < args.count:
        strands = randomizer.randrange(2,5)
        word = [randomizer.choice((-1,1))*randomizer.randrange(1,strands)
                for _ in range(randomizer.randrange(1,8))]
        try:
            diagram = Diagram.from_braid(strands,word)
        except ValueError:
            continue
        if len(inputs) % 3 == 0:
            diagram = diagram.mirror()
        inputs.append((strands,word,diagram))
    checks, finite = [], []
    start = perf_counter()
    for strands,word,diagram in inputs:
        oracle = reduced_homology(CubeDiagram(diagram.pd))
        expected = 'UNKNOT' if oracle['rank'] == 1 else 'KNOTTED'
        for presentation in ('bridge','tietze'):
            answer = su2_decide(diagram,presentation=presentation,seconds=args.seconds,
                                trace_zero_probe=True)
            status = answer['status']
            if status != 'INCONCLUSIVE' and status != expected:
                raise AssertionError((word,presentation,answer,oracle))
            checks.append(dict(pd=diagram.pd,source_word=word,source_strands=strands,
                               presentation=presentation,expected=expected,
                               oracle_rank=oracle['rank'],answer=answer))
        if diagram.crossings <= 5:
            gens,rels = wirtinger_presentation(diagram)
            b = bridge_presentation(diagram)
            brels = [tuple(w)+(s,)+tuple(-x for x in reversed(w))+(-t,)
                     for s,t,w in b['conjugacies']]
            simplified = simplify_presentation(gens,rels)
            counts = [group_count(gens,rels), group_count(b['generators'],brels),
                      group_count(simplified['generators'],simplified['relators'])]
            if len(set(counts)) != 1:
                raise AssertionError((word,counts))
            finite.append(dict(pd=diagram.pd,homomorphisms_to_S3=counts[0]))
    prime_family = []
    for m in (3,5,7,11,21,51):
        diagram = Diagram.from_rational(0,[[0,3]]*m)
        gens,rels = wirtinger_presentation(diagram)
        nullity = fox_nullity(gens,rels)
        assert diagram.crossings == 3*m and nullity == m
        prime_family.append(dict(twist_boxes=m,crossings=diagram.crossings,
                                 fox3_dimension=nullity,group_rank_lower_bound=m))
    report = dict(seed=20261008,seconds_per_solver=args.seconds,diagrams=len(inputs),
                  queries=len(checks),completed=sum(c['answer']['status']!='INCONCLUSIVE' for c in checks),
                  inconclusive=sum(c['answer']['status']=='INCONCLUSIVE' for c in checks),
                  mismatches=0,finite_group_diagrams=len(finite),
                  elapsed_seconds=perf_counter()-start,checks=checks,
                  finite_group_checks=finite,prime_pretzel_family=prime_family)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('checks','finite_group_checks')},indent=2))


if __name__ == '__main__':
    main()
