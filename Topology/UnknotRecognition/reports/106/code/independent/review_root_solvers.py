"""Independent finite-instance cross-check of the delivered root solvers."""
from pathlib import Path
import argparse
import json
import sys
from random import Random
from collections import Counter
sys.path.insert(0, str(Path(__file__).resolve().parent))
from independent_exceptional_audit import trees,peels

def dense(problem):
    result=[[0]*problem['columns'] for _ in problem['rows']]
    for r,row in enumerate(problem['rows']):
        for c,a in row:result[r][c]=a
    return result

def expected(problem):
    edges=[(0,0) if e is None else tuple(e) for e in problem['edges']]
    matrix=dense(problem)
    return any(peels(matrix,t) for t in trees(problem['vertices'],edges))

def check_success(problem,result):
    if result['status']!='SUCCESS':return
    cert=result['certificate'];chosen=cert['tree'];live=set(range(len(problem['rows'])))-set(chosen)
    edges=[(0,0) if e is None else tuple(e) for e in problem['edges']]
    assert frozenset(chosen) in list(trees(problem['vertices'],edges))
    matrix=dense(problem)
    used=set()
    for r,c in cert['peeling']:
        assert r in live and c not in used and matrix[r][c]==1
        assert sum(matrix[u][c] for u in live)==1
        live.remove(r);used.add(c)
    assert not live

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast',type=Path,required=True,
                        help='directory containing the triple_forest_research package')
    parser.add_argument('--native',type=Path,required=True,
                        help='native_core_sources.json produced by the native source exporter')
    parser.add_argument('--output',type=Path,
                        default=Path(__file__).with_suffix('.json'),
                        help='JSON report path (default: beside this script)')
    args=parser.parse_args(argv)
    fast=args.fast.resolve()
    if not (fast/'triple_forest_research'/'nonlinear.py').is_file():
        parser.error('--fast must contain triple_forest_research/nonlinear.py')
    if not args.native.is_file():
        parser.error('--native must name an existing native source JSON file')
    sys.path.insert(0,str(fast))
    from triple_forest_research.nonlinear import solve_boolean,solve_width

    rng=Random(202610126729)
    random_counts=Counter()
    for case in range(650):
        n=rng.randint(1,5);m=rng.randint(max(1,n-1),8)
        edges=[(i,rng.randrange(i))for i in range(1,n)]
        edges += [((rng.randrange(n),rng.randrange(n))if rng.randrange(5) else None)
                  for _ in range(m-len(edges))]
        columns=[]
        for _ in range(rng.randrange(8)):
            values=[0]*m
            for r in rng.sample(range(m),rng.randrange(min(m,5)+1)):
                values[r]=rng.choice([1,1,1,2,3])
            columns.append(values)
        matrix=[[c[r] for c in columns]for r in range(m)]
        problem=dict(vertices=n,columns=len(columns),edges=edges,
                     rows=[[[c,a]for c,a in enumerate(row)if a]for row in matrix])
        want=expected(problem)
        a=solve_width(problem,max_work=50000000)
        b=solve_boolean(problem,seed=case+4321,max_work=50000000,trials=2)
        assert (a['status']=='SUCCESS')==want,(case,a,problem)
        assert a['status'] in ['SUCCESS','NO_FOREST'],(case,a)
        assert (b['status']=='SUCCESS')==want,(case,b,problem)
        check_success(problem,a);check_success(problem,b)
        random_counts[str(want)]+=1
    corpus=json.loads(args.native.read_text())
    rows=[];native_counts=Counter()
    for item in corpus['cases']:
        pair=[]
        for name in ['problem','optimized_problem']:
            problem=item[name];want=expected(problem)
            answer=solve_width(problem,max_work=50000000)
            assert (answer['status']=='SUCCESS')==want,(item['id'],name,answer)
            assert answer['status']in['SUCCESS','NO_FOREST']
            check_success(problem,answer)
            pair.append(answer['status'])
            native_counts[name+'_'+answer['status']]+=1
        if pair[0]!=pair[1]:
            rows.append(dict(id=item['id'],canonical=pair[0],optimized=pair[1]))
    result=dict(scope='Finite supplied graph/matrix validation; source authentication performed by separate native exporter',
                seed=202610126729, random_cases=650,random_feasibility=dict(random_counts),
                random_contract='arbitrary exceptional support up to five and counts 1,2,3; includes loops and unavailable rows',
                all_root_algorithms_match_independent_tree_enumeration=True,
                all_successes_independently_replayed=True,
                native_problem_pairs=len(corpus['cases']),native_counts=dict(native_counts),
                native_lower_forest_coverage_changes=rows)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
