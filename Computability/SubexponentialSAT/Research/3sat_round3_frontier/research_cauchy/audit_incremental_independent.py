"""Independent exhaustive completion audit of root-authored balancer."""
from fractions import Fraction
from itertools import product
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('root_incremental', ROOT/'research_balancing/incremental.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def completion_score(A, row_labels, columns, Q, z):
    loads = [[0]*Q for _ in range(Q)]
    for row, a in zip(A, row_labels):
        for w, b in zip(row, columns):
            loads[a][b] += w
    return sum(z**v for row in loads for v in row)


def main():
    counts = dict(fixtures=0, engines=0, candidate_completion_means=0,
                  literal_completions=0)
    matrices = [[list(v[:2]), list(v[2:])] for v in product(range(3), repeat=4)]
    matrices += [[], [[], []], [[0,0,0]], [[7,0,3], [0,5,0]],
                 [[0,0,0], [0,0,0]], [[1,1,1], [1,1,1], [1,1,1]]]
    for A in matrices:
        n = len(A[0]) if A else 0
        for Q in [1,2,3,4]:
            for h in [2,5]:
                results = [module.balance(A,Q,h=h,engine=e,trace=True)
                           for e in ['reference','cached','incremental']]
                counts['engines'] += 3
                for field in ['rows','columns','loads','scores','initial','final','active_pairs','mass']:
                    if any(x[field] != results[0][field] for x in results):
                        raise ValueError(('engine mismatch', A,Q,h,field))
                result = results[-1]
                C = max([sum(row[j] for row in A) for j in range(n)] + [1])
                z = Fraction(h*C+1,h*C)
                prefix = []
                for j in range(n):
                    scores = []
                    for candidate in range(Q):
                        values = []
                        for suffix in product(range(Q), repeat=n-j-1):
                            values.append(completion_score(A,result['rows'],prefix+[candidate]+list(suffix),Q,z))
                        counts['literal_completions'] += len(values)
                        scores.append(sum(values)/len(values))
                        counts['candidate_completion_means'] += 1
                    if tuple(scores) != result['scores'][j]:
                        raise ValueError(('completion expectation mismatch', A,Q,h,j))
                    chosen = min(range(Q), key=lambda b:(scores[b],b))
                    if chosen != result['columns'][j]:
                        raise ValueError('first-label minimizer mismatch')
                    prefix.append(chosen)
                D = result['active_pairs']
                if result['operations']['candidate_terms'] != Q*D:
                    raise ValueError('sparse candidate term count mismatch')
                if results[1]['operations']['candidate_terms'] != n*Q*Q:
                    raise ValueError('cached candidate term count mismatch')
                counts['fixtures'] += 1
    return {'status':'PASS','counts':counts,
            'scope':'Independent local component audit, not SAT runtime evidence',
            'preprocessing_correction':'The matrix prototype also scans Q bins per input row: O(n_rows Q+n_rows n) preprocessing.'}


if __name__ == '__main__':
    print(json.dumps(main(),indent=2,sort_keys=True))
