"""Create the exact small examples used to explain the general proofs."""
import json
from pathlib import Path
import sys


def main():
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0,str(root))
    from activation_forests import from_dense, solve_output, verify_output
    examples = {
        'triangle': from_dense(3,[[0,1],[1,2],[2,0]],[[1],[1],[1]]),
        'parallel_obstruction': from_dense(2,[[0,1]]*3,[[1],[1],[1]]),
        'shared_witness': from_dense(2,[[0,1],[0,1],[0,1],[0,0]],
            [[1,1,2,0],[1,0,0,1],[0,1,0,1],[0,0,1,1]]),
        'unsupported_cycle': from_dense(1,[None]*4,
            [[0,0,1,1],[1,0,1,0],[0,0,1,1],[0,1,0,1]]),
        'parity_without_matroid_exchange': from_dense(4,
            [[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]],
            [[1,0,0],[0,1,0],[1,1,0],[0,0,1],[1,0,1],[0,1,1]])}
    for name,problem in examples.items():
        result=solve_output(problem)
        assert verify_output(problem,result)
        (root/'examples'/f'{name}.json').write_text(json.dumps({
            'scope':'Exact finite example, not an asserted native triangulation.',
            'problem':problem,'result':result},indent=2)+'\n')
    print({'examples':len(examples),'verified':True})


if __name__=='__main__':
    main()
