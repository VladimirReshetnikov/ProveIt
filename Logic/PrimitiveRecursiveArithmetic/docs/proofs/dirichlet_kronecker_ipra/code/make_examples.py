"""Reproduce the archive's exact-rational demonstration certificates."""
from fractions import Fraction as F
from pathlib import Path
import json
from approximation import (
    rational_name, sqrt_name, dirichlet_scalar, dirichlet_simultaneous,
    unbounded_denominator, rational_compatibility, kronecker_search,
    kronecker_positive, jsonable,
)


def main():
    out = Path(__file__).resolve().parents[1] / 'examples'
    out.mkdir(exist_ok=True)
    matrix = [[F(1, 3), F(1, 5)], [F(1, 2), F(1, 7)]]
    target = [F(1, 6), F(2, 35)]
    compatible = rational_compatibility(matrix, target)
    assert compatible['compatible']
    examples = {
        'scalar_sqrt2_N100': dirichlet_scalar(sqrt_name(2), 100),
        'simultaneous_sqrt2_sqrt3_N100': dirichlet_simultaneous(
            [sqrt_name(2), sqrt_name(3)], 100),
        'padding_rational_half_B17': unbounded_denominator(rational_name(F(1,2)), 17),
        'kronecker_rational_matrix': {
            'matrix': matrix, 'target': target, 'compatibility': compatible,
            'witness': kronecker_search(
                [[rational_name(x) for x in row] for row in matrix],
                [rational_name(x) for x in target], 50, compatible['C']),
        },
        'kronecker_exact_obstruction': {
            'matrix': [[F(1,2), F(1,2)]], 'target': [F(0),F(1,2)],
            'certificate': rational_compatibility([[F(1,2),F(1,2)]], [F(0),F(1,2)]),
        },
        'kronecker_sqrt2_target_half': kronecker_positive(
            sqrt_name(2), rational_name(F(1,2)), 100, lambda H: 4*H, B=100),
    }
    for name, result in examples.items():
        (out/(name+'.json')).write_text(json.dumps(jsonable(result),indent=2)+'\n')
        if 'witness' in result:
            witness=result['witness']
        else:
            witness=result
        print(name, 'q=',witness.get('q'), 'p=',witness.get('p'))
    print('Wrote',len(examples),'exact-rational example files.')


if __name__ == '__main__':
    main()
