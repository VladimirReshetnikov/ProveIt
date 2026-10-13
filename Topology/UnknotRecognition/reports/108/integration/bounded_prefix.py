"""Polynomial incumbent prefix followed by the exact FPT forest fallback.

The incumbent is the pinned incoming Dual Forest Normalization implementation.
Each of its search nodes has polynomial work. Limiting it to m+1 nodes retains
the FPT bound of the fallback, where m is the number of supplied rows.
This is an optional research dispatcher, not a maintained recognizer change.
"""
from activation_forests.model import parse_problem, integer
from activation_forests.output_solver import solve_output
from reference.dual_forest.dual_forest_search import solve_by_stopping


def solve_prefix(problem, *, max_fallback_work=None):
    if max_fallback_work is not None and (not integer(max_fallback_work) or max_fallback_work < 0):
        raise ValueError('fallback work limit must be a nonnegative integer or None')
    data = parse_problem(problem)
    eligible = sum(e is not None and e[0] != e[1] for e in data.edges)
    limit = len(data.rows) + 1
    # Route an obviously disconnected namespace directly to the output
    # producer and its sparse cut certificate.
    if data.vertices <= eligible + 1:
        result = solve_by_stopping(problem, max_nodes=limit)
        backend = 'incumbent'
    else:
        result = {'status': 'INCONCLUSIVE'}
        backend = 'output'
    if result['status'] == 'INCONCLUSIVE':
        result = solve_output(problem, max_work=max_fallback_work)
        backend = 'output'
    answer = {'status': result['status'], 'method': 'bounded_incumbent_prefix',
              'stats': {'prefix_node_limit': limit, 'backend': backend,
                        'backend_stats': result.get('stats', {})}}
    if result['status'] == 'INCONCLUSIVE':
        answer['reason'] = result.get('reason', 'fallback incomplete')
    else:
        answer['certificate'] = {'schema': 'activation-prefix-v1',
            'input_sha256': data.digest, 'backend': backend, 'result': result}
    return answer
