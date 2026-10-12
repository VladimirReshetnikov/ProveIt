"""Dispatcher certificate replay; imports neither forest producer."""
from activation_forests.model import parse_problem
from activation_forests.output_verify import verify_output
from reference.dual_forest.dual_forest_verify import verify as verify_incumbent


def verify_prefix(problem, result):
    try:
        data = parse_problem(problem)
        if type(result) is not dict or result.get('status') not in ('SUCCESS', 'NO_FOREST'):
            return False
        certificate = result.get('certificate')
        if type(certificate) is not dict or set(certificate) != {
                'schema', 'input_sha256', 'backend', 'result'}:
            return False
        if certificate['schema'] != 'activation-prefix-v1' \
                or certificate['input_sha256'] != data.digest:
            return False
        nested = certificate['result']
        if type(nested) is not dict or nested.get('status') != result['status']:
            return False
        if certificate['backend'] == 'incumbent':
            return bool(verify_incumbent(problem, nested))
        if certificate['backend'] == 'output':
            return verify_output(problem, nested)
        return False
    except (ValueError, TypeError, KeyError, IndexError, AssertionError):
        return False
