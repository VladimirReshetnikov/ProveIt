"""Independent parser/convolution/evaluation for the emitted coefficient lists.

No emitter, evaluator, compiler or producer polynomial helper is imported.
Finite sample validation is not a general arbitrary-mass exporter or proof.
"""
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAX_JSON_BYTES = 16 * 1024 * 1024
MAX_VARIABLES = 10000
MAX_ROWS = 10000
MAX_TERMS = 200000
MAX_BITS = 4096
MAX_ROUNDS = 16


def require(ok, detail):
    if not ok:
        raise ValueError(detail)


def exact_int(value, label, minimum=None):
    require(type(value) is int and abs(value).bit_length() <= MAX_BITS, label + ': exact bounded integer required')
    if minimum is not None:
        require(value >= minimum, label + ': below minimum')
    return value


def read_json(path):
    raw = Path(path).read_bytes()
    require(len(raw) <= MAX_JSON_BYTES, 'JSON byte limit')
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=unique)


def preflight(data, witness):
    require(type(data) is dict and type(witness) is list, 'artifact/witness shape')
    T = exact_int(data['T'], 'T', 0)
    K = exact_int(data['K'], 'K', 0)
    require(T + K <= MAX_ROUNDS, 'practical round limit exceeded')
    inputs = data['input_values']
    require(type(inputs) is list and len(inputs) == 3, 'three natural input coordinates required')
    require(type(data['input_count']) is int and data['input_count'] == 3, 'input arity type')
    require(len(inputs) + len(witness) <= MAX_VARIABLES, 'variable limit')
    for v in inputs + witness:
        exact_int(v, 'natural value', 0)
    target = data['target']
    require(type(target) is list and len(target) == 2, 'two target coordinates required')
    for v in target:
        exact_int(v, 'target')
    require(target[0] < target[1], 'target order')
    require(type(data['residuals']) is list and len(data['residuals']) <= MAX_ROWS, 'residual count limit')
    require(type(data['variable_names']) is list and len(data['variable_names']) == len(inputs) + len(witness),
            'variable names arity')
    return inputs + witness


def parse_terms(terms, arity, degree):
    require(type(terms) is list and len(terms) <= MAX_TERMS, 'term limit/type')
    result = {}
    order = []
    for term in terms:
        require(type(term) is list and len(term) == 2, 'term shape')
        coefficient, monomial = term
        exact_int(coefficient, 'coefficient')
        require(coefficient != 0, 'zero coefficient')
        require(type(monomial) is list and len(monomial) <= degree, 'monomial degree/type')
        require(all(type(i) is int and 0 <= i < arity for i in monomial), 'variable index')
        key = tuple(monomial)
        require(list(key) == sorted(key) and key not in result, 'monomial canonicality')
        result[key] = coefficient
        order.append(key)
    require(order == sorted(order), 'term ordering')
    return result


def evaluate(poly, values):
    answer = 0
    for indices, coefficient in poly.items():
        term = coefficient
        for i in indices:
            term *= values[i]
        answer += term
    return answer


def check(data, witness):
    values = preflight(data, witness)
    rows = [parse_terms(row, len(values), 2) for row in data['residuals']]
    require(sum(map(len, rows)) <= MAX_TERMS, 'aggregate residual term limit')
    require(sum(len(row) ** 2 for row in rows) <= 1000000, 'convolution work limit')
    expanded = parse_terms(data['expanded_quartic'], len(values), 4)
    computed = defaultdict(int)
    for row in rows:
        for left, a in row.items():
            for right, b in row.items():
                computed[tuple(sorted(left + right))] += a * b
    computed = {key: value for key, value in computed.items() if value}
    require(computed == expanded, 'expanded coefficient list differs from exact residual convolution')
    residual_values = [evaluate(row, values) for row in rows]
    score = sum(v * v for v in residual_values)
    require(score == 0 and evaluate(expanded, values) == score, 'nonzero or inconsistent witness score')
    return dict(status='passed', residuals=len(rows), residual_terms=sum(map(len, rows)),
                expanded_terms=len(expanded), variables=len(values), independent_residual_score=score,
                independent_expanded_score=0)


def main():
    data = read_json(HERE / 'example-polynomial.json')
    witness = read_json(HERE / 'example-witness.json')
    result = check(data, witness)
    result['polynomial_sha256'] = sha256((HERE / 'example-polynomial.json').read_bytes()).hexdigest()
    result['witness_sha256'] = sha256((HERE / 'example-witness.json').read_bytes()).hexdigest()
    (HERE / 'independent-expansion-receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
