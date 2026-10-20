"""Independent finite facts for Source147's matrix and all membership fourth inputs.

No delivered checker, parser, proof assistant or search is imported. The native
rows below are transcribed explicitly and independently reviewed against C222.
The all-natural valuation and derivation inductions are in proof.md.
"""
from pathlib import Path
from itertools import product
from math import isqrt
import argparse
import hashlib
import json


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--model', type=Path, default=Path(__file__).with_name('model.json'))
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    raw = args.model.read_bytes()
    pin = hashlib.sha256(raw).hexdigest()
    assert pin == '639477b266ca069ae8298568d447c06a53924e4981e106434db9039b8f85f2d8'
    model = json.loads(raw)
    carrier = range(5)
    designated = set(model['D'])
    assert designated == {3, 4} and (model['T'], model['F'], model['eq']) == (4, 2, 3)
    I = lambda a, b: model['table'][a][b]
    R = lambda a, b: 2
    E = lambda a, b: 3
    Q = lambda a, b: model['Q'][b]
    N = lambda a: I(a, 2)
    Ex = lambda a, b: N(Q(a, N(b)))
    sub = lambda a, b, k: Q(k, I(R(k, a), R(k, b)))
    req = lambda b, k, m: Q(b, I(m, N(Q(b, I(m, N(R(b, k)))))))
    clos = lambda a, b, k, m: Q(b, I(R(b, k), N(Q(a, I(m, N(Q(a, I(sub(a, b, k), req(b, k, m)))))))))
    nks = lambda a, b, c: Q(c, I(clos(a, b, c, c), N(req(b, c, c))))
    vrel = lambda a, b, c: I(R(a, b), Q(c, R(a, b)))
    bundle = lambda a, b, c: N(I(vrel(a, b, c), nks(a, b, c)))
    rho8 = lambda a, b, c, u: I(I(I(c, u), a), I(I(a, c), I(b, c)))
    rows = {
        'rho1': (2, lambda a, b: Ex(a, E(a, b))),
        'rho2': (3, lambda a, b, c: I(Q(a, I(b, c)), I(Q(a, b), Q(a, c)))),
        'rho3': (3, lambda a, b, c: I(E(a, b), I(R(c, a), R(c, b)))),
        'rho4': (3, lambda a, b, c: I(Q(a, Q(b, c)), Q(b, Q(a, c)))),
        'rho5': (3, lambda a, b, c: I(E(c, a), I(R(c, b), R(a, b)))),
        'rho6': (2, lambda a, b: I(Ex(a, Q(a, b)), b)),
        'G': (3, lambda a, b, c: I(E(c, a), I(E(c, b), Q(R(a, b), E(a, b))))),
        'bundle_without_gate': (3, bundle),
        'rho8_any_membership_fourth': (3, lambda a, b, c: rho8(a, b, c, 2)),
    }
    receipts = {}
    for name, (arity, formula) in rows.items():
        values = [formula(*args) for args in product(carrier, repeat=arity)]
        assert set(values) <= designated, (name, sorted(set(values)))
        receipts[name] = dict(cases=len(values), output_values=sorted(set(values)))
    assert all(a not in designated or I(a, b) not in designated or b in designated for a, b in product(carrier, repeat=2))
    assert all(a not in designated or Q(0, a) in designated for a in carrier)
    assert I(4, 4) == 4 and 4 in designated and 2 not in designated
    assert all(I(a, a) in designated for a in carrier) and 3 in designated
    # Separate small native-code diagnostics; they do not replace the induction.
    value = [4]
    for code in range(1, 213):
        pair, tag = divmod(code, 4)
        diagonal = (isqrt(8 * pair + 1) - 1) // 2
        right = pair - diagonal * (diagonal + 1) // 2
        left = diagonal - right
        assert left <= pair < code and right <= pair
        value.append(I(value[left], value[right]) if tag == 0 else 2 if tag == 1 else Q(left, value[right]) if tag == 2 else 3)
    assert [value[n] for n in [8, 10, 1, 3, 0]] == [0, 1, 2, 3, 4]
    assert value[52] == value[212] == 1
    unrestricted_failures = [list(x) for x in product(carrier, repeat=4) if rho8(*x) not in designated]
    assert unrestricted_failures
    result = dict(status='FINITE_MATRIX_FACTS_PASS', model_sha256=pin,
        schemas=receipts, schema_cases=sum(x['cases'] for x in receipts.values()),
        modus_ponens_cases=25, generalization_cases=5, zero_alias_checked=True,
        native_code_diagnostics=213, extra_equality_and_identities=True,
        unrestricted_rho8_failures=len(unrestricted_failures),
        EFQ_counterexample=dict(code=52, value=value[52]), K_counterexample=dict(code=212, value=value[212]),
        extension='Every native membership atom has value2, so any collection of membership-fourth rho8 instances shares the same125-case certificate.',
        scope='Finite matrix facts and bounded native-code diagnostics. Primitive-recursive total valuation and PA-formalizable proof induction are ordinary arguments in proof.md, not a Lean/Rocq kernel result.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
