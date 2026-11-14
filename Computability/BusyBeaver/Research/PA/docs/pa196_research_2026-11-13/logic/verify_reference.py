#!/usr/bin/env python3
"""Small positive/negative checks of the explicit native HA reference kernel.

These are implementation checks, not a formal proof of the HA equivalence.
"""
import copy
import json
from pathlib import Path
from native_ha_checker import Z, Reject, verify, substitute, same, progress_mode


def var(n):
    return ['v', n]


def succ(t):
    return ['s', t]


def eq(s, t):
    return ['e', s, t]


def refl(t):
    p = ['zero', t, 400, Z]
    return ['tr', p, p, 401, eq(var(401), t)]


def symmetric(p, left):
    return ['tr', p, refl(left), 402, eq(var(402), left)]


def transitive(p, q, left):
    return ['tr', q, p, 403, eq(left, var(403))]


def atom_family(t):
    # Q_v [ t = I(v,t;u.Su) ]. Its zero instance follows by computation.
    return ['q', 200, eq(t, ['i', var(200), t, 201, succ(var(201))])]


def compound_progress_packet():
    x, y, z = 100, 101, 102
    zz = var(z)
    one = succ(Z)
    h = succ(var(201))
    i0 = ['i', Z, zz, 201, h]
    i1 = ['i', one, zz, 201, h]
    pzero = ['zero', zz, 201, h]  # I(0,z;u.Su)=z
    pbase = symmetric(pzero, i0)  # z=I(0,z;u.Su)
    pqe = ['qe', ['hyp', 0], pbase, one]  # z=I(1,z;u.Su)
    pstep = ['succ', Z, zz, 201, h]  # I(1,z;u.Su)=S(I(0,z;u.Su))
    psucc = ['tr', pzero, pstep, 404, eq(i1, succ(var(404)))]
    zeqsz = transitive(pqe, psucc, zz)
    branch = ['tr', zeqsz, ['hyp', 0], 405, atom_family(var(405))]
    body = atom_family(var(y))
    return {'logic': 'ha', 'context': [], 'goal': ['d', x, y, body],
            'proof': ['di', x, y, body, Z, z, branch]}


def accepted(packet):
    try:
        return verify(packet)
    except Reject:
        return False


def main():
    compound = compound_progress_packet()
    control = copy.deepcopy(compound)
    control['logic'] = 'ipra'
    invalid_goal = {'goal': eq(Z, succ(Z)), 'proof': refl(Z)}
    fresh_failure = copy.deepcopy(compound)
    fresh_failure['context'] = [eq(var(102), var(102))]
    # Re-index the inherited local hypothesis after adding a context entry.
    # Freshness fails before proof inspection, so no re-indexing is needed.
    original = ['q', 1, eq(var(0), var(1))]
    substituted = substitute(original, {0: var(1)})
    expected = ['q', 2, eq(var(1), var(2))]
    rows = {
        'reflexivity_zero': accepted({'goal': eq(Z, Z), 'proof': refl(Z)}),
        'false_goal_rejected': not accepted(invalid_goal),
        'compound_progress_accepted_ha': accepted(compound),
        'same_packet_rejected_ipra_control': not accepted(control),
        'eigenvariable_capture_rejected': not accepted(fresh_failure),
        'capture_avoiding_substitution': same(substituted, expected),
        'ha_compound_zero_selects_progress': progress_mode(atom_family(Z), Z, 'ha'),
        'ipra_compound_zero_selects_case': not progress_mode(atom_family(Z), Z, 'ipra'),
        'nonliteral_zero_selects_case': not progress_mode(atom_family(Z), ['i', Z, Z, 2, Z], 'ha'),
    }
    result = {'checks': rows, 'all_passed': all(rows.values()),
              'scope': 'Reference implementation checks only; no formal metatheorem or TM state bound.'}
    root = Path(__file__).resolve().parent
    (root / 'compound_progress_certificate.json').write_text(json.dumps(compound, indent=2) + '\n')
    (root / 'reference_receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return 0 if result['all_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
