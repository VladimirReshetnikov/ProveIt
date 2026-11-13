"""Exercise both checked proof translations on meaningful closed/open cases."""
import json
from pathlib import Path
from translate import translate, translate_proof, old_refl, old, new
from proof_macros import R, S, P, proof, hypothesis, congruence, transport, computation

HERE = Path(__file__).resolve().parent


def main():
    closed = []
    errors = []
    outputs = HERE / 'certificates' / 'translated'
    outputs.mkdir(parents=True, exist_ok=True)
    for path in sorted((HERE / 'certificates').glob('*.json')):
        data = json.loads(path.read_text())
        try:
            new.verify(data)
        except Exception:
            for direction in [False]:
                try:
                    translate(data, direction)
                except Exception:
                    errors.append(path.name)
                else:
                    raise AssertionError(('invalid source accepted', path.name))
            continue
        control = translate(data, False)
        returned = translate(control, True)
        assert returned['goal'] == data['goal']
        assert old.verify(control) and new.verify(returned)
        (outputs / ('control_' + path.name)).write_text(json.dumps(control) + '\n')
        (outputs / ('returned_' + path.name)).write_text(json.dumps(returned) + '\n')
        closed.append(path.name)
    open_cases = []
    for h in [1, S(1), P(1), R(S(1), 1, R(S(3), 1, S(2)))]:
        major = [-1, -2]
        from proof_macros import instantiate
        minor = [instantiate(h, [-1]), -3]
        context = [([0, 0], major), ([0, 0], minor)]
        p = ['x', h, ['u', 0, 0, old_refl(0)], ['u', 1, 0, old_refl(0)]]
        forward = translate_proof(p, context, 3, True)
        back = translate_proof(forward, context, 3, False)
        assert old.derive(back, context, 3) == old.derive(p, context, 3)
        open_cases.append({'template': h, 'same_end_sequent': True})
    report = {'closed_round_trips': len(closed), 'open_round_trips': len(open_cases),
              'invalid_source_rejections': len(errors), 'mismatches': 0,
              'closed_cases': closed, 'open_cases': open_cases, 'rejected': errors}
    evidence = HERE.parent / 'evidence' if (HERE / 'counter_eval.py').exists() else HERE
    evidence.mkdir(exist_ok=True)
    (evidence / 'translation_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('closed_cases','open_cases','rejected')}, indent=2))


if __name__ == '__main__':
    main()
