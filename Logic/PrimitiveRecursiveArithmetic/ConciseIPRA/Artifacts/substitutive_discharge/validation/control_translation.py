"""Replay both exact-goal translations against the matched canonical control."""
import copy
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


K = load('selected_kernel', ROOT / 'code/canonical_checker.py')
C = load('separate_kernel', ROOT / 'code/canonical_separate.py')
V = load('certificate_builder', ROOT / 'validation/canonical_validation.py')


def scopes(a, body, g, n):
    body = K.sub(body, -n - 1, 1)
    return g + [(K.sub(body, 0), body)]


def convert(a, p, g, n, into_control):
    tag = p[0]
    if tag == 'c':
        return copy.deepcopy(p)
    if tag == 'u':
        _, j, t, premise = p
        return ['u', j, t, convert(g[j][0], premise, g, n, into_control)]
    if tag == 'i':
        _, t, branch = p
        body = K.sub(a[0], t, 1)
        hyp = K.sub(body, -n - 1 if len(body) == 2 and t == 0 else 0)
        target = K.sub(body, [0, -n - 1, 0])
        return ['i', t, convert(target, branch, g + [(K.H, hyp)], n + 1, into_control)]
    if into_control:
        _, body, fml, s, t, major, eq, branch = p
        local = scopes(a, body, g, n)
        return ['e', body, convert([body], major, g, n, True),
                ['t', fml, s, t, convert([s, t], eq, local, n + 1, True),
                 convert(K.sub(fml, s), branch, local, n + 1, True)]]
    if tag == 'e':
        _, body, major, branch = p
        local = scopes(a, body, g, n)
        return ['e', body, a, V.W(0), 0, convert([body], major, g, n, False),
                ['c'], convert(a, branch, local, n + 1, False)]
    _, fml, s, t, eq, branch = p
    eq_new = convert([s, t], eq, g, n, False)
    branch_new = convert(K.sub(fml, s), branch, g, n, False)
    return ['e', V.J, fml, s, t, V.DUMMY_PROOF,
            V.lift(eq_new, n, len(g)), V.lift(branch_new, n, len(g))]


def main():
    rows = []
    for name, packet in V.positives().items():
        data = packet.data()
        K.check(data)
        control = {'goal': packet.goal,
                   'proof': convert(packet.goal, packet.proof, [], 0, True)}
        C.check(control)
        returned = {'goal': packet.goal,
                    'proof': convert(packet.goal, control['proof'], [], 0, False)}
        K.check(returned)
        rows.append({'name': name, 'control_accepted': True, 'return_accepted': True,
                     'exact_goal_preserved': data['goal'] == control['goal'] == returned['goal']})
    cli = 0
    for directory, expected in [('accepted', True), ('rejected', False)]:
        for path in sorted((ROOT / 'examples/canonical' / directory).glob('*.json')):
            for optimize in [False, True]:
                cmd = [sys.executable] + (['-O'] if optimize else []) + [str(ROOT / 'code/canonical_checker.py')]
                r = subprocess.run(cmd, input=path.read_text(), text=True, capture_output=True, timeout=30)
                accepted = r.returncode == 0 and r.stdout.strip() == 'ACCEPT'
                if accepted != expected:
                    raise AssertionError((path.name, optimize, r.returncode, r.stdout, r.stderr))
                cli += 1
    result = {'exact_goal_round_trips': len(rows), 'standalone_cli_checks': cli,
              'normal_and_optimized_python': True, 'passed': True, 'translations': rows}
    (ROOT / 'evidence/control_translation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'translations'}))


if __name__ == '__main__':
    main()
