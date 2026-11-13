"""Translate canonical four-field certificates by tracing their source checker.

Only mode fields of actual introductions with literal-equation matrices change.
The theorem code, all term/formula codes, scopes, and proof-tree shape are kept.
This is an untrusted proof producer; exact_threshold.py checks every output.
"""
import ast
import copy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'controls'


def prefix(path):
    tree = ast.parse(Path(path).read_text())
    # The two kernels declare c, k, and i before their reader import.
    items = []
    for node in tree.body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            break
        items.append(node)
    return compile(ast.Module(body=items, type_ignores=[]), str(path), 'exec')


def translate(certificate):
    original = copy.deepcopy(certificate)
    result = copy.deepcopy(certificate)
    ns = {}
    exec(prefix(BASE/'intrinsic_checker.py'), ns)
    i = ns['i']
    pending = list(range(len(original)-1))
    changes = []

    def check(g, a):
        idx = pending.pop()
        s, u, t, m = r = original[idx]
        checked = i(a)
        ns['k'] -= 1
        computation = [[[s] if s else 1, u, t], i(t, r[:3], 3) if s else u]
        if checked in (ns['k'], *g, computation):
            return
        h = m * 3
        if not h:
            a = i(*a, t, 2)
            h = a
            if len(a) == 2:
                replacement = 0 if u == 2 else 2
                result[idx][1] = replacement
                changes.append({'packet_index':idx, 'old_mode':u, 'new_mode':replacement})
        major_result = check(g, m)
        image = (major_result or m or len(a) == 2 == u) and ns['k']
        opened = i(h, image)
        # Source control is deliberately evaluated with the original eagerness.
        options = (a, i(t, s))
        matches = (m, a) == (r[:2] if s else [t]*3, i(t, u))
        check(g + [opened], i(options[matches], [ns['k']]))

    check([[]], original[-1])
    return result, changes


def accepts(path, cert):
    ns = {}
    exec(prefix(path), ns)
    stream = copy.deepcopy(cert)
    ns['q'] = stream.pop
    try:
        ns['c']([[]], ns['q']())
        return True
    except Exception:
        return False


def main():
    incoming = json.loads((BASE/'native_positives.json').read_text())['cases']
    out = ROOT/'tests/fixtures/regenerated'
    out.mkdir(exist_ok=True)
    cases = []
    for case in incoming:
        certificate, changes = translate(case['certificate'])
        accepted = accepts(ROOT/'code/checker.py', certificate)
        item = dict(case, certificate=certificate, mode_changes=changes, accepted=accepted)
        cases.append(item)
        (out/(case['name']+'.json')).write_text(json.dumps(certificate,separators=(',',':'))+'\n')
        print(case['name'], 'ACCEPT' if accepted else 'FAIL', len(changes))
    (out/'cases.json').write_text(json.dumps({'cases':cases},indent=2)+'\n')
    if not all(c['accepted'] for c in cases):
        raise SystemExit(1)

if __name__ == '__main__':
    main()
