"""Focused validation of the intrinsic phase checker; no theorem library is trusted.

This script is development evidence, not a proof by finite testing. It checks
all packaged phase regressions, the intentionally changed Boolean/unused-data
contract, the public arity grammar, active float rejection, and scope attacks.
"""
import ast
import copy
import gzip
import hashlib
import io
import json
import math
from pathlib import Path
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'code/checker.py'


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + '\n').encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return dict(tokens=sum(t.type not in ignored for t in
                           tokenize.tokenize(io.BytesIO(normalized).readline)),
                ast_nodes=len(list(ast.walk(tree))), normalized_bytes=len(normalized),
                gzip9_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                source_sha256=hashlib.sha256(raw).hexdigest())


def kernel(path):
    tree = ast.parse(path.read_text())
    keep = []
    for node in tree.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and
                t.id in ('q', 'p') for t in node.targets):
            break
        keep.append(node)
    return compile(ast.Module(body=keep, type_ignores=[]), str(path), 'exec')


KERNEL = kernel(SOURCE)



def run(doc, code=KERNEL):
    state = {}
    exec(code, state)
    try:
        document = json.loads(json.dumps(doc, allow_nan=True))
        state['q'] = document.pop
        state['c']([[]], document.pop())
        return True
    except Exception:
        return False


def open_tree(a, *, depth=0, floor=0, image=0j):
    state = {}
    exec(KERNEL, state)
    state['k'] = floor
    try:
        return True, state['i'](a, image, depth)
    except Exception:
        return False, None


def actual_term(a, binders=0):
    if type(a) is bool:
        return a is True
    if type(a) is int:
        return a == 1 or 3 <= a < 3 + 2 * binders and a % 2 == 1
    if type(a) is not list:
        return False
    return (len(a) == 1 and actual_term(a[0], binders) or
            len(a) == 3 and actual_term(a[0], binders) and
            actual_term(a[1], binders) and actual_term(a[2], binders + 1))


def sorted_public(a, binders=0):
    if type(a) is not list:
        return False
    return (len(a) == 1 and sorted_public(a[0], binders + 2) or
            len(a) == 2 and all(actual_term(t, binders) for t in a))


def alias_true(a):
    if type(a) is list:
        return list(map(alias_true, a))
    return True if type(a) is int and a == 1 else a


def main():
    baseline = json.loads((ROOT / 'tests/cases.json').read_text())['cases']
    rows = []
    failures = []
    for case in baseline:
        expected = case['expected'] or case['name'].startswith('invalid_unused_alphabet_')
        got = run(case['certificate'])
        rows.append(dict(name=case['name'], expected=expected, accepted=got))
        if got != expected:
            failures.append(rows[-1])

    positives = [c for c in baseline if c['expected'] and
                 not c['name'].startswith('valid_unused')]
    aliases = []
    for case in positives:
        doc = alias_true(case['certificate'])
        aliases.append(dict(name=case['name'] + '_true_alias', accepted=run(doc)))
        if not aliases[-1]['accepted']:
            failures.append(aliases[-1])

    # Independent public grammar uses actual binders only: S binds none;
    # an iterator binds one variable in its third child and nowhere else.
    scalars = [None, False, True, '', 'x', 'xx', {}, {'x': 0},
               -20, -3, -2, -1, 0, 1, 2, 3, 4, 5, 7, 11,
               0.0, 1.0, -1.0, 0.5, 3.5,
               float('nan'), float('inf'), float('-inf')]
    rng = random.Random(20261113)

    def raw(depth):
        if not depth or rng.random() < 0.55:
            return copy.deepcopy(rng.choice(scalars))
        return [raw(depth - 1) for _ in range(rng.randrange(5))]

    samples = [raw(4) for _ in range(4000)]
    samples.extend(c['certificate'][-1] for c in positives)
    for a in scalars:
        for form in ([a, 1], [[a], [1]], [[1, 1, a], 1]):
            for n in range(4):
                value = copy.deepcopy(form)
                for _ in range(n):
                    value = [value]
                samples.append(value)
    for a in samples:
        got, _ = open_tree(a)
        if got != sorted_public(a):
            failures.append(dict(kind='public_grammar', value=a,
                                 expected=sorted_public(a), accepted=got))

    active = 0
    for floor in (0, -1, -4):
        for depth in (0, 1, 2, 3, 4, 7):
            for value in scalars:
                got, output = open_tree(value, floor=floor, depth=depth, image=1)
                active += 1
                if got and type(value) not in (int, bool):
                    failures.append(dict(kind='active_type', value=value,
                                         floor=floor, depth=depth, output=output))

    process = []
    process_cases = [
        ('zero', json.loads((ROOT / 'examples/zero.json').read_text()), True),
        ('induction', json.loads((ROOT / 'examples/induction.json').read_text()), True),
        ('implication', json.loads((ROOT / 'examples/implication.json').read_text()), True),
        ('future_capture', json.loads((ROOT / 'examples/reject_capture.json').read_text()), False),
    ]
    zero = process_cases[0][1]
    process_cases.extend([
        ('true_alias', alias_true(zero), True),
        ('unused_json', [{'unused': [None, True, 0.25, 'data']}] + zero, True),
        ('false_goal', zero[:-1] + [[1, [1]]], False),
        ('float_goal', zero[:-1] + [[1.0, 1]], False),
        ('string_goal', zero[:-1] + [['', 1]], False),
        ('dict_goal', zero[:-1] + [[{}, 1]], False),
        ('null_goal', zero[:-1] + [[None, 1]], False),
    ])
    for optimized in (False, True):
        for name, doc, expected in process_cases:
            p = subprocess.run([sys.executable, *(['-O'] if optimized else []), str(SOURCE)],
                               input=json.dumps(doc), text=True, capture_output=True,
                               timeout=15)
            accepted = p.returncode == 0 and p.stdout == 'ACCEPT\n'
            row = dict(name=name, optimized=optimized, expected=expected,
                       accepted=accepted, exit_code=p.returncode)
            process.append(row)
            if accepted != expected:
                failures.append(row)

    report = dict(python=sys.version, candidate=measure(SOURCE),
                  matched_control=measure(ROOT / 'reference/checker316.py'),
                  baseline_cases=len(rows), intentional_true_alias_cases=len(aliases),
                  public_grammar_cases=len(samples), active_scalar_cases=active,
                  full_process_cases=len(process), failures=failures,
                  baseline=rows, aliases=aliases, process=process)
    (ROOT / 'tests/receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ('baseline', 'aliases', 'process')}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
