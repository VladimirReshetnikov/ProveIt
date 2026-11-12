"""Reproduce the canonical-clause comparison and normalization checks."""
import ast
import contextlib
import copy
import gzip
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
CODE = ROOT / 'code'
OUT = ROOT / 'evidence'
sys.path.insert(0, str(ROOT.parent / 'code'))
sys.path.insert(0, str(CODE))
import baseline
import canonical
import canonical_control
from canonical_translation import normal, root, to_canonical


def accepts(checker, certificate):
    try:
        checker.verify(certificate)
        return True
    except Exception:
        return False


def metrics(name):
    directory = ROOT.parent / 'code' if name == 'baseline' else CODE
    tree = ast.parse((directory / (name + '.py')).read_text())
    if ast.get_docstring(tree) is not None:
        tree.body = tree.body[1:]
    source = (ast.unparse(tree) + '\n').encode()
    (OUT / (name + '.normalized.py')).write_bytes(source)
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {'program': name, 'normalized_bytes': len(source),
            'significant_tokens': sum(t.type not in ignored for t in
                tokenize.generate_tokens(io.StringIO(source.decode()).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_bytes': len(gzip.compress(source, compresslevel=9, mtime=0))}


def inherited_examples():
    path = ROOT.parent / 'baseline/ipra_raw_clausal/tests/verify.py'
    spec = importlib.util.spec_from_file_location('inherited_test_module', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    corpus = {}

    def capture(frame, event, arg):
        if event == 'return' and frame.f_code is module.main.__code__:
            corpus['positive'] = frame.f_locals['translated']
            corpus['negative'] = frame.f_locals['rejects']

    log = io.StringIO()
    sys.setprofile(capture)
    try:
        with contextlib.redirect_stdout(log):
            module.main()
    finally:
        sys.setprofile(None)
    return corpus


def witness_repair_example():
    one = [0, 0]
    witness = [0, 0, 0]
    base = [0, one, one]
    pred = [-1, one, one]
    step_term = [[0, -1], one, one]
    hypothesis = ['u', 0, 0, ['r', 0]]
    base_computation = ['v', ['r', one], ['r', base]]
    one_zero = ['v', hypothesis, base_computation]
    step_computation = ['v', ['r', pred], ['r', step_term]]
    reversed_step = ['v', ['r', step_term], step_computation]
    step = ['v', one_zero, reversed_step]
    goal = [[[1, one, one], 0]]
    return {'goal': goal, 'proof': ['i', goal, witness, step]}


def main():
    OUT.mkdir(exist_ok=True)
    (ROOT / 'examples').mkdir(exist_ok=True)
    corpus = inherited_examples()
    positive = dict(corpus['positive'])
    positive['zero_witness_requires_mode_repair'] = witness_repair_example()
    results = []
    targets = {}
    for name, source in positive.items():
        target, counts = to_canonical(source)
        canonical_control.verify(target)
        if target['goal'] != normal(source['goal']):
            raise RuntimeError('wrong normalized end formula')
        targets[name] = target
        results.append({'name': name, 'status': 'accepted_after_translation', **counts})
    repaired = targets['zero_witness_requires_mode_repair']
    if repaired['proof'][2] != [[0, 0], 0, 0]:
        raise RuntimeError('canonical nonliteral zero alias was not used')
    uncorrected = copy.deepcopy(repaired)
    uncorrected['proof'][2] = 0
    if accepts(canonical, uncorrected):
        raise RuntimeError('retagged case proof accepted as a progress proof')
    negative = dict(corpus['negative'])
    negative['illegal_zero_counter_goal'] = {
        'goal': [[0, 0, 1], [0, 0, 1]], 'proof': ['r', [0, 0, 1]]}
    negative['invalid_retagged_case'] = uncorrected
    negative['root_case_is_removed'] = {
        'goal': [0, 0], 'proof': ['v', ['r', 0], ['r', 0]]}
    negative['canonical_predecessor_source_mismatch'] = {
        'goal': [0, 0],
        'proof': ['v', ['r', [0, 0]], ['r', [[0, 0], 0, 1]]]}
    for name, data in negative.items():
        if accepts(canonical, data):
            raise RuntimeError('accepted invalid certificate: ' + name)
        results.append({'name': name, 'status': 'rejected'})
    metric_rows = [metrics(n) for n in ('baseline', 'canonical_control', 'canonical')]
    cli_runs = 0
    for optimization in ([], ['-O']):
        for script in (CODE / 'canonical.py', OUT / 'canonical.normalized.py'):
            for name, data, expected in (
                    [(n, d, True) for n, d in targets.items()] +
                    [(n, d, False) for n, d in negative.items()]):
                run = subprocess.run([sys.executable] + optimization + [str(script)],
                                     input=json.dumps(data), text=True, capture_output=True)
                if (run.returncode == 0) != expected or run.stdout.strip() != (
                        'ACCEPT' if expected else 'REJECT'):
                    raise RuntimeError('public CLI mismatch: ' + name)
                cli_runs += 1
    for name in ('used_induction_hypothesis', 'zero_witness_requires_mode_repair',
                 'capture_avoiding_witness', 'nested_compound_binders',
                 'closure_specialization_4'):
        for kind, data in [('raw', positive[name]), ('canonical', targets[name])]:
            (ROOT / 'examples' / (name + '.' + kind + '.json')).write_text(
                json.dumps(data, indent=2) + '\n')
    report = {'python': sys.version, 'positive_examples': len(targets),
              'negative_examples': len(negative), 'cli_runs': cli_runs,
              'translation': 'raw to canonical, with literal-zero witness repair',
              'reverse_translation': 'written equivalence; no implemented raw proof compiler',
              'metrics': metric_rows, 'tests': results}
    (OUT / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (OUT / 'metrics.json').write_text(json.dumps(metric_rows, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('positive_examples',
        'negative_examples', 'cli_runs', 'metrics')}, indent=2))


if __name__ == '__main__':
    main()
