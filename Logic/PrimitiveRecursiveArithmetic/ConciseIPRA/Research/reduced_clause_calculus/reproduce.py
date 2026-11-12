"""Reproduce the matched comparison and substantive certificate checks.

Run with CPython 3.12.14. The inherited test generator is executed unchanged;
its positive and negative corpora are captured at its successful return.
"""
import ast
import contextlib
import difflib
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
CODE = ROOT / 'code'
EVIDENCE = ROOT / 'evidence'
EXAMPLES = ROOT / 'examples'
sys.path.insert(0, str(CODE))
import baseline
import reduced
from translations import compile_tree, node_count, to_baseline, to_reduced


def metric(path):
    tree = ast.parse(path.read_text())
    if ast.get_docstring(tree) is not None:
        tree.body = tree.body[1:]
    normalized = (ast.unparse(tree) + '\n').encode()
    (EVIDENCE / (path.stem + '.normalized.py')).write_bytes(normalized)
    insignificant = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
                     tokenize.NL, tokenize.INDENT, tokenize.DEDENT,
                     tokenize.COMMENT}
    tokens = sum(t.type not in insignificant for t in
                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    return {'program': path.stem, 'normalized_bytes': len(normalized),
            'significant_tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def accepted(checker, data):
    try:
        checker.verify(data)
        return True
    except Exception:
        return False


def inherited_corpus():
    path = ROOT / 'baseline' / 'ipra_raw_clausal' / 'tests' / 'verify.py'
    spec = importlib.util.spec_from_file_location('inherited_verify', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    corpus = {}

    def capture(frame, event, arg):
        if event == 'return' and frame.f_code is module.main.__code__:
            corpus['positive'] = frame.f_locals['translated']
            corpus['negative'] = frame.f_locals['rejects']
            corpus['cli_runs'] = frame.f_locals['cli_runs']

    stream = io.StringIO()
    sys.setprofile(capture)
    try:
        with contextlib.redirect_stdout(stream):
            module.main()
    finally:
        sys.setprofile(None)
    (EVIDENCE / 'inherited_execution.json').write_text(stream.getvalue())
    return corpus


def main():
    if sys.version_info[:3] != (3, 12, 14):
        raise RuntimeError('comparison is pinned to CPython 3.12.14')
    EVIDENCE.mkdir(exist_ok=True)
    EXAMPLES.mkdir(exist_ok=True)
    corpus = inherited_corpus()
    positives = dict(corpus['positive'])
    negatives = dict(corpus['negative'])
    for i, t in enumerate((0, [0, 0], [0, [0, 0]],
                           [[0, 0], 0, [1, 0, 2]])):
        proof = ['v', ['r', t], ['r', t]]
        positives['explicit_root_' + str(i)] = {'goal': [t, t], 'proof': proof}
    w = [0, 0, 0]
    computation = ['v', ['r', 0], ['r', w]]
    proof = ['v', computation, ['r', w]]
    positives['root_after_zero_computation'] = {'goal': [w, 0], 'proof': proof}
    results = []
    transformed = {}
    for name, data in positives.items():
        baseline.verify(data)
        proof, roots = compile_tree(data['proof'], [], 0)
        target = to_reduced(data)
        back = to_baseline(target)
        if back['goal'] != data['goal'] or proof != target['proof']:
            raise RuntimeError('end formula changed')
        # No root case survives; recompiling a reduced proof is the identity.
        idempotent, remaining = compile_tree(target['proof'], [], 0)
        if remaining or idempotent != target['proof']:
            raise RuntimeError('compiler left a root case')
        transformed[name] = target
        results.append({'name': name, 'status': 'accepted_both_directions',
                        'old_nodes': node_count(data['proof']),
                        'root_nodes': roots,
                        'new_nodes': node_count(target['proof'])})
    for name, data in negatives.items():
        if accepted(baseline, data) or accepted(reduced, data):
            raise RuntimeError('accepted malformed inherited certificate: ' + name)
        results.append({'name': name, 'status': 'rejected_by_both'})
    # These are valid baseline certificates using precisely the removed case.
    deleted = {k: v for k, v in positives.items() if k.startswith('explicit_root_')}
    for name, data in deleted.items():
        if accepted(reduced, data):
            raise RuntimeError('removed root case is still accepted')
        results.append({'name': name, 'status': 'source_only_until_translated'})
    cli_runs = 0
    for optimize in (False, True):
        for script in (CODE / 'reduced.py', EVIDENCE / 'reduced.normalized.py'):
            if not script.exists():
                metric(CODE / 'reduced.py')
            cases = [(k, v, True) for k, v in transformed.items()]
            cases += [(k, v, False) for k, v in negatives.items()]
            cases += [(k, v, False) for k, v in deleted.items()]
            for name, data, expect in cases:
                command = [sys.executable] + (['-O'] if optimize else []) + [str(script)]
                run = subprocess.run(command, input=json.dumps(data), text=True,
                                     capture_output=True, check=False)
                if (run.returncode == 0) != expect or run.stdout.strip() != (
                        'ACCEPT' if expect else 'REJECT'):
                    raise RuntimeError('public CLI mismatch: ' + name)
                cli_runs += 1
    metrics = [metric(CODE / (name + '.py')) for name in ('baseline', 'reduced')]
    delta = {key: metrics[0][key] - metrics[1][key] for key in
             ('normalized_bytes', 'significant_tokens', 'ast_nodes', 'gzip9_bytes')}
    if not all(delta[k] > 0 for k in ('normalized_bytes', 'significant_tokens', 'ast_nodes')):
        raise RuntimeError('no strict matched improvement')
    for name in ('explicit_root_0', 'used_induction_hypothesis',
                 'capture_avoiding_witness', 'zero_source_nested_template',
                 'nested_compound_binders', 'closure_specialization_4'):
        for label, data in [('baseline', positives[name]), ('reduced', transformed[name])]:
            (EXAMPLES / (name + '.' + label + '.json')).write_text(
                json.dumps(data, indent=2) + '\n')
    report = {'python': sys.version,
              'baseline_commit': '831081033253cca2115196cf86bb99c77ed2aeae',
              'baseline_archive_git_blob': '9c59217d9ea27fbd7542fcc47f90632d0f6fab64',
              'inherited_positive_examples': len(corpus['positive']),
              'inherited_negative_examples': len(corpus['negative']),
              'inherited_cli_runs': corpus['cli_runs'],
              'positive_examples': len(positives), 'negative_examples': len(negatives),
              'removed_root_cases_checked': len(deleted), 'proposal_cli_runs': cli_runs,
              'exact_node_overhead': 'N_new = N_old + 2 * root_nodes',
              'metrics': metrics, 'delta': delta, 'tests': results}
    (EVIDENCE / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    (EVIDENCE / 'metrics.json').write_text(json.dumps(metrics, indent=2) + '\n')
    diff = difflib.unified_diff(
        (EVIDENCE / 'baseline.normalized.py').read_text().splitlines(True),
        (EVIDENCE / 'reduced.normalized.py').read_text().splitlines(True),
        fromfile='baseline.normalized.py', tofile='reduced.normalized.py')
    (EVIDENCE / 'mathematical_deletion.patch').write_text(''.join(diff))
    print(json.dumps({k: report[k] for k in ('positive_examples', 'negative_examples',
          'proposal_cli_runs', 'inherited_cli_runs', 'metrics', 'delta')}, indent=2))


if __name__ == '__main__':
    main()
