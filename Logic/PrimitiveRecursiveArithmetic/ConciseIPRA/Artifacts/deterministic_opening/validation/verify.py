"""Reproduce meaningful certificate checks and essential-guard mutations.

Every accepted closed fixture is checked in a fresh normal and -O process.
The matched old proofs are separately accepted in both modes. Mathematical
soundness and completeness are not inferred from these finite executions.
"""
from pathlib import Path
import ast
import csv
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tempfile
import tokenize

ROOT = Path(__file__).resolve().parent.parent


def ensure(condition, message):
    if not condition:
        raise RuntimeError(message)


def execute(checker, payload, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(checker)]
    run = subprocess.run(command, input=payload, text=True, capture_output=True, timeout=30)
    accepted = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
    rejected = run.returncode != 0 and run.stdout.strip() == 'REJECT'
    ensure(accepted or rejected, 'invalid checker outcome: ' + repr((command, run.returncode, run.stdout, run.stderr)))
    return accepted


def measure(relative):
    raw = (ROOT / relative).read_bytes()
    tree = ast.parse(raw)
    if (tree.body and isinstance(tree.body[0], ast.Expr)
            and isinstance(tree.body[0].value, ast.Constant)
            and isinstance(tree.body[0].value.value, str)):
        del tree.body[0]
    normalized = (ast.unparse(tree) + '\n').encode()
    excluded = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
                tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT}
    tokens = sum(token.type not in excluded for token in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    return {'path': relative, 'normalized_bytes': len(normalized), 'significant_tokens': tokens,
            'ast_nodes': sum(1 for _ in ast.walk(tree)),
            'gzip9_bytes': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            'raw_bytes': len(raw), 'source_sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def main():
    files = ['code/checker_open.py', 'code/checker.py', 'reference/witness_discharge_checker.py']
    initial_hashes = {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in files}
    for generator in ['generate.py', 'generate_open.py', 'substitution_transition.py']:
        run = subprocess.run([sys.executable, str(ROOT / 'validation' / generator)],
                             capture_output=True, text=True, timeout=60)
        ensure(run.returncode == 0, generator + ': ' + run.stdout + run.stderr)
        print(run.stdout.strip(), flush=True)
    run = subprocess.run([sys.executable, '-O', str(ROOT / 'validation/substitution_transition.py')],
                         capture_output=True, text=True, timeout=30)
    ensure(run.returncode == 0, 'optimized substitution transition: ' + run.stdout + run.stderr)

    suites = [
        ('deterministic_opening', 'code/checker_open.py', 'examples_open', 'matched_old_proofs'),
        ('deterministic_discharge_appendix', 'code/checker.py', 'examples', 'translated_witness_discharge'),
    ]
    results = []
    total_runs = 0
    for name, checker, directory, old_folder in suites:
        counts = {}
        for category, expected in [('positive', True), ('negative', False)]:
            paths = sorted((ROOT / directory / category).glob('*.json'))
            counts[category] = len(paths)
            for path in paths:
                payload = path.read_text()
                for optimized in [False, True]:
                    got = execute(ROOT / checker, payload, optimized)
                    ensure(got == expected, name + ': wrong verdict ' + path.name + ' optimized=' + str(optimized))
                    total_runs += 1
        paths = sorted((ROOT / directory / old_folder).glob('*.json'))
        counts['old_proofs_normal_and_optimized'] = len(paths)
        for path in paths:
            for optimized in [False, True]:
                ensure(execute(ROOT / 'reference/witness_discharge_checker.py', path.read_text(), optimized),
                       'old comparison proof rejected: ' + path.name)
                total_runs += 1
        results.append({'suite': name, **counts, 'all_expected_verdicts': True})

    mutations = []
    with tempfile.TemporaryDirectory(prefix='ipra_guard_review_') as temp:
        opening = (ROOT / 'code/checker_open.py').read_text()
        discharge = (ROOT / 'code/checker.py').read_text()
        configurations = [
            ('opening_without_left_guard', opening,
             ' and row[0] == -n - 1', '',
             'examples_open/negative/essential_left_guard_false_equality.json', 'False equality 1=0'),
            ('opening_without_base_guard', opening,
             'not any(sub(opened, 0)) and ', '',
             'examples_open/negative/essential_base_guard_false_equality.json', 'False equality 1=0'),
            ('opening_without_goal_scope', opening,
             '    syntax(a, n, True)\n', '',
             'examples_open/negative/outer_scope_guard_escape.json', 'A fresh eigenparameter escapes the closed result'),
            ('discharge_without_left_guard', discharge,
             'row[0] == i == -n - 1', 'i == -n - 1',
             'examples/negative/essential_left_guard_false_equality.json', 'False equality 1=0'),
            ('discharge_without_base_guard', discharge,
             'local[-1][0] == [0, 0] and ', '',
             'examples/negative/essential_base_guard_false_closure.json', 'A false closure with true base and second row 1=0'),
            ('discharge_without_goal_scope', discharge,
             '    syntax(a, n, True)\n', '',
             'examples/negative/outer_scope_guard_escape.json', 'A fresh eigenparameter escapes the closed result'),
        ]
        for name, source, before, after, attack, consequence in configurations:
            ensure(source.count(before) == 1, 'mutation no longer isolates one guard: ' + name)
            mutant = Path(temp) / (name + '.py')
            mutant.write_text(source.replace(before, after, 1))
            for optimized in [False, True]:
                ensure(execute(mutant, (ROOT / attack).read_text(), optimized), 'essential guard mutation not detected: ' + name)
                total_runs += 1
            mutations.append({'mutation': name, 'attack': attack, 'mutant_accepts_normal_and_optimized': True,
                              'correct_checker_rejects': True, 'consequence': consequence})

    metrics = [measure(path) for path in files]
    ensure(all(row['source_sha256'] == initial_hashes[row['path']] for row in metrics),
           'a checker source changed while validation was running')
    metric_data = {'python': platform.python_version(),
                   'convention': 'Remove module docstring; ast.unparse; append one LF; significant tokens exclude layout/comments; gzip9 mtime=0.',
                   'rows': metrics}
    (ROOT / 'evidence/independent_metrics.json').write_text(json.dumps(metric_data, indent=2) + '\n')
    with (ROOT / 'evidence/independent_metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=metrics[0].keys())
        writer.writeheader()
        writer.writerows(metrics)
    evidence = {'python': platform.python_version(), 'suites': results,
                'fresh_checker_processes': total_runs, 'essential_guard_mutations': mutations,
                'open_local_sequents': {'opening': 1, 'discharge': 1},
                'targeted_substitution_transition': {'source': 'ACCEPT', 'passive_only': 'REJECT',
                                                     'combined_smaller_branch_substitution': 'ACCEPT',
                                                     'process_modes': ['normal', '-O']},
                'independent_old_kernel_replays': {'opening_matched_theorems': 16, 'discharge_translations': 17},
                'opening_translation_limit': 'The opening suite supplies matched old proofs of identical theorems, not a generic executable proof translation.',
                'discharge_translation': 'All valid appendix fixtures are checked before a general DD-to-WD producer translates them; old checker and independent inherited kernel both replay the output.',
                'mathematical_limit': 'Finite tests and mutation controls supplement the written proof. They are not proof-assistant verification or a proof of universal soundness/completeness.',
                'source_hashes': initial_hashes}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print(json.dumps({'fresh_checker_processes': total_runs, 'suites': results, 'metrics': metrics}, indent=2))


if __name__ == '__main__':
    main()
