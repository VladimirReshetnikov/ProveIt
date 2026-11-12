"""Reproduce source metrics and the finite positive witness.

This script does not prove the infinite-model theorem. See the report.
Uses only the Python standard library. Recorded metrics use CPython 3.12.14.
"""
import ast
from collections import Counter
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


class StripDocstrings(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node

    visit_Module = strip
    visit_FunctionDef = strip
    visit_AsyncFunctionDef = strip
    visit_ClassDef = strip


def measure(path):
    tree = StripDocstrings().visit(ast.parse(path.read_text(encoding='utf-8')))
    ast.fix_missing_locations(tree)
    normalized = ast.unparse(tree) + '\n'
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
               tokenize.COMMENT}
    tokens = sum(t.type not in ignored for t in
                 tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {
        'significant_tokens': tokens,
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
        'normalized_bytes': len(normalized.encode('utf-8')),
        'normalized_sha256': hashlib.sha256(normalized.encode()).hexdigest(),
    }


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def count_proof(proof):
    tag = proof[0]
    counts = Counter({tag: 1})
    if tag == 'qi':
        counts.update(count_proof(proof[2]))
    elif tag == 'tr':
        counts.update(count_proof(proof[2]))
        counts.update(count_proof(proof[3]))
    else:
        require(tag in {'hyp', 'succ'}, 'Unexpected witness rule: ' + tag)
    return counts


def main():
    provenance = json.loads((ROOT / 'SOURCE_PROVENANCE.json').read_text())
    for source in provenance['source_records']:
        path = ROOT / source['local_path']
        require(hashlib.sha256(path.read_bytes()).hexdigest() == source['sha256'],
                'Changed pinned source: ' + source['local_path'])

    metrics = {}
    expected = {
        'frontier_tokens.py': (256, 283, 593),
        'frontier_ast.py': (263, 276, 580),
        'frontier_bytes.py': (267, 303, 506),
    }
    for name, triple in expected.items():
        result = measure(ROOT / 'reference' / name)
        actual = tuple(result[k] for k in
                       ['significant_tokens', 'ast_nodes', 'normalized_bytes'])
        require(actual == triple, 'Metric mismatch for ' + name + ': ' + str(actual))
        metrics[name] = result

    spec = importlib.util.spec_from_file_location(
        'frozen_native', ROOT / 'reference/native_eight.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    certificate = json.loads((ROOT / 'evidence/progress_witness.json').read_text())
    checker.check(certificate)
    counts = count_proof(certificate['proof'])
    require(counts == Counter({'qi': 1, 'tr': 2, 'hyp': 1, 'succ': 2}),
            'Unexpected proof-tree inventory')

    equation = certificate['goal'][1]
    step = {
        'variables': 1,
        'context': [checker.opening(equation, -1)],
        'goal': checker.opening(equation, [0, -1]),
        'proof': certificate['proof'][2],
    }
    require('qi' not in count_proof(step['proof']), 'Step uses progress')
    checker.check(step)
    base = {
        'variables': 0, 'context': [],
        'goal': checker.opening(equation, 0),
        'proof': ['zero', 0, 1],
    }
    checker.check(base)
    for name, value in [('step_witness.json', step), ('base_witness.json', base)]:
        (ROOT / 'evidence' / name).write_text(json.dumps(value, indent=2) + '\n')

    cli = []
    for optimized in (False, True):
        for name in ('progress_witness.json', 'step_witness.json', 'base_witness.json'):
            command = [sys.executable] + (['-O'] if optimized else [])
            command += [str(ROOT / 'reference/native_eight.py')]
            result = subprocess.run(command,
                input=(ROOT / 'evidence' / name).read_bytes(),
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
            require(result.returncode == 0 and result.stdout == b'ACCEPT\n',
                    'Certificate CLI failed: ' + name)
            cli.append({'certificate': name, 'optimized_python': optimized,
                        'exit_code': result.returncode, 'stdout': 'ACCEPT'})

    report = {
        'status': 'PASS',
        'python': platform.python_version(),
        'pinned_source_hashes_checked': len(provenance['source_records']),
        'metrics': metrics,
        'coordinate_envelope': {'significant_tokens': 256, 'ast_nodes': 276,
                                'normalized_bytes': 506},
        'positive_derivation': {'tree_nodes': sum(counts.values()),
                                'rule_counts': dict(counts)},
        'step_without_progress_checked': True,
        'zero_computation_checked': True,
        'cli_checks': cli,
        'scope': 'Finite positive evidence and measurements only. The independence '
                 'theorem is a written infinite-model proof, not checked by this script.',
    }
    (ROOT / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
