"""Reproduce bounded-head certificates, source metrics, and CLI checks.

Finite tests supplement the written proof. They are not a proof of soundness
or completeness. This program and the producer are outside the trusted core.
"""
import ast
import hashlib
import importlib.util
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def measure(path):
    original = path.read_bytes()
    parsed = ast.parse(original)
    full = ast.unparse(parsed) + '\n'
    # Match the repository's code-only normalization; separately disclose
    # the complete normalized source including its explanatory docstring.
    if (parsed.body and isinstance(parsed.body[0], ast.Expr)
            and isinstance(parsed.body[0].value, ast.Constant)
            and isinstance(parsed.body[0].value.value, str)):
        parsed.body.pop(0)
    source = ast.unparse(parsed) + '\n'
    return {'file': str(path.relative_to(ROOT)),
            'significant_tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(source).readline)),
            'ast_nodes': sum(1 for _ in ast.walk(parsed)),
            'normalized_bytes': len(source.encode()),
            'normalized_bytes_with_docstring': len(full.encode()),
            'source_sha256': hashlib.sha256(original).hexdigest(),
            'normalized_sha256': hashlib.sha256(source.encode()).hexdigest()}


def to_head(data, head):
    def proof(p):
        if p is None:
            return None
        rule, *a = p
        if rule == 'hc':
            return proof(a[2])
        if rule == 'vs':
            return ['vs', *a[:3], proof(a[3]), proof(a[4])]
        if rule == 'qe':
            return ['qe', head.normal(a[0]), a[1], proof(a[2]), proof(a[3])]
        if rule == 'de':
            return ['de', head.normal(a[0]), proof(a[1]), proof(a[2])]
        if rule == 'di':
            return ['di', a[0], proof(a[1])]
        raise ValueError(rule)
    return {'variables': data['variables'],
            'context': [head.normal(a) for a in data['context']],
            'goal': head.normal(data['goal']), 'proof': proof(data['proof'])}


def run(program, path, expected, optimized):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    command.append(str(program))
    result = subprocess.run(command, input=path.read_bytes(), capture_output=True, timeout=20)
    accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
    return {'program': str(program.relative_to(ROOT)), 'fixture': str(path.relative_to(ROOT)),
            'optimized': optimized, 'expected': expected, 'accepted': accepted,
            'passed': accepted == expected}


def main():
    subprocess.run([sys.executable, str(ROOT / 'code/build_certificates.py')], check=True)
    bounded = ROOT / 'code/bounded_checker.py'
    control = ROOT / 'controls/head_checker.py'
    head = module('matched_head', control)
    checks = []
    cases = json.loads((ROOT / 'tests/cases.json').read_text())
    head_directory = ROOT / 'tests/head'
    head_directory.mkdir(exist_ok=True)
    translations = []
    for case in cases:
        path = ROOT / 'tests' / case['file']
        for optimized in (False, True):
            checks.append(run(bounded, path, case['expected'], optimized))
        if case['expected']:
            data = json.loads(path.read_text())
            normalized = to_head(data, head)
            head.check(normalized)
            translated_path = head_directory / path.name
            translated_path.write_text(json.dumps(normalized, separators=(',', ':')) + '\n')
            for optimized in (False, True):
                checks.append(run(control, translated_path, True, optimized))
            translations.append({'fixture': case['file'], 'same_raw_goal': normalized['goal'] == data['goal'],
                                 'same_raw_context': normalized['context'] == data['context']})
    report = {'python': platform.python_version(),
              'metrics': [measure(path) for path in (bounded, control, ROOT / 'controls/head_checker_source.py')],
              'cli_executions': len(checks), 'failed': [row for row in checks if not row['passed']],
              'checks': checks, 'head_translations': translations,
              'interpretation': 'The translated controls check head-normalized sequents. Equality of raw certificate languages is not claimed.',
              'formal_proof': False}
    (ROOT / 'evidence/verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key not in ('checks',)}, indent=2))
    if report['failed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
