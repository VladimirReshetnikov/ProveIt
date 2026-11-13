"""Focused independent-process verification of the input-framing composition.

The controls and candidates are complete acceptance modules. This verifier,
fixture transducer and optional fixture producer are outside those modules.
"""
import ast
import concurrent.futures
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
from transduce import array_to_stream, stream_to_array

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
        tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def measure(path):
    normalized = ast.unparse(ast.parse(path.read_text())) + '\n'
    return {'file': str(path.relative_to(ROOT)),
            'tokens': sum(t.type not in SKIP for t in
                          tokenize.generate_tokens(io.StringIO(normalized).readline)),
            'ast_nodes': len(list(ast.walk(ast.parse(normalized)))),
            'normalized_bytes': len(normalized.encode()),
            'source_sha256': sha(path.read_bytes())}


class ReaderReplacement(ast.NodeTransformer):
    def visit_Call(self, node):
        node = self.generic_visit(node)
        if (isinstance(node.func, ast.Name) and node.func.id == 'loads'
                and len(node.args) == 1 and isinstance(node.args[0], ast.Call)
                and isinstance(node.args[0].func, ast.Name)
                and node.args[0].func.id == 'input' and not node.args[0].args):
            return ast.copy_location(ast.Call(func=ast.Name(id='q', ctx=ast.Load()),
                                             args=[], keywords=[]), node)
        return node


def functions(path, replace_reader=False):
    module = ast.parse(path.read_text())
    if replace_reader:
        module = ReaderReplacement().visit(module)
    return [ast.dump(node, include_attributes=False) for node in module.body
            if isinstance(node, ast.FunctionDef)]


def execute(job):
    name, profile, path, mode, data, expected = job
    args = [sys.executable, '-I', '-S', '-B']
    if mode:
        args.append('-O')
    args.append(str(path))
    try:
        result = subprocess.run(args, input=data, capture_output=True, timeout=20)
        accepted = result.returncode == 0 and result.stdout == b'ACCEPT\n'
        return {'case': name, 'profile': profile, 'program': str(path.relative_to(ROOT)),
                'optimized': mode, 'expected': expected, 'accepted': accepted,
                'passed': accepted == expected, 'timed_out': False}
    except subprocess.TimeoutExpired:
        return {'case': name, 'profile': profile, 'program': str(path.relative_to(ROOT)),
                'optimized': mode, 'expected': expected, 'accepted': False,
                'passed': False, 'timed_out': True}


def main():
    provenance = json.loads((ROOT / 'provenance.json').read_text())
    checks = []
    for item in provenance['files']:
        path = ROOT / item['local_path']
        checks.append({'check': 'source_sha256', 'file': item['local_path'],
                       'passed': sha(path.read_bytes()) == item['sha256']})
    metrics = []
    for kind in ('tokens', 'ast'):
        control = ROOT / 'controls' / (kind + '_stream.py')
        candidate = ROOT / 'candidate' / (kind + '_whole.py')
        checks.append({'check': 'complete_function_AST_identity_after_reader_replacement',
                       'profile': kind,
                       'passed': functions(control, True) == functions(candidate)})
        metrics += [measure(control), measure(candidate)]
    cases = json.loads((ROOT / 'cases.json').read_text())
    jobs = []
    for case in cases:
        stream = (ROOT / 'fixtures' / case['file']).read_bytes()
        whole = (ROOT / 'fixtures' / case['whole_file']).read_bytes()
        value = json.loads(whole)
        expected_rows = [json.loads(line) for line in stream.decode().splitlines()]
        checks.append({'check': 'outer_reversal_and_inverse', 'file': case['file'],
                       'passed': stream_to_array(stream.decode()) == value
                       and [json.loads(line) for line in array_to_stream(value).splitlines()]
                       == expected_rows})
        checks.append({'check': 'fixture_hashes', 'file': case['file'],
                       'passed': sha(stream) == case['stream_sha256']
                       and sha(whole) == case['whole_sha256']})
        profiles = ('local', 'global') if case['profile'] == 'both' else (case['profile'],)
        for profile in profiles:
            kind = 'ast' if profile == 'local' else 'tokens'
            for mode in (False, True):
                jobs.append((case['file'], profile, ROOT/'controls'/(kind+'_stream.py'),
                             mode, stream, case['expected']))
                jobs.append((case['file'], profile, ROOT/'candidate'/(kind+'_whole.py'),
                             mode, whole, case['expected']))
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        outcomes = list(pool.map(execute, jobs))
    failures = [x for x in checks + outcomes if not x['passed']]
    report = {'scope': 'Finite implementation checks; universal framing equivalence is proved separately.',
              'python': sys.version, 'fixed_repository_commit': provenance['commit'],
              'input_contract': 'Exact integer/list records; canonical closed guarded Eq/D goal. Whole-JSON array versus one JSON record per line.',
              'metrics': metrics, 'fixture_cases': len(cases), 'executions': len(outcomes),
              'failures': failures, 'checks': checks, 'outcomes': outcomes}
    (ROOT/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('checks','outcomes')}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
