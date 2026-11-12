"""Run finite checks and whole-module measurements; not part of any proof kernel."""
import ast
import copy
import gzip
import hashlib
import importlib.util
import io
import json
import platform
import random
import subprocess
import sys
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROFILES = {'raw': 'code/raw_checker.py', 'zero': 'code/zero_checker.py',
            'full': 'code/full_checker.py',
            'full_expression': 'code/full_expression_checker.py'}
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
           tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}


def load(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    data = (ast.unparse(tree) + '\n').encode()
    zipped = gzip.compress(data, compresslevel=9, mtime=0)
    stem = path.stem
    (ROOT/'evidence'/f'{stem}.normalized.py').write_bytes(data)
    (ROOT/'evidence'/f'{stem}.normalized.py.gz').write_bytes(zipped)
    return dict(path=str(path.relative_to(ROOT)), raw_bytes=len(raw),
                normalized_bytes=len(data),
                significant_tokens=sum(t.type not in IGNORED for t in
                    tokenize.tokenize(io.BytesIO(data).readline)),
                ast_nodes=sum(1 for _ in ast.walk(tree)),
                gzip9_bytes=len(zipped), source_sha256=hashlib.sha256(raw).hexdigest(),
                normalized_sha256=hashlib.sha256(data).hexdigest())


def run(profile, payload, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT/PROFILES[profile])]
    result = subprocess.run(command, input=payload, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=20)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def random_term(rng, n, depth):
    if not depth:
        return ['v', rng.randrange(n)] if n and rng.randrange(2) else ['z']
    tag = rng.randrange(4)
    if tag == 0:
        return random_term(rng, n, 0)
    if tag == 1:
        return ['s', random_term(rng, n, depth-1)]
    return ['i', random_term(rng,n,depth-1), random_term(rng,n,depth-1),
            random_term(rng,n+1,depth-1)]


def random_formula(rng, n, depth):
    if not depth:
        return ['=', random_term(rng,n,2), random_term(rng,n,2)]
    tag = rng.choice(['q','d'])
    return [tag, random_formula(rng,n+(1 if tag=='q' else 2),depth-1)]


def traversal_checks():
    candidate = load(ROOT/PROFILES['full'])
    reference = load(ROOT/'reference/full_forward.py')
    rng = random.Random(20261111)
    counts = dict(normalization=0, shift=0, substitution=0, validated_normal_forms=0)
    for j in range(250):
        n = j % 4
        for a, sort in [(random_term(rng,n,3),0),
                        (random_formula(rng,n,2),1)]:
            f = lambda i,d: ['v',i]
            lhs, rhs = candidate.walk(copy.deepcopy(a),f), reference.walk(copy.deepcopy(a),f)
            if lhs != rhs:
                raise ValueError('Changed normalization')
            counts['normalization'] += 1
            candidate.syntax(lhs,n,sort)
            counts['validated_normal_forms'] += 1
            if candidate.shift(a,2) != reference.shift(a,2):
                raise ValueError('Changed capture-safe shift')
            counts['shift'] += 1
        body = random_term(rng,n+1,3)
        image = random_term(rng,n,2)
        if candidate.sub(body,image) != reference.sub(body,image):
            raise ValueError('Changed capture-safe substitution')
        counts['substitution'] += 1
    return counts


def main():
    (ROOT/'evidence').mkdir(exist_ok=True)
    metrics = {name:measure(ROOT/path) for name,path in PROFILES.items()}
    cases = json.loads((ROOT/'tests/cases.json').read_text())
    receipts = []
    for case in cases:
        payload = (ROOT/case['file']).read_bytes()
        for profile in case['profiles']:
            for optimized in [False,True]:
                actual = run(profile,payload,optimized)
                receipts.append(dict(file=case['file'],profile=profile,
                                     optimized=optimized,expected=case['expected'],actual=actual))
    failures = [r for r in receipts if r['actual'] != r['expected']]
    traversals = traversal_checks()
    result = dict(python=sys.version,platform=platform.platform(),zlib_build=zlib.ZLIB_VERSION,
                  zlib_runtime=zlib.ZLIB_RUNTIME_VERSION,metrics=metrics,
                  normalization='Complete module: ast.unparse(ast.parse(source)) plus one LF. No AST content removed.',
                  gzip='gzip.compress(normalized_source, compresslevel=9, mtime=0); informational only.',
                  distinct_cases=len({r['file'] for r in receipts}),
                  process_checks=len(receipts),accepted=sum(r['expected'] for r in receipts),
                  rejected=sum(not r['expected'] for r in receipts),failures=failures,
                  traversal_comparisons=traversals,receipts=receipts,
                  limitations=['Finite tests do not prove universal soundness or completeness.',
                               'The tagged interface is distinct from the compact arity codec.',
                               'Hypothesis and axiom leaves ignore their proof field after validating the goal.',
                               'All inspected terms and formulas must already be canonical for the selected profile.'])
    (ROOT/'evidence/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='receipts'},indent=2))
    if failures:
        raise SystemExit('Verification mismatch')


if __name__=='__main__':
    main()
