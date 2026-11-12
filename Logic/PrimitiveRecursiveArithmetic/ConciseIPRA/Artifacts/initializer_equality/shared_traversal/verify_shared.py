"""Matched tests and whole-module metrics; this file is not imported by a checker."""
import ast
import gzip
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import random
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'reference'


def load(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


suite = load(BASE / 'test_family.py')


def measure(path):
    tree = suite.RemoveDocstrings().visit(ast.parse(path.read_text()))
    normalized = ast.unparse(ast.fix_missing_locations(tree)) + '\n'
    raw = normalized.encode()
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    result = {'tokens': sum(t.type not in ignored for t in tokenize.tokenize(io.BytesIO(raw).readline)),
              'ast_nodes': sum(1 for _ in ast.walk(ast.parse(normalized))),
              'normalized_bytes': len(raw),
              'gzip9': len(gzip.compress(raw, compresslevel=9, mtime=0)),
              'raw_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    return normalized, result


rng = random.Random(20261111)


def random_term(module, scope, level=3):
    if level == 0 or rng.randrange(4) == 0:
        return rng.randrange(scope + 1)
    if rng.randrange(3) == 0:
        return module.successor(random_term(module, scope, level - 1))
    return module.rec(random_term(module, scope, level - 1),
                      random_term(module, scope, level - 1),
                      random_term(module, scope + 1, level - 1))


def random_formula(module, scope, level=3):
    if level == 0 or rng.randrange(3) == 0:
        return ['=', random_term(module, scope), random_term(module, scope)]
    tag = rng.choice(('Q', 'D'))
    return [tag, random_formula(module, scope + (1 if tag == 'Q' else 2), level - 1)]


result = {'python': sys.version, 'scope': 'Complete source comparison and finite regression support; no machine-checked metatheory.', 'modes': {}}
for mode in ('canonical', 'raw', 'scalar'):
    old_path = BASE / f'{mode}_checker.py'
    new_path = ROOT / f'{mode}_shared.py'
    old, new = load(old_path), load(new_path)
    # Compatibility aliases exist only in this untrusted test process.
    new.shift_term = new.shift_formula = new.shift
    new.subst_term = new.subst_formula = new.subst
    pos, neg = suite.cases(old, mode)
    semantic = suite.substitution_checks(new, mode)
    normalized, new_metrics = measure(new_path)
    _, old_metrics = measure(old_path)
    normalized_path = ROOT / f'{mode}_shared.normalized.py'
    normalized_path.write_text(normalized)
    normalized_path.with_suffix('.py.gz').write_bytes(gzip.compress(normalized.encode(), compresslevel=9, mtime=0))
    records = []
    for expected, coll in [(True, pos), (False, neg)]:
        for name, data in coll.items():
            outcomes = []
            for target in (old_path, new_path, normalized_path):
                for optimize in (False, True):
                    args = [sys.executable] + (['-O'] if optimize else []) + [str(target)]
                    proc = subprocess.run(args, input=json.dumps(data), text=True,
                                          capture_output=True, timeout=10)
                    got = proc.returncode == 0 and proc.stdout == 'ACCEPT\n' and not proc.stderr
                    if got != expected:
                        raise RuntimeError((mode, name, target.name, optimize, proc.returncode, proc.stdout, proc.stderr))
                    outcomes.append({'program': target.name, 'optimized': optimize, 'accept': got})
            records.append({'name': name, 'expected': expected, 'outcomes': outcomes})
    comparisons = 0
    for _ in range(200):
        scope = rng.randrange(5)
        d = rng.randrange(scope + 1)
        amount = rng.randrange(4)
        images = [random_term(old, scope) for _ in range(rng.randrange(4))]
        t = random_term(old, scope + len(images))
        a = random_formula(old, scope + len(images))
        for tree, os, ou in ((t, old.shift_term, old.subst_term), (a, old.shift_formula, old.subst_formula)):
            if os(tree, amount, d) != new.shift(tree, amount, d):
                raise RuntimeError(('shift mismatch', mode, tree, amount, d))
            if ou(tree, images, d) != new.subst(tree, images, d):
                raise RuntimeError(('subst mismatch', mode, tree, images, d))
            comparisons += 2
    result['modes'][mode] = {'old': old_metrics, 'new': new_metrics,
                             'named_cases': len(pos) + len(neg), 'positive': len(pos),
                             'negative': len(neg), 'process_checks': len(records) * 6,
                             'inherited_semantic': semantic,
                             'additional_exact_traversal_comparisons': comparisons,
                             'records': records}
(ROOT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:{a:b for a,b in v.items() if a!='records'} for k,v in result['modes'].items()}, indent=2))
