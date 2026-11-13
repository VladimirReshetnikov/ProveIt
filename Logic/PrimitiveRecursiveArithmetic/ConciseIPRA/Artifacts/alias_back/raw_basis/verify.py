"""Replay raw-equality proof compilers, standalone kernels and scope attacks."""
import ast
import io
import json
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'code'))
import raw_alias as target
import raw_template_matched as control
from translate import translate, to_newest


def measure(path):
    tree = ast.parse(path.read_text())
    for n in ast.walk(tree):
        if (isinstance(n, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
                and n.body and isinstance(n.body[0], ast.Expr)
                and isinstance(n.body[0].value, ast.Constant)
                and isinstance(n.body[0].value.value, str)):
            del n.body[0]
    source = ast.unparse(tree) + '\n'
    tokens = [t for t in tokenize.generate_tokens(io.StringIO(source).readline)
              if t.type not in (tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE,
                                tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
                                tokenize.ENDMARKER)]
    return {'tokens': len(tokens), 'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
            'normalized_bytes': len(source.encode())}


def main():
    cases = []
    source_cases = []
    for p in sorted((ROOT / 'reference/fixtures').glob('*.json')):
        original = json.loads(p.read_text())
        out = translate(original)
        (ROOT / 'tests' / p.name).write_text(json.dumps(out, separators=(',', ':')) + '\n')
        cases.append((p.stem, out, True))
        source_cases.append((p.stem, original, True))
    h = lambda n: ['u', n, None]
    R = lambda t, n=0: ['a', t, h(n)]
    cases.extend([
        ('alias_reflexivity_zero', {'goal': [0, 0], 'proof': R(0)}, True),
        ('alias_reflexivity_compound', {'goal': [[0, 0, 1], [0, 0, 1]], 'proof': R([0, 0, 1])}, True),
        ('nested_alias_depends_outer', {'goal': [[0, 0], [0, 0]],
         'proof': ['a', 0, ['a', [0, -1], h(1)]]}, True),
        ('back_compound_formula', {'goal': [[0, 0]], 'proof': ['a', 0,
          ['v', [[-1, -1]], h(0), ['i', [[0, 0]], 0, h(1)]]]}, True),
        ('alias_seed_captures_fresh', {'goal': [0, 0], 'proof': R(-1)}, False),
        ('alias_seed_captures_fresh_compound', {'goal': [0, 0], 'proof': R([0, -1])}, False),
        ('alias_seed_dangling_bound', {'goal': [0, 0], 'proof': R(1)}, False),
        ('alias_seed_boolean', {'goal': [0, 0], 'proof': R(False)}, False),
        ('alias_seed_float', {'goal': [0, 0], 'proof': R(0.0)}, False),
        ('back_old_parameter', {'goal': [0, 0], 'proof': ['a', 0, ['a', 0,
          ['v', [-1, 0], h(0), R(0, 2)]]]}, False),
        ('back_zero_source', {'goal': [0, 0], 'proof': ['v', [0, 0], R(0), R(0)]}, False),
        ('back_wrong_minor', {'goal': [0, [0, 0]], 'proof': ['a', 0,
          ['v', [-1, [0, 0]], h(0), R(0, 1)]]}, False),
        ('back_boolean_formula', {'goal': [0, 0], 'proof': ['a', 0,
          ['v', [False, False], h(0), R(0, 1)]]}, False),
        ('use_supplied_term', {'goal': [0, 0], 'proof': ['a', 0, ['u', 0, 0, None]]}, False),
        ('use_boolean_index', {'goal': [0, 0], 'proof': ['a', 0, ['u', False, None]]}, False),
        ('use_negative_index', {'goal': [0, 0], 'proof': ['a', 0, ['u', -1, None]]}, False),
        ('use_out_of_range', {'goal': [0, 0], 'proof': ['a', 0, h(1)]}, False),
        ('computation_erased_fresh', {'goal': [[0, 0, -1], 0], 'proof': ['c', 0, 0, -1]}, False),
        ('computation_bad_counter', {'goal': [0, 0], 'proof': ['c', [0, 0, 0], 0, 0]}, False),
        ('branch_future_parameter', {'goal': [0, 0], 'proof': ['a', 0, ['c', 0, -2, 1]]}, False),
        ('export_false_alias_claim', {'goal': [0, [0, 0]], 'proof': R(0)}, False),
        ('extra_root_field', {'goal': [0, 0], 'proof': R(0), 'extra': 0}, False),
        ('boolean_goal_alias', {'goal': [False, False], 'proof': R(0)}, False),
        ('float_goal_alias', {'goal': [0.0, 0.0], 'proof': R(0)}, False),
        ('open_equation_as_existential', {'goal': [0, 0], 'proof': ['e', [0, 0], R(0), h(0)]}, False),
        ('unknown_rule', {'goal': [0, 0], 'proof': ['unknown']}, False),
    ])
    source_context = [([], [-1, 0]), ([], [0, 0])]
    source_proof = ['v', [-1, -1], ['u', 0, 0, None], ['u', 1, 0, None]]
    target_context = [([], [0, 0]), ([], [-3, 0]), ([], [-4, -4]), ([], [0, 0])]
    embedded = to_newest(source_proof, source_context, 2, target_context, 4,
                         {-1: -3, -2: -1}, [1, 3])
    if target.derive(embedded, target_context, 4) != [-3, -3]:
        raise AssertionError('arbitrary target embedding')
    receipts = []
    for name, data, expected in cases:
        for program in ('raw_alias.py', 'raw_alias_small.py'):
            for optimized in (False, True):
                cmd = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code' / program)]
                r = subprocess.run(cmd, input=json.dumps(data), text=True, capture_output=True)
                accepted = r.returncode == 0 and r.stdout == 'ACCEPT\n'
                if accepted != expected:
                    raise AssertionError((name, program, optimized, expected, r.returncode, r.stdout, r.stderr))
                receipts.append({'case': name, 'program': program, 'optimized': optimized,
                                 'accepted': accepted})
    for name, data, expected in source_cases:
        for program in ('raw_template_matched.py', 'raw_template_small.py'):
            for optimized in (False, True):
                cmd = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / 'code' / program)]
                r = subprocess.run(cmd, input=json.dumps(data), text=True, capture_output=True)
                accepted = r.returncode == 0 and r.stdout == 'ACCEPT\n'
                if accepted != expected:
                    raise AssertionError((name, program, optimized, expected, r.returncode, r.stdout, r.stderr))
                receipts.append({'case': name, 'program': program, 'optimized': optimized,
                                 'accepted': accepted})
    result = {'python': sys.version, 'translated_closed_examples': len(source_cases),
              'candidate_cases': len(cases), 'process_runs': len(receipts),
              'non_order_preserving_scope_embedding': True,
              'metrics': {p.name: measure(p) for p in sorted((ROOT / 'code').glob('raw*.py'))},
              'results': receipts}
    (ROOT / 'evidence/validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'results'}, indent=2))


if __name__ == '__main__':
    main()
