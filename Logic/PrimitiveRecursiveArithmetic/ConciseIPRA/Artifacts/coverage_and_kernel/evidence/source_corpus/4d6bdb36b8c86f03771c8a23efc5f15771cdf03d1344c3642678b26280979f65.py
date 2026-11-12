"""Three concrete unsound mutations, each checked through a false theorem."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def run(path, packet, optimized):
    p = subprocess.run([sys.executable] + (['-O'] if optimized else []) + [str(path)],
                       input=json.dumps(packet), text=True, capture_output=True, timeout=12)
    return p.returncode == 0 and p.stdout.strip() == 'ACCEPT'


def main():
    cases = json.loads((ROOT / 'tests/cases.json').read_text())
    byte_cases = cases['code/checker.py']
    reflexivity = next(c for c in byte_cases if c['name'] == 'equality_transport_reflexivity')
    proof = copy.deepcopy(reflexivity['packet'])
    two = proof[-1][0]
    false_equation = [two, [two]]
    fake_major = [false_equation, two, [two], [two, 3]]
    false_transport = proof[:-1] + [fake_major, false_equation]
    compound = next(c for c in byte_cases if c['name'] == 'forbidden_compound_progress')['packet']
    false_atom = [0, [0]]
    leaked_hypothesis = [[[], 0, 0, [0]], [[false_atom], 0, 0, 0], false_atom]
    sources = {n: (ROOT / n).read_text() for n in ('code/checker.py', 'code/checker_ast.py')}
    mutants = [
        ('unverified_major', 'code/checker.py',
         sources['code/checker.py'].replace('        c(m, g)\n', ''), false_transport),
        ('compound_induction', 'code/checker.py',
         sources['code/checker.py'].replace('len(a) % 2 == m', 'True'), compound)
    ]

    class Mutable(ast.NodeTransformer):
        def visit_AugAssign(self, node):
            if isinstance(node.target, ast.Name) and node.target.id == 'g':
                node.value = ast.List(elts=node.value.elts, ctx=ast.Load())
            return self.generic_visit(node)
        def visit_Call(self, node):
            if (isinstance(node.func, ast.Name) and node.func.id == 'c'
                    and len(node.args) == 2 and isinstance(node.args[1], ast.Tuple)
                    and not node.args[1].elts):
                node.args[1] = ast.List(elts=[], ctx=ast.Load())
            return self.generic_visit(node)
    mutant = ast.unparse(Mutable().visit(ast.parse(sources['code/checker_ast.py']))) + '\n'
    mutants.append(('leaking_mutable_context', 'code/checker_ast.py', mutant, leaked_hypothesis))
    rows = []
    with tempfile.TemporaryDirectory() as d:
        for name, original, source, packet in mutants:
            path = Path(d) / (name + '.py')
            path.write_text(source)
            for optimized in (False, True):
                good = run(ROOT / original, packet, optimized)
                bad = run(path, packet, optimized)
                rows.append(dict(name=name, original=original, optimized=optimized,
                                 correct_accepts=good, mutant_accepts=bad,
                                 passed=not good and bad, packet=packet,
                                 mutant_sha256=hashlib.sha256(source.encode()).hexdigest()))
    result = dict(scope='Targeted finite controls, not a universal proof.',
                  runs=2*len(rows), controls=len(rows),
                  passed=sum(r['passed'] for r in rows), rows=rows)
    (ROOT / 'evidence/mutation_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}))
    failed = [r for r in rows if not r['passed']]
    if failed:
        print(json.dumps(failed, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
