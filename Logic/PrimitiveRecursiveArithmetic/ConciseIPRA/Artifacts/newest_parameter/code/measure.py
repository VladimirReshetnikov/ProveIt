"""Measure complete, matched strict checkers without counting docstrings."""
import ast
import hashlib
import io
import json
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class StripDocstrings(ast.NodeTransformer):
    def generic_visit(self, node):
        super().generic_visit(node)
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    del node.body[0]
        return node


def measure(path):
    raw = path.read_bytes()
    tree = StripDocstrings().visit(ast.parse(raw.decode('utf-8')))
    normalized = ast.unparse(tree) + '\n'
    ignored = {tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
               tokenize.DEDENT, tokenize.ENDMARKER, tokenize.ENCODING}
    return dict(tokens=sum(t.type not in ignored for t in tokenize.generate_tokens(
                              io.StringIO(normalized).readline)),
                ast_nodes=sum(1 for _ in ast.walk(ast.parse(normalized))),
                normalized_bytes=len(normalized.encode('utf-8')),
                original_bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())


def main():
    files = {
        'unrestricted_control': ROOT / 'reference' / 'checker_guarded_unrestricted.py',
        'previous_pattern_dispatch': ROOT / 'reference' / 'checker_guarded_pattern_dispatch.py',
        'newest_parameter': ROOT / 'code' / 'checker_guarded.py',
    }
    result = {name: measure(path) for name, path in files.items()}
    expected = {
        'unrestricted_control': (1078, 1252, 3442),
        'previous_pattern_dispatch': (1159, 1339, 3688),
        'newest_parameter': (1070, 1243, 3425),
    }
    for name, numbers in expected.items():
        assert tuple(result[name][key] for key in ('tokens', 'ast_nodes', 'normalized_bytes')) == numbers
    report = dict(status='PASS', normalization='Remove actual module/function/class docstrings; '
                  'ast.unparse; append one LF; count complete module.', checkers=result,
                  claim='Matched reduction only; no global minimum claimed.')
    (ROOT / 'evidence' / 'metrics.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
