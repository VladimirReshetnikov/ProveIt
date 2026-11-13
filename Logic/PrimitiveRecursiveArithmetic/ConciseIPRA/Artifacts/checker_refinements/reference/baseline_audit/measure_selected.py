"""Reproduce selected pinned-checker metrics; executes no checker."""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import tokenize

ROOT = Path(__file__).resolve().parent
COMMIT = '6874c85a4cea45d881de73620284fcc75d740942'
PREFIX = 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts/'
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PROGRAMS = {
    'three_field/code/checker_tokens.py': ('R/U whole-array', 'd22b22d4ede303c09bbf5fea754651834ce8e80a'),
    'three_field/code/checker_ast.py': ('R/U whole-array', '6b7b3bbba4ffc95f9d10081477096d910be1ace9'),
    'checked_reductions/checkers/compact477.py': ('R/U header', 'f75effd3b65fa496c7979649bd5a1b5da37cebd5'),
    'head_conversion/code/compact477.py': ('R/U header eager', '48cc9c417ea9e011edf5f1c5fafd91f33a205fbf'),
    'boolean_constancy/checkers/code/checker244.py': ('R/U stream', '93fa53b7be19edb3e38b8a828bcdcfa6803e835e'),
    'fused_iteration/code/checker_refinement/checker.py': ('R/U stream', '33af7c81e2d27eebee3b89b796f2186857af23ca'),
    'boolean_constancy/checkers/code/checker478.py': ('R/U whole-array', '748b53eeea2cf9af66db1cfa391d5e8a133d15ef'),
    'immediate_application/code/checker479.py': ('R/U whole-array', '54e5dce6cad73c1db67644c33e2f15ec72c2f211'),
    'refinement/second_delivery/checkers/code/native_tokens.py': ('G/A-', 'b5a69d427d8bbd9b6e29ca089960cff6559a5442'),
    'refinement/second_delivery/checkers/code/native_bytes.py': ('G/A-', '53b21c760d7a3b3e10a1842d784de05f8a01b8de'),
    'refinement/second_delivery/checkers/code/strict_bytes.py': ('T/ed', '14580460acbb049feba24640b21409dde70a17a5'),
    'checked_reductions/checkers/strict330.py': ('T/ed', '5562ecb1306810933a95555a40552f07f5a79232'),
    'tolerant_certificates/code/checker.py': ('Gt/A-', 'e980900cf3c554252373c7316f4009d3797af83f'),
    'zero_alias/implementation/alias_inverted.py': ('T/ed1', 'b6aa7b08e7c9bcada0f31e04b292d50fa057dbd5'),
}


def measure(name, contract, expected_sha):
    data = (ROOT / name).read_bytes()
    blob_sha = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    if blob_sha != expected_sha:
        raise ValueError(f'Pinned source mismatch: {name}: {blob_sha}')
    tree = ast.parse(data)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and type(value.value) is str:
                    node.body.pop(0)
    source = ast.unparse(tree) + '\n'
    return {
        'path': name, 'contract': contract,
        'tokens': sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(source).readline)),
        'ast_nodes': sum(1 for _ in ast.walk(ast.parse(source))),
        'normalized_bytes': len(source.encode()),
        'source_git_blob_sha1': blob_sha,
        'source_sha256': hashlib.sha256(data).hexdigest(),
        'source_url': f'https://github.com/VladimirReshetnikov/ProveIt/blob/{COMMIT}/{PREFIX}{name}',
    }


if __name__ == '__main__':
    result = {
        'commit': COMMIT, 'python': platform.python_version(),
        'metric': 'Remove genuine docstrings, ast.unparse plus one LF, significant tokens excluding layout/comment/endmarker tokens, all AST nodes.',
        'scope': 'Selected representative pinned-source audit; not an exhaustive corpus census, proof of correctness, or mathematical lower bound.',
        'programs': [measure(name, *meta) for name, meta in PROGRAMS.items()],
        'article_envelopes': {
            'R/U whole-input main table': [249, 271, 477],
            'R/U also admitting stream profiles': [244, 265, 477],
            'G/A- public-goal-validated': [321, 369, 596],
            'T/ed strict': [330, 379, 621],
        },
        'envelopes_attained_by_different_programs': True,
        'different_interfaces_not_directly_comparable': True,
    }
    text = json.dumps(result, indent=2) + '\n'
    (ROOT / 'selected_metrics.json').write_text(text)
    print(text)
