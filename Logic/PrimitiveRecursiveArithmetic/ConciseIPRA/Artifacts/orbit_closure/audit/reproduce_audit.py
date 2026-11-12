#!/usr/bin/env python3
"""Reproduce metrics and Git identities for the frozen Research Python corpus.

This script parses sources, but never executes them. All repository blobs are
provided as blobs/<git-sha>.py, together with all_py_blobs.json. A source is
not automatically classified as a complete checker merely because it is small.
"""
import ast
import hashlib
import io
import json
import pathlib
import sys
import tokenize

ROOT = pathlib.Path(__file__).resolve().parent
IGNORED = {
    tokenize.COMMENT, tokenize.INDENT, tokenize.DEDENT, tokenize.NEWLINE,
    tokenize.NL, tokenize.ENDMARKER, tokenize.ENCODING,
}


class StripDocstrings(ast.NodeTransformer):
    """Remove precisely Python's module, function, and class docstrings."""

    def visit(self, node):
        node = super().visit(node)
        if isinstance(node, (ast.Module, ast.FunctionDef,
                             ast.AsyncFunctionDef, ast.ClassDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
                if not node.body and not isinstance(node, ast.Module):
                    node.body.append(ast.Pass())
        return node


def measure(raw):
    tree = StripDocstrings().visit(ast.parse(raw.decode('utf-8')))
    tree = ast.fix_missing_locations(tree)
    normalized = ast.unparse(tree) + '\n'
    # Reparse what is actually measured; this also checks the empty-body repair.
    tree = ast.parse(normalized)
    return {
        'bytes': len(normalized.encode('utf-8')),
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast': sum(1 for _ in ast.walk(tree)),
    }


def main():
    sources = json.loads((ROOT / 'all_py_blobs.json').read_text())
    previous = {
        r['sha']: r for r in
        json.loads((ROOT / 'all_measured_blobs.json').read_text())
    }
    for row in sources:
        raw = (ROOT / 'blobs' / (row['sha'] + '.py')).read_bytes()
        digest = hashlib.sha1(
            b'blob ' + str(len(raw)).encode() + b'\0' + raw
        ).hexdigest()
        if digest != row['sha']:
            raise ValueError(('Git blob identity mismatch', row['sha']))
        actual = measure(raw)
        expected = {key: previous[row['sha']][key] for key in actual}
        if actual != expected:
            raise ValueError(('Metric mismatch', row['sha'], actual, expected))
    frontier = json.loads((ROOT / 'frontier.json').read_text())
    for row in frontier['attaining_sources']:
        raw = (ROOT / 'blobs' / (row['git_blob_sha'] + '.py')).read_bytes()
        if measure(raw) != row['metrics']:
            raise ValueError(('Frontier mismatch', row))
    exclusions = json.loads((ROOT / 'subfrontier_exclusions.json').read_text())
    excluded = {r['git_blob_sha'] for r in exclusions['excluded_sources']}
    envelope = frontier['coordinate_envelope']
    smaller = {
        r['sha'] for r in previous.values()
        if any(r[key] < envelope[key] for key in envelope)
    }
    if excluded != smaller:
        raise ValueError(('Incomplete subfrontier classification',
                          sorted(smaller - excluded), sorted(excluded - smaller)))
    for row in exclusions['excluded_sources']:
        if row['metrics'] != {
                key: previous[row['git_blob_sha']][key]
                for key in ('bytes', 'tokens', 'ast')}:
            raise ValueError(('Exclusion metric mismatch', row['git_blob_sha']))
    print(json.dumps({
        'python': sys.version.split()[0],
        'verified_git_blobs': len(sources),
        'verified_repository_paths': sum(len(r['paths']) for r in sources),
        'frontier': frontier['coordinate_envelope'],
        'subfrontier_classified_utilities': len(excluded),
    }, indent=2))


if __name__ == '__main__':
    main()
