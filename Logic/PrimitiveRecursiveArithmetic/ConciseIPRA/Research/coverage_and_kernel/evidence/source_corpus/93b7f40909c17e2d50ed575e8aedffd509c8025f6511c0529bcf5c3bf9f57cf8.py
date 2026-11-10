"""Reproduce full-source metrics for every extracted current-draft Python file.

Usage: python3 code/audit_corpus.py EXTRACTED_ROOT OUTPUT_JSON
The candidate label is a review aid, not a semantic certification.
"""
import ast
import hashlib
import io
import json
import platform
from pathlib import Path
import sys
import tokenize

IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


class StripDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node

    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def significant(source):
    return sum(t.type not in IGNORED
               for t in tokenize.generate_tokens(io.StringIO(source).readline))


def measure(raw):
    source = raw.decode('utf-8')
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(source)))
    normalized = ast.unparse(tree) + '\n'
    imports = [ast.unparse(n) for n in tree.body
               if isinstance(n, (ast.Import, ast.ImportFrom))]
    strings = {n.value for n in ast.walk(tree)
               if isinstance(n, ast.Constant) and isinstance(n.value, str)}
    return {
        'normalized_tokens': significant(normalized),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized.encode('utf-8')),
        'raw_bytes': len(raw),
        'imports': imports,
        'standalone_candidate': 'ACCEPT' in strings and 'REJECT' in strings,
    }


def main():
    root = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2])
    sources = {}
    errors = []
    occurrences = 0
    for path in sorted(root.rglob('*.py')):
        occurrences += 1
        raw = path.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        relative = path.relative_to(root).as_posix()
        if digest in sources:
            sources[digest]['paths'].append(relative)
            continue
        try:
            metrics = measure(raw)
        except Exception as exc:
            errors.append({'path': relative, 'error': repr(exc)})
            continue
        sources[digest] = {'sha256': digest, 'paths': [relative], **metrics}
    candidates = [row for row in sources.values() if row['standalone_candidate']]
    keys = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')
    envelope = {key: min(row[key] for row in candidates) for key in keys}
    attainers = {key: [{'sha256': row['sha256'], 'paths': row['paths']}
                      for row in candidates if row[key] == envelope[key]]
                 for key in keys}
    result = {
        'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'repository_commit': '6c902762efcb1e78a5dd25db745310bab74f47a5',
        'archive_count': len([p for p in root.iterdir() if p.is_dir()]),
        'python_occurrences': occurrences,
        'distinct_measurable_sources': len(sources),
        'standalone_candidate_count': len(candidates),
        'observed_candidate_envelope': envelope,
        'attainers': attainers,
        'scope': 'All extracted .py files; full standalone modules measured. Candidate detection uses literal ACCEPT and REJECT strings and needs human semantic role review. The reported attainers have been reviewed as complete Choice-DI checkers. Bare raise is permitted in their public interface and emits a traceback on stderr. This is an observed finite-corpus envelope, not a universal lower bound.',
        'errors': errors,
        'sources': list(sources.values()),
    }
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items()
                      if key != 'sources'}, indent=2))


if __name__ == '__main__':
    main()
