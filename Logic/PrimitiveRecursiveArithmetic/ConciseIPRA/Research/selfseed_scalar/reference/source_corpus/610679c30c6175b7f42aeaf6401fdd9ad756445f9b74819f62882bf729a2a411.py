"""Statically inventory ZIP Python sources; execute no inspected source code."""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zipfile
import zlib


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


IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def metrics(raw):
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(raw.decode())))
    normalized = ast.unparse(tree) + '\n'
    encoded = normalized.encode()
    return {
        'tokens': sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        'ast': sum(1 for _ in ast.walk(tree)),
        'bytes': len(encoded),
        'raw': len(raw),
        'gzip_raw': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'gzip_norm': len(gzip.compress(encoded, compresslevel=9, mtime=0)),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('archives', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    seen_archives, sources, occurrences, errors = set(), {}, [], []

    def scan(data, origin, depth=0):
        archive_hash = hashlib.sha256(data).hexdigest()
        if archive_hash in seen_archives:
            return
        seen_archives.add(archive_hash)
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for name in archive.namelist():
                path = origin + '!' + name
                if name.endswith('.zip'):
                    try:
                        scan(archive.read(name), path, depth + 1)
                    except Exception as error:
                        errors.append([path, str(error)])
                elif name.endswith('.py'):
                    raw = archive.read(name)
                    digest = hashlib.sha256(raw).hexdigest()
                    occurrences.append({'sha256': digest, 'path': path, 'depth': depth})
                    if digest in sources:
                        sources[digest]['paths'].append(path)
                    else:
                        try:
                            sources[digest] = {
                                'sha256': digest, 'paths': [path], **metrics(raw)}
                        except Exception as error:
                            errors.append([path, str(error)])

    archives = sorted(args.archives.glob('*.zip'))
    for archive in archives:
        scan(archive.read_bytes(), archive.name)
    result = {
        'python': platform.python_version(), 'zlib': zlib.ZLIB_VERSION,
        'direct_archives': len(archives), 'distinct_archives': len(seen_archives),
        'source_occurrences': len(occurrences), 'distinct_sources': len(sources),
        'sources': list(sources.values()), 'occurrences': occurrences,
        'errors': errors,
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ('sources', 'occurrences')}, indent=2))


if __name__ == '__main__':
    main()
