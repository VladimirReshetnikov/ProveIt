"""Check exact normalized-source duplication against the pinned corpus.

This checks textual normalization only. It does not prove mathematical
novelty, soundness, equivalence, or optimality.
"""
import argparse
import ast
import hashlib
import io
import json
from pathlib import Path
import tokenize

SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path, nargs='+')
    parser.add_argument('--index', type=Path,
                        default=Path(__file__).with_name('baseline_fingerprints.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    index = json.loads(args.index.read_text())
    rows = []
    for path in args.candidate:
        tree = ast.parse(path.read_bytes())
        source = ast.unparse(tree) + '\n'
        data = source.encode()
        digest = hashlib.sha256(data).hexdigest()
        matches = index.get(digest, [])
        rows.append(dict(candidate=str(path), sha256_normalized=digest,
                         metrics=dict(significant_tokens=sum(t.type not in SKIP for t in
                             tokenize.generate_tokens(io.StringIO(source).readline)),
                             ast_nodes=sum(1 for _ in ast.walk(tree)),
                             normalized_utf8_bytes=len(data)),
                         exact_normalized_matches=matches,
                         absent_from_pinned_corpus=not matches))
    result = dict(pinned_commit='1156099ffe30f7497d2c11ab20271f46cffcd115',
                  distinct_normalized_sources=len(index),
                  limitation='Exact normalized-source duplication only; '
                             'not mathematical novelty or universal minimality.',
                  candidates=rows)
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')


if __name__ == '__main__':
    main()
