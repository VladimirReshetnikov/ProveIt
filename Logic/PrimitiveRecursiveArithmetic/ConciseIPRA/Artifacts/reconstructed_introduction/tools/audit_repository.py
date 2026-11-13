"""Measure a local ConciseIPRA snapshot and every .py member of incoming ZIPs.

Usage: python3 tools/audit_repository.py /path/to/ProveIt > census.json
No measured source is executed. This is an optional corpus audit, not a
dependency of any proof checker.
"""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize
import zipfile

SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def row(raw, path):
    tree = ast.parse(raw)
    source = (ast.unparse(tree) + "\n").encode()
    return dict(path=path,
                tokens=sum(t.type not in SKIP for t in
                           tokenize.tokenize(io.BytesIO(source).readline)),
                ast_nodes=len(list(ast.walk(ast.parse(source)))),
                normalized_bytes=len(source),
                gzip9_bytes=len(gzip.compress(source, 9, mtime=0)),
                raw_sha256=hashlib.sha256(raw).hexdigest(),
                normalized_sha256=hashlib.sha256(source).hexdigest())


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    repo = Path(sys.argv[1]).resolve()
    root = repo / "Logic/PrimitiveRecursiveArithmetic/ConciseIPRA"
    if not (root / "Artifacts").is_dir():
        raise SystemExit("ConciseIPRA/Artifacts is missing from the supplied repository.")
    rows = []
    failures = []
    archives = []

    def add(raw, name):
        try:
            rows.append(row(raw, name))
        except (SyntaxError, UnicodeError, ValueError) as error:
            failures.append(dict(path=name, error=str(error)))

    for path in sorted((root / "Artifacts").rglob("*.py")):
        add(path.read_bytes(), str(path.relative_to(root)))
    for path in sorted((root / "docs/incoming").glob("*.zip")):
        raw = path.read_bytes()
        archives.append(dict(name=path.name, bytes=len(raw),
                             sha256=hashlib.sha256(raw).hexdigest(),
                             git_blob=hashlib.sha1(b"blob " + str(len(raw)).encode()
                                                  + b"\x00" + raw).hexdigest()))
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            for info in sorted(archive.infolist(), key=lambda item: item.filename):
                if not info.is_dir() and info.filename.endswith(".py"):
                    add(archive.read(info), "incoming/" + path.name + "/" + info.filename)
    print(json.dumps(dict(python=sys.version, sources=len(rows),
                          unique_normalized_sources=len({r["normalized_sha256"] for r in rows}),
                          failures=failures, archives=archives, rows=rows), indent=2))


if __name__ == "__main__":
    main()
