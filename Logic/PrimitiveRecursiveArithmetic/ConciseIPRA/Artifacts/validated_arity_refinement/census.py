#!/usr/bin/env python3
"""Static source census. Never import or execute any corpus source."""
import argparse
import ast
import csv
import gzip
import hashlib
import io
import json
import pathlib
import platform
import subprocess
import tokenize
import zipfile

PREFIX = 'Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/'
IGNORED = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
           tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


class StripDocs(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
            if not node.body and not isinstance(node, ast.Module):
                node.body.append(ast.Pass())
        return node
    visit_Module = strip
    visit_FunctionDef = strip
    visit_AsyncFunctionDef = strip
    visit_ClassDef = strip


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()


def measures(raw, name):
    result = {'source_sha256': digest(raw), 'source_bytes': len(raw)}
    try:
        text = raw.decode('utf-8-sig')
        tree = StripDocs().visit(ast.parse(text, filename=name))
        normalized = (ast.unparse(tree) + '\n').encode()
        reparsed = ast.parse(normalized)
        result.update(
            status='parsed',
            tokens=sum(t.type not in IGNORED for t in tokenize.tokenize(io.BytesIO(normalized).readline)),
            ast_nodes=sum(1 for _ in ast.walk(tree)),
            normalized_bytes=len(normalized),
            gzip9_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
            normalized_sha256=digest(normalized),
            accept_print=any(isinstance(n, ast.Call)
                and isinstance(n.func, ast.Name) and n.func.id == 'print'
                and any(isinstance(x, ast.Constant) and x.value == 'ACCEPT' for x in n.args)
                for n in ast.walk(tree)),
            dynamic_execution=any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id in {'exec', 'eval'} for n in ast.walk(tree)),
        )
    except Exception as e:
        result.update(status='not_python', error=type(e).__name__ + ': ' + str(e)[:200])
    return result


def run(repository, output):
    repository, output = pathlib.Path(repository), pathlib.Path(output)
    output.mkdir(parents=True, exist_ok=True)
    commit = subprocess.check_output(['git', '-C', str(repository), 'rev-parse', 'HEAD'], text=True).strip()
    records = subprocess.check_output(['git', '-C', str(repository), 'ls-tree', '-rz', 'HEAD', '--', PREFIX])
    blobs = {}
    for record in records.split(b'\0'):
        if not record:
            continue
        header, name = record.split(b'\t', 1)
        mode, kind, sha = header.decode().split()
        if kind == 'blob':
            blobs[name.decode()] = sha
    rows, archives = [], []
    source_cache = {}

    def add(identifier, stored, metadata):
        raw = gzip.decompress(stored) if identifier.endswith('.gz') else stored
        sha = digest(raw)
        if sha not in source_cache:
            source_cache[sha] = measures(raw, identifier)
        row = dict(identifier=identifier, stored_bytes=len(stored),
                   stored_sha256=digest(stored), **metadata, **source_cache[sha])
        rows.append(row)

    for name, sha in sorted(blobs.items()):
        if name.startswith(PREFIX + 'Artifacts/') and name.endswith(('.py', '.gz')):
            raw = (repository / name).read_bytes()
            if git_blob(raw) != sha:
                raise ValueError('Working tree differs from pinned commit: ' + name)
            try:
                add(name, raw, dict(origin='file', git_blob_sha1=sha))
            except (OSError, EOFError) as e:
                rows.append(dict(identifier=name, origin='file', git_blob_sha1=sha,
                    status='unreadable_compressed_source', error=repr(e)))
        elif name.startswith(PREFIX + 'docs/incoming/') and name.endswith('.zip'):
            raw = (repository / name).read_bytes()
            if git_blob(raw) != sha:
                raise ValueError('Working tree differs from pinned commit: ' + name)
            archive = dict(path=name, git_blob_sha1=sha, sha256=digest(raw), bytes=len(raw))
            archives.append(archive)
            with zipfile.ZipFile(io.BytesIO(raw)) as z:
                for member in sorted(z.namelist()):
                    if member.endswith(('.py', '.gz')):
                        try:
                            add(name + '!' + member, z.read(member), dict(origin='zip_member',
                                archive_git_blob_sha1=sha, archive_sha256=archive['sha256'], member=member))
                        except (OSError, EOFError) as e:
                            rows.append(dict(identifier=name + '!' + member, origin='zip_member',
                                status='unreadable_compressed_source', error=repr(e)))

    summary = dict(repository='https://github.com/VladimirReshetnikov/ProveIt',
        commit=commit, python=platform.python_version(),
        normalization='Remove genuine module/function/class docstrings; replace a docstring-only function/class body by pass; ast.unparse; append LF.',
        token_exclusions=sorted(IGNORED), gzip='gzip.compress(level=9,mtime=0)',
        source_entries=len(rows), parsed_entries=sum(r['status']=='parsed' for r in rows),
        distinct_source_bytes=len(source_cache),
        accept_print_entries=sum(r.get('accept_print', False) for r in rows),
        archives=archives,
        limitations=['Static inventory does not prove checker soundness or completeness.',
                    'Automatic ACCEPT-print detection is a triage aid, not eligibility classification.',
                    'Only Artifacts .py/.gz and Python/.gz members of current incoming ZIPs are in scope.',
                    'Nested historical ZIP archives inside those ZIPs are not recursively expanded.'])
    (output/'source_census.json').write_text(json.dumps(dict(summary=summary, sources=rows), indent=2)+'\n')
    columns=['identifier','status','tokens','ast_nodes','normalized_bytes','gzip9_bytes',
             'accept_print','dynamic_execution','source_sha256','normalized_sha256','git_blob_sha1']
    with (output/'source_census.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=columns,extrasaction='ignore');writer.writeheader();writer.writerows(rows)
    candidates=[r for r in rows if r.get('accept_print') and not r.get('dynamic_execution')
                and (r['tokens']<=330 or r['ast_nodes']<=375 or r['normalized_bytes']<=650)]
    unique={r['normalized_sha256']:r for r in candidates}
    (output/'small_accepting_modules.json').write_text(json.dumps(sorted(unique.values(),
        key=lambda r:(r['normalized_bytes'],r['tokens'],r['identifier'])),indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    print('Distinct small ACCEPT modules:',len(unique))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('repository');parser.add_argument('output')
    a=parser.parse_args();run(a.repository,a.output)
