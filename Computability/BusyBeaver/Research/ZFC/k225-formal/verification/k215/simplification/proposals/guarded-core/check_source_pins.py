#!/usr/bin/env python3
"""Owned byte/provenance checks. All received source and archive content is data."""
import os
import sys
if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION')
import ast
import hashlib
import json
import zipfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise SystemExit(message)

def read(name):
    return json.loads((ROOT / name).read_text())

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def safe(base, name):
    rel = PurePosixPath(name)
    require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == name, 'UNSAFE_INPUT_PATH')
    p = base.joinpath(*rel.parts)
    require(p.is_file() and not p.is_symlink() and base in p.resolve().parents, 'MISSING_OR_UNSAFE_INPUT: ' + name)
    return p

def main():
    received = {}
    for topic in ('affine', 'checked'):
        root = ROOT / topic / 'extracted'
        rows = read(topic + '/FILE_MANIFEST.json')
        expected = {row['path'] for row in rows}
        require(len(expected) == len(rows), 'DUPLICATE_RECEIVED_PATH')
        actual = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}
        require(actual == expected, 'RECEIVED_MANIFEST_COVERAGE: ' + topic)
        for row in rows:
            data = safe(root, row['path']).read_bytes()
            require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'RECEIVED_FILE_PIN: ' + row['path'])
        received[topic] = len(rows)
    root = ROOT / 'refinements/incoming/K215_Certificate_Refinements_2026-10-21'
    manifest = json.loads((root / 'manifest.json').read_text())['files']
    require({p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()} == set(manifest) | {'manifest.json'}, 'REFINEMENTS_MANIFEST_COVERAGE')
    for name, pin in manifest.items():
        data = safe(root, name).read_bytes()
        require(len(data) == pin['bytes'] and sha(data) == pin['sha256'], 'REFINEMENTS_RECEIVED_FILE_PIN: ' + name)
    received['refinements'] = len(manifest) + 1
    archive = ROOT / 'downloads/affine.zip'
    intake = read('affine/INTAKE.json')
    data = archive.read_bytes()
    require(len(data) == intake['bytes'] and sha(data) == intake['sha256'] and blob(data) == intake['git_blob_sha'], 'ORIGINAL_AFFINE_ARCHIVE_PIN')
    root = ROOT / 'affine/extracted'
    with zipfile.ZipFile(archive) as z:
        members = [info for info in z.infolist() if not info.is_dir()]
        require(len(members) == len({info.filename for info in members}) == received['affine'], 'ARCHIVE_MEMBER_COUNT')
        for info in members:
            require(info.file_size <= 20000000, 'ARCHIVE_MEMBER_BOUND')
            require(z.read(info.filename) == safe(root, info.filename).read_bytes(), 'ARCHIVE_EXTRACTED_BYTE_MISMATCH: ' + info.filename)
    index = read('SOURCE_BINDING_INDEX.json')
    for row in index['bindings']:
        data = safe(ROOT, row['local_file']).read_bytes()
        if row.get('sha256'):
            require(sha(data) == row['sha256'], 'SOURCE_SHA256: ' + row['local_file'])
        if row.get('git_blob_sha1'):
            require(blob(data) == row['git_blob_sha1'], 'SOURCE_GIT_BLOB: ' + row['local_file'])
    checked_hashes = read('checked/OWNED_SHA256.json')
    for name, pin in checked_hashes.items():
        require(sha(safe(ROOT / 'checked', name).read_bytes()) == pin, 'CHECKED_OWNED_PIN: ' + name)
    for topic, name in [('refinements', 'REVIEW_MANIFEST.json'), ('guarded_review', 'MANIFEST.json')]:
        for path, pin in read(topic + '/' + name).items():
            data = safe(ROOT / topic, path).read_bytes()
            require(len(data) == pin['bytes'] and sha(data) == pin['sha256'], 'TOPIC_MANIFEST_PIN: ' + topic + '/' + path)
    report_sources = read('report/qa/SOURCE_BINDINGS.json')['sources']
    for name, pin in report_sources.items():
        data = safe(ROOT, name).read_bytes()
        require(len(data) == pin['bytes'] and sha(data) == pin['sha256'], 'REPORT_SOURCE_BINDING: ' + name)
    qa = read('report/qa/QA.json')
    require(qa['status'] == 'PASS' and qa['pages'] == 7, 'REPORT_QA_SCOPE')
    for name, pin in qa['artifacts'].items():
        data = safe(ROOT / 'report', name).read_bytes()
        require(len(data) == pin['bytes'] and sha(data) == pin['sha256'], 'REPORT_ARTIFACT_BINDING: ' + name)
    for line in (ROOT / 'report/SHA256SUMS').read_text().splitlines():
        expected, name = line.split(None, 1)
        require(sha(safe(ROOT / 'report', name.strip()).read_bytes()) == expected, 'REPORT_CHECKSUM: ' + name)
    scripts = index['positive_owned_checkers']
    imports = {}
    for script in scripts:
        tree = ast.parse(safe(ROOT, script).read_text(), filename=script)
        names = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                names.update(alias.name.split('.')[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom):
                require(node.level == 0 and node.module, 'RELATIVE_IMPORT_NOT_ALLOWLISTED: ' + script)
                names.add(node.module.split('.')[0])
            elif isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                require(node.func.id not in {'eval', 'exec', 'compile', '__import__'}, 'DYNAMIC_CODE_NOT_ALLOWED: ' + script)
        require(names <= sys.stdlib_module_names, 'NON_STDLIB_IMPORT: ' + script)
        require(not (names & {'subprocess', 'socket', 'urllib', 'http', 'requests', 'runpy', 'importlib'}), 'EXECUTION_OR_NETWORK_IMPORT: ' + script)
        imports[script] = sorted(names)
    result = {
        'status': 'PASS_SOURCE_ARCHIVE_AND_RECORDED_RECEIPT_BINDINGS',
        'review_commit': index['review_commit'],
        'received_files_verified': received,
        'original_affine_archive_sha256': sha(archive.read_bytes()),
        'original_affine_archive_extracted_byte_equal': True,
        'current_and_historical_source_bindings_verified': len(index['bindings']),
        'final_report_source_bindings_verified': len(report_sources),
        'reported_pdf_pages': qa['pages'],
        'positive_owned_checker_imports': imports,
        'received_files_executed': False,
        'proof_assistants_run': False,
        'claim_limit': 'Exact bytes and recorded evidence bindings, not a fresh compiler/kernel replay.',
    }
    (ROOT / 'SOURCE_PIN_CHECKS.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
