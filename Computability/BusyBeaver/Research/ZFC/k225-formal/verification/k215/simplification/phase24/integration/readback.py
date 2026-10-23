#!/usr/bin/env python3
"""Post-copy byte/link readback only; CLI and manifest schema are in README.md."""
from pathlib import Path
from urllib.parse import unquote, urlsplit
import argparse, hashlib, json, re
PLAN_SHA = '4bda49c298304608bd3196d92a3c748140142e8a649708102d827e690f489505'
CORE = {'README.md', 'capture-config.json', 'capture.json', 'capture.py',
        'check-plan.json', 'check.py', 'evidence.tar.gz', 'index.json',
        'result-review.json', 'result.json', 'review_actual.py'}
digest = lambda data: hashlib.sha256(data).hexdigest()
def contents(path):
    path = Path(path)
    assert path.is_absolute() and path.is_file() and not path.is_symlink(), path
    return path.read_bytes()
def exact(path, hashed):
    assert re.fullmatch('[0-9a-f]{64}', hashed), hashed
    data = contents(path); assert digest(data) == hashed, path
    return data
p = argparse.ArgumentParser(description=__doc__)
for name in ['manifest', 'plan', 'previous-leaf', 'new-leaf', 'output']:
    p.add_argument('--' + name, type=Path, required=True)
p.add_argument('--manifest-sha', required=True)
p.add_argument('--docs', type=Path, nargs=4, required=True)
a = p.parse_args()
assert a.output.is_absolute() and not a.output.exists() and not a.output.is_symlink()
manifest_bytes = exact(a.manifest, a.manifest_sha)
manifest = json.loads(manifest_bytes); rows = manifest['files']
assert isinstance(rows, list) and rows
plan_bytes = exact(a.plan, PLAN_SHA); plan = json.loads(plan_bytes)
destinations = set()
for row in rows:
    source, destination = Path(row['source']), Path(row['destination'])
    assert destination not in destinations, destination
    destinations.add(destination)
    data = exact(source, row['sha256'])
    assert contents(destination) == data, destination
for leaf in [a.previous_leaf, a.new_leaf]:
    assert leaf.is_absolute() and leaf.is_dir() and not leaf.is_symlink(), leaf
    assert {path.name for path in leaf.iterdir()} == CORE, leaf
    for name in CORE: contents(leaf / name)
assert {a.new_leaf / name for name in CORE} <= destinations
assert len(plan['modules']) == 230 and len(plan['source_overlay']) == 13
assert len(plan['present_inputs']) == 102 and len(plan['absent_inputs']) == 16
for row in plan['modules']:
    assert len(exact(row['source'], row['source_sha256'])) == row['bytes']
for row in plan['source_overlay']:
    exact(row['canonical'], row['candidate']['sha256'])
for path, hashed in plan['present_inputs'].items(): exact(path, hashed)
for path in plan['absent_inputs']:
    assert not Path(path).exists() and not Path(path).is_symlink(), path
for name in CORE:
    path = a.previous_leaf / name
    exact(path, plan['present_inputs'][str(path)])
docs = set(a.docs); assert len(docs) == 4 and docs <= destinations
links = []
for doc in sorted(docs):
    assert doc.is_relative_to(a.new_leaf.parent) and doc.suffix == '.md', doc
    text = contents(doc).decode('utf-8')
    assert '${' not in text and not re.search(r'\bPENDING\b', text), doc
    text = re.sub(r'(?ms)^```[^\n]*\n.*?^```[^\n]*(?:\n|$)', '', text)
    targets = re.findall(r'\]\(\s*(<[^>\n]+>|[^\s)]+)', text)
    targets += re.findall(r'^\s*\[[^\]\n]+\]:\s*(<[^>\n]+>|\S+)', text, re.M)
    for target in targets:
        value = urlsplit(target.removeprefix('<').removesuffix('>'))
        if value.scheme or value.netloc or value.fragment or not value.path: continue
        relative = Path(unquote(value.path))
        if relative.is_absolute(): continue
        resolved = (doc.parent / relative).resolve()
        assert resolved.is_file(), (doc, target, resolved)
        links.append({'document': str(doc), 'target': target, 'resolved': str(resolved)})
report = {'status': 'PASS_POST_COPY_SOURCE_AND_DOCUMENT_READBACK_ONLY',
          'auditor_sha256': digest(contents(Path(__file__).absolute())),
          'manifest_sha256': digest(manifest_bytes), 'plan_sha256': digest(plan_bytes),
          'copied_files': len(rows), 'selected_sources': len(plan['modules']),
          'canonical_overlays': len(plan['source_overlay']), 'present_pins': len(plan['present_inputs']),
          'absences': len(plan['absent_inputs']), 'previous_leaf_files': len(CORE),
          'new_leaf_files': len(CORE), 'documents': [str(doc) for doc in sorted(docs)],
          'local_file_links': links, 'scope': 'Post-copy identity and local-link checks only; no proof recheck.',
          'compiler_execution': False, 'archive_extraction': False, 'captured_code_execution': False, 'network': False}
with a.output.open('x') as stream: json.dump(report, stream, indent=2); stream.write('\n')
