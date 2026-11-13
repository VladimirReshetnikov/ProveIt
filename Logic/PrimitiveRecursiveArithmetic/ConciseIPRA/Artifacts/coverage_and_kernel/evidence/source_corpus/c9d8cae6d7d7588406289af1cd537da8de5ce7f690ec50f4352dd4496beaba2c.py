"""Reproduce the pinned source-corpus measurements entirely offline.

This parses and measures every .py archive member; it never imports or executes
those source modules. Only the unchanged reference/source_measure.py utility
is imported. The measured corpus is exhaustive, but deciding whether a source
is a complete proof checker is a separate semantic review, recorded in
evidence/corpus_audit.md rather than inferred by this script.
"""
import hashlib
import importlib.util
import io
import json
from pathlib import Path, PurePosixPath
import platform
import sys
import tempfile
import zipfile


ROOT = Path(__file__).resolve().parent
METRICS = {
    'tokens': 'normalized_tokens',
    'ast': 'ast_nodes',
    'bytes': 'normalized_bytes',
}
BOUNDARY = (
    'Exhaustive archive identity and Python-source measurements only. '
    'Semantic classification of complete theorem checkers is recorded in '
    'evidence/corpus_audit.md; this script does not infer it from size, '
    'filenames, imports, or source text and does not execute corpus modules.'
)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git_blob_sha1(data):
    header = b'blob ' + str(len(data)).encode('ascii') + b'\0'
    return hashlib.sha1(header + data).hexdigest()


def main():
    snapshot_path = ROOT / 'evidence/repository_snapshot.json'
    expected_path = ROOT / 'evidence/corpus_source_metrics.json'
    measurer_path = ROOT / 'reference/source_measure.py'
    snapshot = json.loads(snapshot_path.read_text())
    expected = json.loads(expected_path.read_text())
    errors = []
    environment_ok = (
        platform.python_implementation() == 'CPython'
        and sys.version_info[:2] == (3, 12)
    )
    if not environment_ok:
        errors.append('Exact source-metric comparison requires CPython 3.12.')

    spec = importlib.util.spec_from_file_location('corpus_source_measure', measurer_path)
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)

    expected_by_hash = {}
    expected_by_path = {}
    for record in expected:
        digest = record['sha256']
        if digest in expected_by_hash:
            errors.append('Duplicate expected content identity: ' + digest)
        expected_by_hash[digest] = record
        for occurrence in record['occurrences']:
            if occurrence in expected_by_path:
                errors.append('Duplicate expected occurrence: ' + occurrence)
            expected_by_path[occurrence] = digest

    names = [record['name'] for record in snapshot['files']]
    if len(names) != len(set(names)):
        errors.append('Duplicate archive filename in the snapshot.')
    actual_names = {path.name for path in (ROOT / 'sources').glob('*.zip')}
    missing_archives = sorted(set(names) - actual_names)
    extra_archives = sorted(actual_names - set(names))
    errors.extend('Missing archive: ' + name for name in missing_archives)
    errors.extend('Unlisted archive: ' + name for name in extra_archives)

    archives = []
    measured_by_hash = {}
    measured_by_path = {}
    source_metric_calls = 0
    with tempfile.TemporaryDirectory(prefix='ipra_corpus_measure_') as temporary:
        scratch_source = Path(temporary) / 'member.py'
        for entry in snapshot['files']:
            name = entry['name']
            if name not in actual_names:
                continue
            if Path(name).name != name:
                errors.append('Archive name is not a basename: ' + name)
                continue
            data = (ROOT / 'sources' / name).read_bytes()
            actual = {
                'size': len(data),
                'blob_sha': git_blob_sha1(data),
                'sha256': sha256(data),
            }
            identity_ok = all(actual[key] == entry[key] for key in actual)
            archive_record = {
                'name': name,
                'repository_path': entry['path'],
                **actual,
                'identity_matches_snapshot': identity_ok,
                'python_members': 0,
            }
            archives.append(archive_record)
            if not identity_ok:
                for key in actual:
                    if actual[key] != entry[key]:
                        errors.append(name + ': archive ' + key + ' mismatch')
                continue

            try:
                archive = zipfile.ZipFile(io.BytesIO(data))
                with archive:
                    for member in sorted(archive.infolist(), key=lambda item: item.filename):
                        if member.is_dir() or not member.filename.endswith('.py'):
                            continue
                        member_path = PurePosixPath(member.filename)
                        if member_path.is_absolute() or '..' in member_path.parts:
                            errors.append(name + ': unsafe source-member path ' + member.filename)
                            continue
                        occurrence = Path(name).stem + '/' + str(member_path)
                        if occurrence in measured_by_path:
                            errors.append('Duplicate archive source occurrence: ' + occurrence)
                            continue
                        source = archive.read(member)
                        digest = sha256(source)
                        measured_by_path[occurrence] = digest
                        archive_record['python_members'] += 1
                        scratch_source.write_bytes(source)
                        try:
                            values = measure.metrics(scratch_source)
                        except (SyntaxError, UnicodeError, ValueError, TypeError) as error:
                            errors.append(occurrence + ': source measurement failed: ' + str(error))
                            continue
                        source_metric_calls += 1
                        compact = {short: values[long] for short, long in METRICS.items()}
                        if values['sha256'] != digest:
                            errors.append(occurrence + ': measurer content hash mismatch')
                        if digest not in measured_by_hash:
                            measured_by_hash[digest] = {
                                **compact, 'sha256': digest, 'occurrences': [],
                            }
                        elif any(measured_by_hash[digest][key] != compact[key] for key in METRICS):
                            errors.append(occurrence + ': duplicate content measured inconsistently')
                        measured_by_hash[digest]['occurrences'].append(occurrence)
            except (zipfile.BadZipFile, OSError, RuntimeError) as error:
                errors.append(name + ': archive reading failed: ' + str(error))

    missing_occurrences = sorted(set(expected_by_path) - set(measured_by_path))
    extra_occurrences = sorted(set(measured_by_path) - set(expected_by_path))
    errors.extend('Missing source occurrence: ' + path for path in missing_occurrences)
    errors.extend('Unexpected source occurrence: ' + path for path in extra_occurrences)
    for occurrence in sorted(set(expected_by_path) & set(measured_by_path)):
        if expected_by_path[occurrence] != measured_by_path[occurrence]:
            errors.append('Source-content hash differs: ' + occurrence)

    missing_hashes = sorted(set(expected_by_hash) - set(measured_by_hash))
    extra_hashes = sorted(set(measured_by_hash) - set(expected_by_hash))
    errors.extend('Missing source-content identity: ' + digest for digest in missing_hashes)
    errors.extend('Unexpected source-content identity: ' + digest for digest in extra_hashes)
    for digest in sorted(set(expected_by_hash) & set(measured_by_hash)):
        original, reproduced = expected_by_hash[digest], measured_by_hash[digest]
        for key in METRICS:
            if original[key] != reproduced[key]:
                errors.append(digest + ': ' + key + ' differs: expected '
                              + str(original[key]) + ', measured ' + str(reproduced[key]))
        if sorted(original['occurrences']) != sorted(reproduced['occurrences']):
            errors.append(digest + ': occurrence-path collection differs')

    measured_sources = sorted(measured_by_hash.values(), key=lambda record: record['sha256'])
    for record in measured_sources:
        record['occurrences'].sort()
    receipt = {
        'repository_commit': snapshot['sha'],
        'python': platform.python_version(),
        'implementation': platform.python_implementation(),
        'metric_environment_matches': environment_ok,
        'classification_boundary': BOUNDARY,
        'source_modules_executed': False,
        'bindings': {
            str(path.relative_to(ROOT)): sha256(path.read_bytes())
            for path in [snapshot_path, expected_path, measurer_path]
        },
        'archive_count': len(archives),
        'archive_bytes': sum(record['size'] for record in archives),
        'archive_identities_verified': sum(record['identity_matches_snapshot'] for record in archives),
        'python_source_occurrences': len(measured_by_path),
        'source_metric_calls': source_metric_calls,
        'distinct_python_source_hashes': len(measured_by_hash),
        'expected_python_source_occurrences': len(expected_by_path),
        'expected_distinct_python_source_hashes': len(expected_by_hash),
        'archive_records': archives,
        'measured_sources': measured_sources,
        'errors': errors,
        'passed': not errors,
    }
    output = ROOT / 'evidence/corpus_reproduction.json'
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({
        key: receipt[key] for key in [
            'repository_commit', 'python', 'archive_count', 'archive_bytes',
            'archive_identities_verified', 'python_source_occurrences',
            'source_metric_calls', 'distinct_python_source_hashes', 'passed', 'errors',
        ]
    }, indent=2))
    print(BOUNDARY)
    if errors:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
