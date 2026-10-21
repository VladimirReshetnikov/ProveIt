"""Validate the exact published predecessor in place, without copying its archive.

Only exact-pinned local Python validators are imported. No archive member is
executed. Relocation changes the repository root, never the relative identity.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

HERE = Path(__file__).resolve().parent
REFERENCE_SHA256 = '747f828b360d11a69efe0deb8e9cb859d7dafc434be8014a417454796348bdb8'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def reference(data=None):
    data = (HERE / 'basis-reference.json').read_bytes() if data is None else data
    assert sha(data) == REFERENCE_SHA256, 'Changed predecessor reference'
    return json.loads(data)


def locate(repo=None):
    ref = reference()
    candidates = [Path(repo).resolve()] if repo is not None else list(HERE.parents)
    for root in candidates:
        packet = root / ref['repository_relative_directory']
        if packet.is_dir():
            return root, packet
    raise AssertionError('Published phase5 packet missing; provide --basis-repo /path/to/Proofs')


def pinned_files(repo=None, supplied_reference=None):
    ref = reference(supplied_reference)
    root, packet = locate(repo)
    data = {}
    for name, pin in ref['files'].items():
        path = packet / name
        assert path.is_file() and not path.is_symlink(), path
        value = path.read_bytes()
        assert len(value) == pin['bytes'] and sha(value) == pin['sha256'], name
        data[name] = value
    return packet, data, ref


def validate(repo=None, supplied_reference=None):
    packet, files, ref = pinned_files(repo, supplied_reference)
    # Bind imports explicitly, so another installed module with a matching name
    # cannot replace a predecessor validator. Restore the caller's module table.
    names = ('phase3_evidence', 'phase4_evidence', '_phase5_pinned_evidence')
    saved = {name: sys.modules.get(name) for name in names}
    try:
        for name, filename in zip(names, ('phase3_evidence.py', 'phase4_evidence.py', 'evidence.py')):
            spec = importlib.util.spec_from_file_location(name, packet / filename)
            module = importlib.util.module_from_spec(spec)
            sys.modules[name] = module
            spec.loader.exec_module(module)
        validator = sys.modules[names[-1]]
        index = json.loads(files['index.json'])
        summary = json.loads(files['result.json'])
        assert sha(files['execution.tar.gz']) == summary['execution_archive_sha256']
        prior = validator.read_archive(files['execution.tar.gz'], index)
        assert len(prior) == summary['archive_members']
        raw = json.loads(prior['execution/result.json'])
        assert sha(prior['execution/result.json']) == ref['raw_result_sha256']
        assert all(summary[k] == v for k, v in raw.items())
        live_bytes = prior.pop('review/live-review.json')
        live = json.loads(live_bytes)
        assert live_bytes == files['live-review.json']
        assert sha(live_bytes) == summary['live_review_sha256']
        assert live['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
        for filename, key in [('review.py', 'reviewer_sha256'), ('evidence.py', 'validator_sha256'),
                              ('capture.py', 'capture_sha256')]:
            assert sha(prior['review/' + filename]) == live[key]
        for filename in ('evidence.py', 'review_saved.py', 'phase4_evidence.py', 'phase3_evidence.py'):
            assert files[filename] == prior['review/' + filename]
        assert validator.manifest_hash(prior) == live['evidence_manifest_sha256']
        assert live['all184_objects_rehashed_after_audits']
        assert live['all185_basis_objects_and_logs_unchanged']
        assert live['current_inventory_exact'] and live['toolchain_and_compiler_rehashed']
        checked = validator.validate(prior)
        assert all(live[k] == v for k, v in checked.items())
        assert summary['compiled_objects_in_archive'] is False
        assert summary['audit_warnings'] == 0 and summary['project_warnings'] == checked['project_warnings']
        # No later read may silently substitute changed predecessor bytes.
        assert pinned_files(repo, supplied_reference)[1] == files
        return prior, checked, files
    finally:
        for name, value in saved.items():
            if value is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = value
