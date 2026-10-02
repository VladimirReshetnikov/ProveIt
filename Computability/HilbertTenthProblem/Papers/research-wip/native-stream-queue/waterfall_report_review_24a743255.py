"""Replay the complete pinned Waterfall report review in private directories.

Original archive bytes remain unchanged. A retired intake is recovered from
its arrival commit. Run with assertions enabled; no nonstandard package needed.
"""
import argparse
from contextlib import contextmanager
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys
import tempfile
import types
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
ARCHIVE = 'Waterfall_Diophantine_Certificates.zip'
ARCHIVE_SHA = 'b5d3ee90f9631695afc3c6f34f765b617eb9c631c65ab32705cf3d0e8811a9fc'
ARRIVAL = '24a743255'
PREFIX = 'waterfall-diophantine'
RUNS = ('verify_matrix_definition.py', 'verify_frontend.py',
        'verify_frontend_independent.py', 'grouped_quadratic.py',
        'verify_quadratic_independent.py', 'verify_halting_example.py',
        'verify_certificates.py', 'verify_release.py')
HELPERS = {
    'frontend': ('waterfall_frontend_review.py', '97c7bb8f820647ea47fafd826c9fc2a9d0dd2a218f011f2ca961af02a199e2c3'),
    'polynomial': ('waterfall_polynomial_review.py', 'c4af73ee8d59fa497f68cf3f6a54fca4146dd759656d57b859c5ccb3f937fd52'),
    'endpoint': ('waterfall_endpoint_alias.py', '0fae44cec255d3387747a24cd9b97df3c22e090c8a3299ccc6d7f6a0b098090b'),
    'projection': ('waterfall_forced_boundary_review.py', '43433a7f16ad325493ebcd7fb3c8c4342f033c7bf8e1ce0292b760f60d924999'),
    'compiler': ('waterfall_forced_boundary_projection.py', '56c2c9eabad9faa51b66e02315264c93da0c9915cb406badfa1822a188f0b747'),
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def archive(*, from_git=False):
    path = ROOT/'docs'/'incoming'/ARCHIVE
    raw = path.read_bytes() if path.exists() and not from_git else subprocess.run(
        ['git', 'show', f'{ARRIVAL}:docs/incoming/{ARCHIVE}'], cwd=ROOT,
        capture_output=True, check=True, timeout=60).stdout
    if sha(raw) != ARCHIVE_SHA:
        raise ValueError('Waterfall archive hash mismatch')
    return raw


def members(raw):
    result = {}
    with ZipFile(io.BytesIO(raw)) as z:
        seen = set()
        for item in z.infolist():
            p = PurePosixPath(item.filename)
            if (p.is_absolute() or not p.parts or p.parts[0] != PREFIX
                    or '..' in p.parts or '\\' in item.filename or str(p) in seen
                    or stat.S_ISLNK(item.external_attr >> 16)):
                raise ValueError('Unsafe/duplicate archive member')
            seen.add(str(p))
            if not item.is_dir():
                result[str(p)] = z.read(item)
    if len(result) != 31:
        raise ValueError('Unexpected member count')
    return result


def extract(files, destination):
    for name, raw in files.items():
        path = destination/name
        if not path.resolve().is_relative_to(destination.resolve()):
            raise ValueError('Unsafe extraction path')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


@contextmanager
def helper(which):
    filename, digest = HELPERS[which]
    path = HERE/filename
    raw = path.read_bytes()
    if sha(raw) != digest:
        raise ValueError('Review helper hash mismatch: '+filename)
    name = '_waterfall_review_'+which
    absent = object()
    previous = sys.modules.get(name, absent)
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    try:
        exec(compile(raw, str(path), 'exec'), module.__dict__)
        yield module
    finally:
        if previous is absent:
            sys.modules.pop(name, None)
        else:
            sys.modules[name] = previous


def compare_receipt(name, result):
    saved = json.loads((HERE/name).read_text())
    assert saved == json.loads(json.dumps(result)), name+' replay differs'
    return result


def run():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    raw = archive()
    assert archive(from_git=True) == raw
    files = members(raw)
    inventory = {name: dict(bytes=len(data), sha256=sha(data)) for name, data in files.items()}
    with tempfile.TemporaryDirectory(prefix='waterfall-complete-review-') as temp:
        work = Path(temp)
        extract(files, work/'author')
        author = work/'author'/PREFIX
        runs = []
        for name in RUNS:
            done = subprocess.run([sys.executable, 'replay/'+name], cwd=author,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'),
                capture_output=True, text=True, timeout=300)
            assert done.returncode == 0, (name, done.stdout, done.stderr)
            runs.append(dict(command='python replay/'+name, status='PASS'))
        assert all((work/'author'/name).read_bytes() == data for name, data in files.items())
        extract(files, work/'independent')
        source = work/'independent'/PREFIX
        results = {}
        with helper('frontend') as h:
            results['frontend'] = compare_receipt('waterfall_frontend_review.json', h.verify(source))
        (work/'polynomial').mkdir()
        with helper('polynomial') as h:
            results['polynomial'] = compare_receipt('waterfall_polynomial_review.json',
                h.main_checks(source, HERE/'waterfall_grouped_exact_domains.patch', work/'polynomial'))
        (work/ARCHIVE).write_bytes(raw)
        with helper('endpoint') as h:
            results['endpoint'] = compare_receipt('waterfall_endpoint_alias.json',
                h.verify(archive=work/ARCHIVE))
        with helper('projection') as h:
            results['projection'] = compare_receipt('waterfall_forced_boundary_review.json',
                h.verify(HERE/'waterfall_forced_boundary_projection.py',
                    source/'replay/grouped_quadratic.py', HERE/'waterfall_polynomial_review.py'))
        with helper('compiler') as h:
            saved_path = HERE/'waterfall_forced_boundary_projection.json'
            saved = json.loads(saved_path.read_text())
            compiled = h.build(7, 'ends')
            assert json.loads(json.dumps(compiled)) == saved['complete_seven_step_compiler']
            assert h.canonical_assignment(compiled, 6, 0) == saved['seven_step_zero']
            assert h.evaluate(compiled, saved['seven_step_zero']) == 0
            assert saved['ledgers'] == results['projection']['ledgers']
            results['compiler_export'] = dict(status='PASS',
                saved_receipt_sha256=sha(saved_path.read_bytes()),
                complete_seven_step_export_and_zero_match=True,
                all_saved_ledgers_match_independent_source_audit=True)
        assert all((work/'independent'/name).read_bytes() == data for name, data in files.items())
    return dict(status='PASS', archive=ARCHIVE, arrival=ARRIVAL, archive_sha256=ARCHIVE_SHA,
        review_source_sha256=sha(Path(__file__).read_bytes()), helpers=HELPERS,
        original_member_inventory=inventory, original_runs=runs,
        unchanged_original_members=31, git_fallback_checked=True, independent=results,
        scope='Reviewed all-value proofs plus finite exact replays; original archive unchanged; '
              'patches are separate artifacts. Fixed-horizon projection is a complete bounded '
              'polynomial; the universal 87-operation bound is unchanged.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = run()
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == json.loads(json.dumps(result)), 'Saved review differs'
    print(json.dumps(dict(status='PASS', original_author_commands=8,
        original_members=31, independent_groups=len(result['independent']), receipt=str(receipt)), indent=2))
