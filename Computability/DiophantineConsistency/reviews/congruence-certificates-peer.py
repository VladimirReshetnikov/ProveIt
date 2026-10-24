#!/usr/bin/env python3
"""Read-only archive authentication and scratch positive/integer replays.

Intentionally does not run direct components, legacy H10 emitters, any
coefficient generator, or any proof assistant. Complete fixed tuples are
authenticated against independently retained earlier payload bytes.
"""
import argparse
import ast
from concurrent.futures import ThreadPoolExecutor
import gzip
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ARCHIVE = REPO / 'docs/incoming/ConZFC_Congruence_Certificates_2026-10-24.zip'
ARCHIVE_SHA = 'f4119b01e56f586558f0910c6deb21b83c82dfc324f884d7d95d28500ef09e63'
PYTHON = Path('/tmp/proofs62ff-wave7-review-venv/bin/python')


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def tuple_binding(package):
    reports = {}
    positive = package / 'positive/coefficients'
    binding = load(positive / 'BINDING.json')
    compact = ROOT / 'candidates/split116-compact/compact57/coefficients/compact_tuple'
    rows = {}
    for name, entry in binding['ports'].items():
        packed = (positive / entry['file']).read_bytes()
        raw = gzip.decompress(packed)
        need(digest(packed) == entry['sha256_gzip'] and digest(raw) == entry['sha256_raw'], 'positive packed/raw payload')
        old = compact / (entry['upstream_port'] + '.bin.gz')
        need(raw == gzip.decompress(old.read_bytes()), 'whole compact44 fixed port equals earlier retained bytes')
        need(len(raw) == entry['raw_bytes'] and int.from_bytes(raw, 'little').bit_length() == entry['bits'], 'positive payload dimensions')
        rows[name] = dict(raw_sha256=digest(raw), matched_earlier=str(old.relative_to(ROOT)))
    reports['positive_compact44'] = rows
    integer = package / 'integer/coefficients'
    fixed = ROOT / 'candidates/fixed-prime-compact-norms/coefficients'
    binding = load(integer / 'BINDING.json')
    earlier = load(fixed / 'BINDING.json')
    coefficients = {}
    rows = {}
    for name, entry in binding['payloads'].items():
        raw = gzip.decompress((integer / entry['file']).read_bytes())
        old = fixed / earlier['ports'][name]['file']
        need(digest(raw) == entry['raw_sha256'] and raw == gzip.decompress(old.read_bytes()), 'whole source34/determinant tuple matches earlier retained bytes')
        need(len(raw) == entry['raw_bytes'], 'integer payload length')
        value = int.from_bytes(raw, 'little')
        need(value.bit_length() == entry['bits'], 'integer payload width')
        coefficients[name] = value
        rows[name] = dict(raw_sha256=digest(raw), matched_earlier=str(old.relative_to(ROOT)))
    need(coefficients['beta'] == 2**1064921 - 1, 'literal integer Mersenne coefficient')
    reports['integer_source34'] = rows
    return reports, coefficients


def integer_literal_checks(directory, coefficients):
    # Execute only reviewed pure finite-algebra functions. In particular omit
    # constants(), which would execute an unnecessary archival recipe.
    names = {'need', 'evaluate', 'conjugate_product', 'trim', 'padd', 'pmul', 'degree_slice', 'check_packet'}
    tree = ast.parse((directory / 'verify.py').read_text())
    nodes = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom)) or isinstance(n, ast.FunctionDef) and n.name in names]
    need({n.name for n in nodes if isinstance(n, ast.FunctionDef)} == names, 'exact finite checker functions')
    scope = {'__name__': '_reviewed_integer_finite_algebra'}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), 'reviewed-finite-integer-checks', 'exec'), scope)
    output = []
    for n, degree in [(13, 1072), (14, 414), (15, 218), (16, 124)]:
        path = directory / 'equations' / ('integer%d_crt_valuation_degree%d.json' % (n, degree))
        output.append(scope['check_packet'](path, coefficients))
    return dict(status='PASS', source_sha256=digest((directory / 'verify.py').read_bytes()),
                functions=sorted(names), no_coefficient_recipe_executed=True, circuits=output)


def run_mode(package, coefficients, optimized):
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='congruence-peer-' + ('optimized-' if optimized else 'normal-')) as temporary:
        work = Path(temporary)
        for component in ('positive', 'integer'):
            shutil.copytree(package / component, work / component)
        prefix = [str(PYTHON), '-B'] + (['-O'] if optimized else [])
        records = []
        for label, directory, command in [('positive', 'positive', ['check.py']),
            ('integer-independent-norms', 'integer', ['independent_review/check.py']),
            ('integer-literal-rebuild', 'integer', ['build.py'])]:
            run = subprocess.run(prefix + command, cwd=work / directory, capture_output=True)
            need(run.returncode == 0, label + ' failed: ' + (run.stdout + run.stderr).decode(errors='replace')[-4000:])
            records.append(dict(check=label, status='PASS', command=prefix+command, stdout_sha256=digest(run.stdout)))
        regenerated = []
        for n, degree in [(13, 1072), (14, 414), (15, 218), (16, 124)]:
            relative = 'equations/integer%d_crt_valuation_degree%d.json' % (n, degree)
            raw = (work / 'integer' / relative).read_bytes()
            need(raw == (package / 'integer' / relative).read_bytes(), 'exact literal integer regeneration')
            regenerated.append(dict(path=relative, sha256=digest(raw)))
        # This pure checker call lives in this interpreter; the selected child
        # checks and every actual builder were also run under the requested -O.
        literals = integer_literal_checks(work / 'integer', coefficients)
        return dict(status='PASS', optimized_children=optimized, runs=records,
                    integer_byte_identical_rebuilds=regenerated, actual_integer_coefficients=literals,
                    positive_report=load(work / 'positive' / ('CHECKS_OPTIMIZED.json' if optimized else 'CHECKS.json')),
                    integer_exact_norm_report=load(work / 'integer/independent_review' / ('CHECKS_OPTIMIZED.json' if optimized else 'CHECKS.json')),
                    elapsed_seconds=round(time.monotonic() - started, 3))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT / 'reviews/congruence-certificates-peer.json')
    args = parser.parse_args()
    need(PYTHON.exists(), 'SymPy Python runtime')
    need(digest(ARCHIVE.read_bytes()) == ARCHIVE_SHA, 'complete incoming archive pin')
    with tempfile.TemporaryDirectory(prefix='congruence-peer-authenticated-') as temporary:
        with zipfile.ZipFile(ARCHIVE) as archive:
            info = archive.infolist()
            need(len(info) == 205, 'whole archive member count')
            for item in info:
                name = PurePosixPath(item.filename)
                need(not name.is_absolute() and '..' not in name.parts and ((item.external_attr >> 16) & 0o170000) != 0o120000, 'safe regular archive member')
                if not item.is_dir():
                    path = Path(temporary) / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(archive.read(item))
        package = Path(temporary) / 'con_zfc_congruence_certificates'
        manifest = load(package / 'MANIFEST.json')
        for entry in manifest['files']:
            raw = (package / entry['path']).read_bytes()
            need(len(raw) == entry['bytes'] and digest(raw) == entry['sha256'], 'complete delivered manifest entry')
        tuples, coefficients = tuple_binding(package)
        with ThreadPoolExecutor(max_workers=2) as pool:
            modes = list(pool.map(lambda opt: run_mode(package, coefficients, opt), (False, True)))
        result = dict(status='PASS', archive=str(ARCHIVE.relative_to(REPO)), archive_sha256=ARCHIVE_SHA,
            archive_members=len(info), archive_uncompressed_bytes=sum(i.file_size for i in info),
            manifest_files_checked=len(manifest['files']), complete_fixed_tuple_byte_comparisons=tuples,
            replays=modes, python_driver_optimized=bool(sys.flags.optimize),
            excluded_components=['direct (queued; not needed for positive/integer review)',
                                 'legacy H10 emitters', 'archival coefficient generators', 'all Lean/proof-assistant execution'],
            scope='Ordinary positive/integer proof peer review plus exact fixed-tuple binding, complete circuit replays, selected cleared-norm identities and exact degree witnesses. Internal object-ZFC derivation remains separate.')
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print(json.dumps(dict(status='PASS', archive_members=len(info), manifest_files=len(manifest['files']),
                             replay_modes=2, whole_tuple_ports=10, output=str(args.output)), indent=2))


if __name__ == '__main__':
    main()
