#!/usr/bin/env python3
"""Authenticate the whole arrival; replay only the reviewed nine-positive component.

No native coefficient generator, H10 emitter or proof assistant is executed.
The eight native payloads are instead byte-compared to earlier reviewed tuples.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ARCHIVE = REPO/'docs/incoming/ConZFC_Constructive_Reductions_2026-10-23.zip'
PIN = '37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(raw):
    return sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_text())


def zero_position_controls(source):
    for base in (source, source/'compact'):
        row = load(base/'data/source.json')['equations'][4]['terms']
        need(all(not any(t['powers'][-4:]) for t in row) and
             sum(t['coefficient'] for t in row) == 1,
             'all-one source excluded independently of fixed ports')
    cases = 0
    # Include zero as an occupied coordinate, with a forced empty middle digit.
    for B in (4, 8, 16):
        for b in (1, 2, 4):
            if b > B:
                continue
            mask = B**3-1-(b-1)*(1+B**2)
            for g in range(B**3):
                digits = (g % B, (g//B) % B, g//(B*B))
                allowed = digits[0] < b and digits[1] == 0 and digits[2] < b
                need((g & mask == 0) == allowed, 'position-zero mask finite control')
                cases += 1
    return dict(all_one_fifth_residual=1, fixed_ports_unused_in_that_row=True,
                position_zero_mask_assignments=cases,
                scope='Finite diagnostics; the universal digit and cofinality proofs are reviewed in prose.')


def run_mode(source, optimized):
    with tempfile.TemporaryDirectory(prefix='constructive-nine-replay-') as tmp:
        work = Path(tmp)/'nine'
        shutil.copytree(source, work)
        prefix = [sys.executable, '-B'] + (['-O'] if optimized else [])
        records = []
        # These scripts contain exact local composition and source-ring checks.
        # Their reviewed producers use only copied data and finite DAG algebra.
        for script in ('normalization_check.py', 'verify.py', 'exact_audit.py', 'build.py'):
            run = subprocess.run(prefix+[script], cwd=work, capture_output=True)
            need(run.returncode == 0, script+': '+(run.stdout+run.stderr).decode(errors='replace')[-3000:])
            records.append(dict(script=script, status='PASS', stdout_sha256=digest(run.stdout)))
        comparisons = []
        for original in sorted((source/'equations').glob('*.json')):
            rebuilt = work/'equations'/original.name
            need(rebuilt.read_bytes() == original.read_bytes(), 'entire rebuilt graph '+original.name)
            comparisons.append(dict(file=original.name, sha256=digest(original.read_bytes())))
        # gzip streams can differ across Python/zlib versions; compare their
        # complete decoded signed values and names, rather than compressed bytes.
        for profile in ('boundary', 'compact'):
            old = load(source/'fixed'/profile/'BINDING.json')['records']
            new = load(work/'fixed'/profile/'BINDING.json')['records']
            need([(r['name'], r['sign'], r['bits'], r['raw_sha256']) for r in old] ==
                 [(r['name'], r['sign'], r['bits'], r['raw_sha256']) for r in new], 'all regenerated fixed values')
            for r in old:
                need(gzip.decompress((source/r['path']).read_bytes()) ==
                     gzip.decompress((work/r['path']).read_bytes()), 'entire regenerated fixed magnitude')
        return dict(status='PASS', optimized=optimized, stages=records,
                    byte_identical_graphs=comparisons,
                    graph_checks=load(work/'VERIFICATION.json'),
                    source_and_radical_checks=load(work/'EXACT_AUDIT.json'),
                    normalization=load(work/'NORMALIZATION_CHECKS.json'),
                    fixed_values_rebuilt=23)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    need(digest(ARCHIVE.read_bytes()) == PIN, 'whole immutable incoming archive')
    with tempfile.TemporaryDirectory(prefix='constructive-nine-auth-') as tmp:
        with zipfile.ZipFile(ARCHIVE) as z:
            members = z.infolist()
            need(len(members) == 339, 'complete archive member inventory')
            for entry in members:
                name = PurePosixPath(entry.filename)
                need(not name.is_absolute() and '..' not in name.parts and
                     ((entry.external_attr >> 16) & 0o170000) != 0o120000, 'safe member')
                if not entry.is_dir():
                    target = Path(tmp)/str(name)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(z.read(entry))
        package = Path(tmp)/'ConZFC_Constructive_Reductions_2026-10-23'
        manifest = (package/'MANIFEST.sha256').read_text().splitlines()
        for line in manifest:
            pin, name = line.split('  ', 1)
            need(digest((package/name).read_bytes()) == pin, 'whole manifest entry '+name)
        source = package/'nine'
        controls = zero_position_controls(source)
        old_roots = {
            'boundary': ROOT/'candidates/saturated-h1868-d/source/data',
            'compact': ROOT/'candidates/split116-compact/compact54-sharp/coefficients/compact_tuple'}
        tuples = {}
        for profile, old_root in old_roots.items():
            base = source if profile == 'boundary' else source/'compact'
            result = {}
            for name in ('beta', 'K', 'MC', 'MF_source'):
                raw = gzip.decompress((base/'data'/(name+'.bin.gz')).read_bytes())
                old = gzip.decompress((old_root/(name+'.bin.gz')).read_bytes())
                need(raw == old, 'complete earlier native port '+profile+'/'+name)
                result[name] = dict(raw_bytes=len(raw), raw_sha256=digest(raw))
            tuples[profile] = result
        pin = load(source/'SOURCE_PINS.json')['ratio_lean']
        ratio = (REPO/pin['path']).read_bytes()
        retained = (source/'inherited/NineRatio.lean').read_bytes()
        need(digest(retained) == pin['sha256'], 'inert retained H10 ratio interface')
        need(retained == ratio+b'\n', 'retained interface differs only by one final LF')
        ratio_binding = dict(pin, current_sha256=digest(ratio),
                             harmless_byte_difference='one extra final LF in retained copy')
        with ThreadPoolExecutor(max_workers=2) as pool:
            modes = list(pool.map(lambda opt: run_mode(source, opt), (False, True)))
        result = dict(status='PASS', archive=str(ARCHIVE.relative_to(REPO)), archive_sha256=PIN,
            members=len(members), manifest_entries=len(manifest), whole_earlier_tuples=tuples,
            inert_ratio_interface=ratio_binding, replays=modes, driver_optimized=bool(sys.flags.optimize),
            independent_zero_position_controls=controls,
            scope='Nine-positive component only: ordinary layout/mask/population proof reviewed separately; full source/radical identities, circuits and fixed values replayed. Other arrival components, native generators, H10 emitters and Lean were not executed.')
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
        print(json.dumps(dict(status='PASS', members=len(members), manifest_entries=len(manifest),
                              ports=8, normal_and_optimized=True, output=str(args.output))))


if __name__ == '__main__':
    main()
