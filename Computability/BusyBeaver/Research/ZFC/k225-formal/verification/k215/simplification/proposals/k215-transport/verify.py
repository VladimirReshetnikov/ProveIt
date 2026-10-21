#!/usr/bin/env python3
"""Audit the delivered packet without mutating its contents.

Default: hashes, literal table bindings, dense/native equality, and every
local invariant window. Optional source regeneration or search replay is
explicit. Formal kernel builds use the separate build_formal.py driver.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    start = None
    rows = {}
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line[9:])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            key = int(q), int(b)
            assert key not in rows and int(b) in (0, 1)
            assert int(w) in (0, 1) and d in ('L', 'R')
            rows[key] = int(w), d, int(z)
    assert start is not None
    return start, rows


def run(command, cwd, log):
    with log.open('w') as output:
        result = subprocess.run(command, cwd=cwd, stdout=output,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}); see {log}')


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are required.')
    ap = argparse.ArgumentParser()
    ap.add_argument('--work', type=Path)
    ap.add_argument('--source', action='store_true')
    ap.add_argument('--search', action='store_true')
    ap.add_argument('--full-search', action='store_true')
    args = ap.parse_args()
    if args.work:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=False)
    else:
        work = Path(tempfile.mkdtemp(prefix='k215-packet-'))

    manifest = json.loads((HERE/'MANIFEST.json').read_text())
    for entry in manifest['files']:
        path = HERE/entry['path']
        assert path.is_file(), entry['path']
        assert path.stat().st_size == entry['bytes'], entry['path']
        assert sha(path) == entry['sha256'], entry['path']

    # Independent dense/native relabeling check; sorted working labels,
    # with the separate terminal assigned dense control 215.
    for stem in ('baseline215', 'marker215'):
        start, native = table(HERE/'machines'/f'{stem}.native.tm')
        dstart, dense = table(HERE/'machines'/f'{stem}.tm')
        controls = sorted({q for q, b in native})
        assert len(controls) == 215 and len(native) == len(dense) == 430
        assert all((q,b) in native for q in controls for b in (0,1))
        halts = {a[2] for a in native.values()}-set(controls)
        assert len(halts) == 1
        mapping = {q:i for i,q in enumerate(controls)}
        mapping[next(iter(halts))] = 215
        assert mapping[start] == dstart == 0
        assert dense == {(mapping[q],b):(w,d,mapping[z])
                         for (q,b),(w,d,z) in native.items()}
        assert (HERE/'formal'/f'{stem}.tm').read_bytes() == \
               (HERE/'machines'/f'{stem}.tm').read_bytes()

    local = work/'local'; local.mkdir()
    for name in ['CM215Tables.lean','baseline215.tm','marker215.tm',
                 'check_lean_binding.py','check_marker_certificate.py']:
        shutil.copyfile(HERE/'formal'/name, local/name)
    for script, output in [('check_lean_binding.py','lean_binding.json'),
                           ('check_marker_certificate.py','marker_certificate.json')]:
        run([sys.executable,'-B',script],local,work/(script+'.log'))
        actual = json.loads((local/output).read_text())
        expected = json.loads((HERE/'formal'/output).read_text())
        assert actual == expected, output

    record = {'status':'PACKET_IDENTITY_AND_LOCAL_AUDIT_PASS',
              'manifest_entries':len(manifest['files']),
              'native_dense_bijections':2,
              'exact_lean_literal_rows':860,
              'admissible_local_windows':1710,
              'source_analysis_recomputed':False,
              'search_replay':None,
              'kernel_build_performed':False}
    if args.source:
        target=work/'source_analysis'
        shutil.copytree(HERE/'source_analysis',target)
        run([sys.executable,'-B','analyze_source.py'],target,work/'source.log')
        for name in ['source_analysis.json','quotient_certificate.json']:
            assert json.loads((target/name).read_text()) == \
                   json.loads((HERE/'source_analysis'/name).read_text()), name
        record['source_analysis_recomputed']=True
    if args.search or args.full_search:
        command=[sys.executable,'-B',str(HERE/'reduction_search/verify.py'),
                 '--replay','full' if args.full_search else 'inherited',
                 '--work',str(work/'search')]
        if not args.full_search:
            command += ['--name','primary','--domain','all']
        run(command,HERE,work/'search.log')
        record['search_replay']=json.loads((work/'search/verification.json').read_text())
    (work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
    print(f'Audit record: {work/"verification.json"}')


if __name__ == '__main__':
    main()
