#!/usr/bin/env python3
"""Rebuild and independently audit the delivered solid-torus gadget fixtures.

Requires the Regina Python module in addition to the standard library.  The
native source modules are loaded from this package's repro/fast directory.
Every expensive solid-torus recognition call runs in a fresh subprocess with
an explicit timeout; a timeout is recorded as unverified, never as True.

Example from any directory:
    python scripts/audit_fixtures.py --output reproduced/fixture_controls.json

The output file must not already exist.  No native source module is modified.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys
import time


def file_digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def data_digest(value):
    encoded = json.dumps(value, sort_keys=True, separators=(',', ':')).encode()
    return hashlib.sha256(encoded).hexdigest()


def regina_triangulation(raw):
    """Construct Regina tetrahedra directly from declared source face pairings."""
    import regina

    result = regina.Triangulation3()
    for _ in raw['tetrahedra']:
        result.newTetrahedron()
    for index, row in enumerate(raw['tetrahedra']):
        for face, entry in enumerate(row):
            if entry is None or result.tetrahedron(index).adjacentTetrahedron(face):
                continue
            result.tetrahedron(index).join(
                face, result.tetrahedron(entry['tetrahedron']),
                regina.Perm4(*entry['permutation']))
    return result


def recognition_worker():
    raw = json.load(sys.stdin)
    tri = regina_triangulation(raw)
    start = time.perf_counter()
    answer = tri.isSolidTorus()
    print(json.dumps({'status': 'completed', 'is_solid_torus': bool(answer),
                      'recognition_seconds': time.perf_counter() - start}))
    return 0


def recognize_with_timeout(raw, timeout):
    start = time.perf_counter()
    try:
        process = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()), '--recognition-worker'],
            input=json.dumps(raw), text=True, capture_output=True,
            timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return {'status': 'timeout', 'is_solid_torus': None,
                'timeout_seconds': timeout,
                'subprocess_seconds': time.perf_counter() - start,
                'scope': 'Recognition not established by this timed call.'}
    elapsed = time.perf_counter() - start
    if process.returncode:
        return {'status': 'error', 'is_solid_torus': None,
                'exit_code': process.returncode, 'stderr': process.stderr,
                'subprocess_seconds': elapsed}
    result = json.loads(process.stdout)
    result['subprocess_seconds'] = elapsed
    result['timeout_seconds'] = timeout
    return result


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=root / 'provenance/fixture_controls.json')
    parser.add_argument('--recognition-timeout', type=float, default=5.0)
    parser.add_argument('--recognition-worker', action='store_true',
                        help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.recognition_worker:
        return recognition_worker()
    if not 0 < args.recognition_timeout <= 60:
        parser.error('recognition timeout must lie in (0, 60] seconds')
    output = args.output.resolve()
    if output.exists():
        parser.error('output already exists: ' + str(output))

    fast = root / 'repro/fast'
    sys.path.insert(0, str(fast))
    import regina
    from causal_research.fixtures import descent_gadgets
    from fastunknot.pachner_commitments import _State, _events

    source_files = [
        'causal_research/fixtures.py',
        'normal_orbit_research/fixtures.py',
        'fastunknot/normal_cocycle.py',
        'fastunknot/normal_surface_geometry.py',
        'fastunknot/pachner_commitments.py',
    ]
    hashes = {name: file_digest(fast / name) for name in source_files}
    cases = []
    total_start = time.perf_counter()
    for gadgets in (1, 2, 4, 8):
        case_start = time.perf_counter()
        fixture = descent_gadgets(gadgets)
        raw, heights = fixture['triangulation'], fixture['heights']
        count = len(raw['tetrahedra'])
        construction_seconds = time.perf_counter() - case_start

        start = time.perf_counter()
        events = _events(_State(raw, heights, tuple(range(count)), 0, 0, ()),
                         True, lambda: None)
        upward = sum(event.kind == 'up' for event in events)
        downward = sum(event.kind == 'down' for event in events)
        native_seconds = time.perf_counter() - start

        start = time.perf_counter()
        tri = regina_triangulation(raw)
        boundaries = [dict(real=boundary.isReal(), ideal=boundary.isIdeal(),
                           orientable=boundary.isOrientable(),
                           euler_characteristic=boundary.eulerChar(),
                           triangles=boundary.countTriangles())
                      for boundary in tri.boundaryComponents()]
        properties = dict(valid=tri.isValid(), orientable=tri.isOrientable(),
                          connected=tri.isConnected(), ideal=tri.isIdeal(),
                          vertices=tri.countVertices(), edges=tri.countEdges(),
                          triangles=tri.countTriangles(), tetrahedra=tri.size(),
                          boundary_components=boundaries, iso_signature=tri.isoSig(),
                          legal_initial_upward=sum(tri.hasPachner(face)
                                                   for face in tri.triangles()),
                          legal_initial_downward=sum(tri.hasPachner(edge)
                                                     for edge in tri.edges()))
        properties['one_torus_boundary'] = (
            len(boundaries) == 1 and boundaries[0]['real']
            and not boundaries[0]['ideal'] and boundaries[0]['orientable']
            and boundaries[0]['euler_characteristic'] == 0)
        regina_seconds = time.perf_counter() - start
        recognition = recognize_with_timeout(raw, args.recognition_timeout)

        checks = dict(
            expected_source_size=(count == 1 + 6 * gadgets),
            native_source_validated=True,
            native_no_initial_downward=(downward == 0),
            native_upward_count_8g=(upward == 8 * gadgets),
            regina_valid=properties['valid'],
            regina_orientable=properties['orientable'],
            regina_connected=properties['connected'],
            regina_finite=(not properties['ideal']),
            regina_one_torus_boundary=properties['one_torus_boundary'],
            independent_move_counts_agree=(
                properties['legal_initial_upward'] == upward
                and properties['legal_initial_downward'] == downward),
        )
        case = dict(gadget_count=gadgets, source_tetrahedra=count,
                    source_sha256=data_digest(raw), heights_sha256=data_digest(heights),
                    native_initial_upward=upward, native_initial_downward=downward,
                    regina=properties, solid_torus_recognition=recognition,
                    checks=checks, structural_controls_passed=all(checks.values()),
                    timing_seconds=dict(fixture_construction=construction_seconds,
                                        native_move_inventory=native_seconds,
                                        regina_structural_controls=regina_seconds,
                                        total=time.perf_counter() - case_start))
        cases.append(case)
        print('g=%d, t=%d, native(up,down)=(%d,%d), structural=%s, solid_torus=%s'
              % (gadgets, count, upward, downward, case['structural_controls_passed'],
                 recognition['is_solid_torus']), flush=True)

    changed = [name for name, digest in hashes.items()
               if file_digest(fast / name) != digest]
    result = dict(
        schema='causal-fixture-controls-v1',
        timestamp_utc=datetime.now(timezone.utc).isoformat(),
        baseline_revision='8188525b70033dcfe7c51ea5ae2c8723ad0c0198',
        python=sys.version, executable=sys.executable, platform=platform.platform(),
        regina_version=regina.versionString(), packaged_fast_source='repro/fast',
        source_module_sha256=hashes, audit_script_sha256=file_digest(Path(__file__)),
        changed_source_modules=changed,
        recognition_timeout_seconds=args.recognition_timeout,
        all_structural_controls_passed=(not changed and all(
            case['structural_controls_passed'] for case in cases)),
        all_solid_tori_independently_recognized=all(
            case['solid_torus_recognition']['is_solid_torus'] is True for case in cases),
        elapsed_seconds=time.perf_counter() - total_start, cases=cases,
        scope=('Source-fixture controls only; no complete bounded search for g=4 or g=8 '
               'is performed here. Recognition timeouts, if any, are left unverified.'))
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print('Saved ' + str(output))
    bad_recognition = any(case['solid_torus_recognition']['status'] == 'error'
                         or case['solid_torus_recognition']['is_solid_torus'] is False
                         for case in cases)
    return 0 if result['all_structural_controls_passed'] and not bad_recognition else 1


if __name__ == '__main__':
    raise SystemExit(main())
