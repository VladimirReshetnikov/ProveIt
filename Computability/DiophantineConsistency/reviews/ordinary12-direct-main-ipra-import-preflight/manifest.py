#!/usr/bin/env python3
"""Capture, or check, the exact selected direct inputs and live cone overlay.

This is a point-in-time filesystem guard, not a Lean join or package audit.
"""
from hashlib import sha256
import json
import os
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]
SCAN = HERE / 'observations/attempt01/result.json'
OVERLAY_RESULT = HERE / 'observations/overlay01/result.json'
CONE = D / 'research/ordinary12-ipra-bridge/compact12-ipra-expanded-cone-preflight/result-v2.json'
PINS = {
    SCAN: '01c68aaea9e3548f25589694cbb0c4582f66c0fce7b072ba0d3a3765fec950a1',
    OVERLAY_RESULT: '385173546dacd65f2c441c8ed2fd0dfd2086e0a59b2f14a98fbc9a0c4ca1eeae',
    CONE: '35fce2dd6720ca1f2db8c39e42ad099f5653bf6b12939fcb77db3fd0fa252ed4',
}
LIB = Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib')
OUTPUT = HERE / 'observations/manifest01/result.json'
FINAL = HERE / 'observations/final01/result.json'
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir',
            '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ilean.hash', '.ir.hash')

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    need(path.is_file(), 'dangling or non-file: ' + str(path))
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}

def snapshot():
    for path, pin in PINS.items():
        need(digest(path) == pin, 'changed input: ' + str(path))
    scan = json.loads(SCAN.read_text())['roots']['DirectMainHalt']
    previous = json.loads(OVERLAY_RESULT.read_text())
    cone = set(json.loads(CONE.read_text())['topological_candidate'])
    modules = set(scan['selected_ancestors'])
    need(len(modules) == 765 and len(cone) == 425 and not modules & cone, 'unexpected sets')
    need(set(previous['records']) == modules, 'incomplete overlay record')
    records = {}
    for name in sorted(modules | cone):
        base = str(LIB / name.replace('.', '/'))
        current = {suffix: record(base + suffix) for suffix in SUFFIXES}
        entry = {'overlay': current, 'in_direct': name in modules, 'in_cone': name in cone}
        if name in modules:
            selected = scan['resolved'][name]
            stem = selected['path'][:-len('.olean')]
            need(record(selected['path']) == selected['record'], 'selected provider drift: ' + name)
            need({s: record(stem + s) for s in SUFFIXES} == selected['companions'],
                 'selected companion drift: ' + name)
            entry['selected_provider'] = selected
            entry['same_object_sha256'] = (current['.olean'] is not None and
                current['.olean']['sha256'] == selected['record']['sha256'])
        records[name] = entry
    for path, pin in PINS.items():
        need(digest(path) == pin, 'input changed during snapshot: ' + str(path))
    return records

def main():
    need(not sys.flags.optimize, 'optimized Python refused')
    need(sys.argv[1:] in (['capture'], ['check'], ['final']), 'usage: manifest.py capture|check|final')
    before = snapshot()
    after = snapshot()
    changed_during = sorted(n for n in before if before[n] != after[n])
    direct = {n: r for n, r in after.items() if r['in_direct']}
    cone = {n: r for n, r in after.items() if r['in_cone']}
    missing = sorted(n for n, r in direct.items() if r['overlay']['.olean'] is None)
    mismatch = sorted(n for n, r in direct.items() if r['overlay']['.olean'] is not None and not r['same_object_sha256'])
    absent_cone = sorted(n for n, r in cone.items() if r['overlay']['.olean'] is None)
    report = {'direct_matched': len(direct) - len(missing) - len(mismatch),
              'direct_missing': missing, 'direct_mismatched': mismatch,
              'cone_missing': absent_cone, 'changed_during_comparison': changed_during}
    if sys.argv[1] in ('capture', 'final'):
        output = OUTPUT if sys.argv[1] == 'capture' else FINAL
        need(not output.exists(), 'refusing to overwrite capture')
        previous = json.loads(OVERLAY_RESULT.read_text())
        if sys.argv[1] == 'capture':
            need(missing == previous['missing'] and mismatch == previous['mismatched'], 'overlay classification changed')
            need(all(r['overlay']['.olean'] == previous['records'][n]['overlay'] for n, r in direct.items()),
                 'overlay records changed')
        else:
            need(not changed_during, 'paths changed during final comparison')
            need(not mismatch, 'different overlapping selected direct objects')
            need(not absent_cone, 'cone objects not all present')
        output.parent.mkdir(parents=True, exist_ok=False)
        output.write_text(json.dumps({'time_ns': time.time_ns(), 'input_pins': {str(k): v for k, v in PINS.items()},
            'overlay_root': str(LIB), 'report': report, 'records_before': {n: before[n] for n in changed_during},
            'records': after,
            'scope': 'selected object and companion paths only; no package, dynamic, or source-to-object audit'},
            sort_keys=True, indent=2) + '\n')
    else:
        captured = json.loads(OUTPUT.read_text())
        changed = sorted(n for n, row in after.items() if row != captured['records'].get(n))
        report['changed_since_manifest'] = changed
        print(json.dumps(report, sort_keys=True))
        need(not changed_during, 'selected direct or cone paths changed during comparison')
        need(not changed, 'selected direct or cone paths changed since manifest; recapture and re-audit')
        need(not mismatch, 'different overlapping selected direct objects')
        need(not absent_cone, 'cone objects not all present')
        return
    print(json.dumps(report, sort_keys=True))

if __name__ == '__main__':
    main()
