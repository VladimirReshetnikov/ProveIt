#!/usr/bin/env python3
"""Independent final build/environment/archive checks. Scientific inputs stay inert."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import stat
import struct
import subprocess
import sys
import zlib

BASE = Path(__file__).absolute().parent / 'final-run'
spec = importlib.util.spec_from_file_location('review_tests', str(BASE.parent / 'supplemental_tests.py'))
T = importlib.util.module_from_spec(spec)
old = list(sys.argv); sys.argv = [sys.argv[0], str(BASE)]
spec.loader.exec_module(T)
sys.argv = old
ROOT = BASE / 'reviewed-release'
RESULTS = T.RESULTS

def write_json(path, data):
    path.write_text(json.dumps(data, sort_keys=True, indent=2) + '\n')

def encoded(data):
    return (json.dumps(data, sort_keys=True, indent=2) + '\n').encode()

def assert_pngs(output, expected_count):
    info = json.loads((output / 'PAGE_INVENTORY.json').read_text())
    files = sorted((output / 'pages').iterdir())
    T.require(len(files) == expected_count and {p.name for p in files} == set(info), 'independent PNG inventory count')
    for p in files:
        raw = p.read_bytes()
        T.require(raw.startswith(b'\x89PNG\r\n\x1a\n'), 'independent PNG signature')
        offset = 8; chunks = []; compressed = b''
        while offset < len(raw):
            length = int.from_bytes(raw[offset:offset+4], 'big')
            kind = raw[offset+4:offset+8]
            data = raw[offset+8:offset+8+length]
            crc = int.from_bytes(raw[offset+8+length:offset+12+length], 'big')
            T.require(crc == zlib.crc32(kind + data) & 0xffffffff, 'independent PNG CRC')
            if kind == b'IHDR':
                width, height, depth, color, compression, filtering, interlace = struct.unpack('>IIBBBBB', data)
                T.require((depth,color,compression,filtering,interlace)==(8,2,0,0,0), 'independent PNG format')
            if kind == b'IDAT': compressed += data
            offset += length + 12; chunks.append(kind)
        pixels = zlib.decompress(compressed)
        T.require(chunks[0] == b'IHDR' and chunks[-1] == b'IEND' and offset == len(raw), 'independent PNG chunk boundaries')
        T.require(len(pixels) == height * (width * 3 + 1), 'independent PNG raster length')
        T.require(all(pixels[i * (width * 3 + 1)] in range(5) for i in range(height)), 'independent PNG filters')
        T.require(info[p.name] == {'width':width, 'height':height, 'bytes':len(raw), 'sha256':hashlib.sha256(raw).hexdigest()}, 'independent PNG inventory values')
    T.record('independent-all-' + str(expected_count) + '-page-png-check-' + output.name, True)

def main():
    source_pins = {p.name:T.pin(p) for p in (ROOT / 'tools').iterdir() if p.is_file()}
    root = T.clone('hostile spaces ü')
    traps = BASE / 'hostile-environment-traps'; traps.mkdir()
    marker = BASE / 'UNEXPECTED_ENVIRONMENT_EXECUTION'
    for name in ('json', 'hashlib', 'subprocess', 'sitecustomize', 'usercustomize'):
        (traps / (name + '.py')).write_text('open(' + repr(str(marker)) + ', "w").write("python trap")\nraise RuntimeError("python trap executed")\n')
    for name in ('pdftex', 'pdflatex', 'kpsewhich', 'pdftotext', 'pdftoppm', 'pdfinfo'):
        p = traps / name
        p.write_text('#!/bin/sh\nprintf trap > ' + str(marker) + '\nexit 91\n'); p.chmod(0o755)
    (traps / 'article.cls').write_text('\\errmessage{HOSTILE ARTICLE CLASS LOADED}\n')
    (traps / 'texmf.cnf').write_text('shell_escape = t\nopenin_any = a\nopenout_any = a\n')
    env = os.environ.copy()
    env.update({'PATH':str(traps), 'HOME':str(traps), 'PYTHONPATH':str(traps), 'PYTHONHOME':str(traps), 'PYTHONPYCACHEPREFIX':str(traps / 'pycache'), 'TEXINPUTS':str(traps), 'TEXMF':str(traps), 'TEXMFCNF':str(traps), 'TEXFORMATS':str(traps), 'TEXFONTMAPS':str(traps), 'TEXMFHOME':str(traps), 'TEXMFVAR':str(traps), 'TEXMFCONFIG':str(traps), 'SOURCE_DATE_EPOCH':'0', 'TZ':'Pacific/Honolulu', 'shell_escape':'t', 'openin_any':'a', 'openout_any':'a', 'MKTEXPK':'1', 'MKTEXTFM':'1', 'MKTEXMF':'1', 'TMPDIR':str(root / 'science/frozen-proof'), 'TEMP':str(root / 'audits/scientific'), 'TMP':str(root / 'dependencies/proofs')})
    pin = T.pin(root / 'manuscript/MANUSCRIPT_PINS.json')
    lockpin = T.pin(root / 'tools/BUILD_DEPENDENCIES_LOCK.json')
    common = ['build_report62.py', '--pins-sha', pin, '--dependency-lock-sha', lockpin, '--require-packaged-match', '--render-dpi', '72']
    output = BASE / 'hostile actual build ü'
    T.command('hostile-environment-actual-report', [*common, '--output-dir', str(output)], root=root, output=output, expected_success=True, env=env)
    T.record('hostile-env-no-python-or-command-trap', not marker.exists() and not (traps / 'pycache').exists())
    receipt = json.loads((output / 'BUILD_RECEIPT.json').read_text())
    T.record('actual-report-22-pages-locked-equality', receipt['status'] == 'PASS' and receipt['page_count'] == 22 and receipt['packaged_pdf_match'] and receipt['dependency_lock_verified'] and T.pin(output / 'Report62.pdf') == T.pin(ROOT / 'Report62.pdf'))
    T.record('preflight-postbuild-lock-byte-equality', (output / 'BUILD_DEPENDENCIES.json').read_bytes() == (ROOT / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())
    union = json.loads((output / 'RECORDER_INPUT_UNION.json').read_text())
    T.record('format-and-three-pass-recorders-retained', [p['pass'] for p in union['passes']] == ['format','compile-1','compile-2','compile-3'] and all(T.pin(output / (p['pass'] + '.fls')) == p['fls_sha256'] for p in union['passes']))
    recorded = set().union(*(set(p['system_inputs']) for p in union['passes']))
    maps = {str(Path((output / ('map-' + name + '.stdout')).read_text().strip()).resolve()) for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map')}
    T.record('independent-recorder-plus-map-union-exact', set(union['union']) == recorded | maps)
    assert_pngs(output, 22)

    for label, mutate in [
        ('extra-top-level-field', lambda d:d.update(extra=True)),
        ('wrong-executable-hash', lambda d:d['executables']['pdftex'].update(sha256='0'*64)),
        ('wrong-system-size', lambda d:next(iter(d['system_inputs'].values())).update(bytes=-1)),
        ('outside-system-root', lambda d:d['system_inputs'].update({'/etc/passwd':{'bytes':0,'sha256':'0'*64}})),
        ('invalid-system-inventory-type', lambda d:d.update(system_inputs=[]))]:
        target = T.clone('lock-' + label)
        lockpath = target / 'tools/BUILD_DEPENDENCIES_LOCK.json'
        lock = json.loads(lockpath.read_text()); mutate(lock); lockpath.write_bytes(encoded(lock))
        dest = BASE / ('lock-rejected-' + label)
        T.command('lock-preflight-' + label, ['build_report62.py', '--pins-sha', pin, '--dependency-lock-sha', T.pin(lockpath), '--output-dir', str(dest)], root=target, output=dest)
    target = T.clone('unused-lock-dependency')
    lockpath = target / 'tools/BUILD_DEPENDENCIES_LOCK.json'; lock = json.loads(lockpath.read_text())
    extra = Path('/usr/share/texlive/texmf-dist/tex/latex/base/alltt.sty')
    T.require(str(extra) not in lock['system_inputs'], 'selected unused dependency actually used')
    lock['system_inputs'][str(extra)] = {'bytes':extra.stat().st_size, 'sha256':T.pin(extra)}; lockpath.write_bytes(encoded(lock))
    dest = BASE / 'unused-lock-dependency-build'
    T.command('reject-unused-pinned-system-input-at-union-equality', ['build_report62.py', '--pins-sha', pin, '--dependency-lock-sha', T.pin(lockpath), '--output-dir', str(dest)], root=target)
    T.record('failed-union-has-no-pass-receipt', not (dest / 'BUILD_RECEIPT.json').exists() and json.loads((dest / 'BUILD_FAILURE.json').read_text())['release_preserved'])

    standalone = T.clone('standalone-mismatch'); p = standalone / 'Report62.tex'; p.write_bytes(p.read_bytes() + b'\n')
    dest = BASE / 'standalone-rejected-output'
    T.command('standalone-modular-inequality-rejected', [*common, '--output-dir', str(dest)], root=standalone, output=dest)
    manuscript = T.clone('modular-mismatch'); p = manuscript / 'manuscript/clocks.tex'; p.write_bytes(p.read_bytes() + b'\n')
    dest = BASE / 'modular-rejected-output'
    T.command('modular-pin-inequality-rejected', [*common, '--output-dir', str(dest)], root=manuscript, output=dest)
    for mode in ['-O','-OO']:
        dest = BASE / ('optimized-' + mode[1:])
        before = T.snapshot(ROOT)
        result = subprocess.run([sys.executable,'-I','-S','-B',mode,str(ROOT/'tools/build_report62.py'),'--pins-sha',pin,'--dependency-lock-sha',lockpin,'--output-dir',str(dest)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        T.record('optimized-interpreter-rejected-' + mode, result.returncode != 0 and not dest.exists() and before == T.snapshot(ROOT))

    manifest = BASE / 'actual-manifest.json'
    T.command('actual-report-manifest', ['release62.py','manifest','--output',str(manifest)], root=root, expected_success=True)
    shutil.copy2(manifest, root/'RELEASE_MANIFEST.json'); manifestpin=T.pin(manifest)
    T.command('actual-sealed-report-verification', ['release62.py','verify','--manifest-sha256',manifestpin], root=root, expected_success=True)
    for suffix in ('a','b'):
        T.command('actual-deterministic-archive-' + suffix, ['release62.py','archive','--manifest-sha256',manifestpin,'--output',str(BASE/('actual-'+suffix+'.zip'))],root=root,expected_success=True)
    T.record('actual-archives-byte-identical', (BASE/'actual-a.zip').read_bytes()==(BASE/'actual-b.zip').read_bytes())
    relocated=BASE/'actual relocated ü'
    T.command('actual-metadata-roundtrip', ['release62.py','extract','--archive',str(BASE/'actual-a.zip'),'--manifest-sha256',manifestpin,'--output-dir',str(relocated)],root=root,expected_success=True)
    T.command('actual-relocated-manifest-verified', ['release62.py','verify','--manifest-sha256',manifestpin],root=relocated,expected_success=True)
    out2=BASE/'actual-relocated-build'
    T.command('actual-relocated-locked-pdf-equality', [*common,'--output-dir',str(out2)],root=relocated,expected_success=True)
    assert_pngs(out2,22)
    T.record('relocated-pdf-byte-identical', (output/'Report62.pdf').read_bytes()==(out2/'Report62.pdf').read_bytes())
    replay_source=Path('/workspace/shared/replay-projective-signal-shears62-20261004')
    def hashes(path):
        return {str(p.relative_to(path)):T.pin(p) for p in path.rglob('*') if p.is_file()}
    T.record('integrated-and-relocated-portable-replay-unchanged', hashes(replay_source)==hashes(relocated/'tools/portable-replay') and T.pin(relocated/'audits/scientific/independent_static_audit.py')=='a945491e115e5f96dfc11e3d6e714ef367ecc0daddfce425d8310cb5949f4fec')
    result={'status':'PASS','scope':'Independent final actual-report builds and package roundtrip; scientific sources and checker were inert', 'test_count':len(RESULTS),'tool_sources':source_pins,'manuscript_pins_sha256':pin,'dependency_lock_sha256':lockpin,'pdf_sha256':receipt['pdf_sha256'],'page_count':22,'tests':RESULTS}
    write_json(BASE/'BUILD_ROUNDTRIP_RESULTS.json',result)
    print(json.dumps({k:result[k] for k in ('status','test_count','pdf_sha256','page_count')}))

if __name__=='__main__':
    main()
