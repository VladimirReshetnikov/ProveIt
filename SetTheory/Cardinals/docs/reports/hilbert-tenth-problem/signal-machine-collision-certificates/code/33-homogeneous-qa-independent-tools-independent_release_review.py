#!/usr/bin/env python3
"""Independent release-only adversarial checks. Scientific sources are inert bytes.
Run with python3 -I -S -B. All mutations occur in this dossier's diagnostic copies.
"""
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import runpy
import shutil
import stat
import struct
import subprocess
import sys
import zlib
import zipfile

HERE = Path(__file__).absolute().parent
ROOT = Path('/workspace/shared/report63-homogeneous-realization-release-20261004')
BINDINGS = json.loads((HERE / 'SOURCE_BINDINGS.json').read_bytes())
EXPECTED = {name: BINDINGS['tools/' + name] for name in ('release63.py', 'build_report63.py', 'selftest63.py')}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def enc(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def ensure(value, message):
    if not value:
        raise AssertionError(message)


def main():
    ensure(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize, 'isolated interpreter required')
    for name, pin in EXPECTED.items():
        ensure(sha((ROOT / 'tools' / name).read_bytes()) == pin, 'reviewed source changed: ' + name)
    api = runpy.run_path(str(ROOT / 'tools/release63.py'), run_name='independent_review_helpers')
    build = runpy.run_path(str(ROOT / 'tools/build_report63.py'), run_name='independent_review_png')
    base = HERE / 'owned-selftest/fixture'
    out = HERE / 'independent-tests'
    out.mkdir(mode=0o700)
    fixture = out / 'fixture'
    shutil.copytree(base, fixture, copy_function=shutil.copy2)
    results = []
    before = {name: api['snapshot'](ROOT / name) for name in ('science', 'audits', 'dependencies')}

    def passed(name, **detail):
        results.append({'name': name, 'status': 'PASS', **detail})
        (out / 'TESTS_SO_FAR.json').write_bytes(enc(results))

    def rejects(name, function, *args):
        try:
            function(*args)
        except (ValueError, TypeError, KeyError, OSError, zlib.error):
            passed(name)
        else:
            raise AssertionError('accepted malformed input: ' + name)

    def clone(name):
        p = out / ('fixture-' + name)
        shutil.copytree(fixture, p, copy_function=shutil.copy2)
        return p

    def command(name, tool, args, root=fixture, success=False, absent=None, env=None, flags=('-I','-S','-B')):
        before_local = api['snapshot'](root, allow_empty=True)
        run = subprocess.run([sys.executable, *flags, str(root / 'tools' / tool), *args], cwd=out,
                             stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300, env=env)
        (out / (name + '.stdout')).write_bytes(run.stdout)
        ensure((run.returncode == 0) == success, 'unexpected exit: ' + name + '\n' + run.stdout.decode(errors='replace')[-3000:])
        ensure(before_local == api['snapshot'](root, allow_empty=True), 'mutated diagnostic source: ' + name)
        if absent is not None:
            ensure(not os.path.lexists(absent), 'created prohibited output: ' + name)
        passed(name, exit_status=run.returncode, diagnostic_source_preserved=True)
        return run

    for i, path in enumerate(('', '/abs', '../x', 'a/../b', 'a//b', 'a/./b', './x', 'x/', 'a\\b', 'a\x00b', 'a\nb')):
        rejects('relative-path-rejection-' + str(i), api['relative_name'], path)
    for i, value in enumerate(('', 'A'*64, 'f'*63, 'g'*64, 5, None)):
        rejects('sha-pin-rejection-' + str(i), api['digest'], value)
    rejects('duplicate-json-key', api['parse'], b'{"same":1,"same":2}')
    canonical_inputs = [str(out) + '/../escape', str(out) + '//child', str(out) + '/./child', str(out) + '/child/', '//workspace/shared/fake']
    for i, raw in enumerate(canonical_inputs):
        command('output-alias-' + str(i), 'release63.py', ['prepare','--output-dir',raw])
    (out / 'dangling-output').symlink_to(out / 'absent-destination')
    command('dangling-symlink-output','release63.py',['prepare','--output-dir',str(out / 'dangling-output')])
    os.mkfifo(out / 'fifo-output')
    command('fifo-existing-output','release63.py',['prepare','--output-dir',str(out / 'fifo-output')])
    for i, protected in enumerate(api['PROTECTED']):
        command('protected-source-output-' + str(i),'release63.py',['prepare','--output-dir',str(protected / 'audit-prohibited-child')], absent=protected / 'audit-prohibited-child')
    for suffix,mutate in [
        ('frozen-content', lambda p: (p/'science/frozen-proof/PROOF.md').write_bytes(b'changed')),
        ('frozen-directory-mode', lambda p: (p/'science/frozen-proof/evidence').chmod(0o700)),
        ('frozen-directory-mtime', lambda p: os.utime(p/'science/frozen-proof/evidence',ns=(1,1))),
        ('frozen-name', lambda p: (p/'science/frozen-proof/PROOF.md').rename(p/'science/frozen-proof/changed.md')),
        ('pin-map-content', lambda p: (p/'INPUT_PINS.json').write_bytes(b'{}\n')),
    ]:
        target=clone(suffix); mutate(target)
        command('reject-'+suffix,'release63.py',['check-inputs'],root=target)
    # Bypass command()'s inventory only for intentionally nonregular trees.
    for name,kind in [('symlink-directory','symlink'),('fifo-source','fifo')]:
        target=clone(name)
        if kind=='symlink': (target/'bad-entry').symlink_to(target/'science',target_is_directory=True)
        else: os.mkfifo(target/'bad-entry')
        r=subprocess.run([sys.executable,'-I','-S','-B',str(target/'tools/release63.py'),'check-inputs'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
        (out/(name+'.stdout')).write_bytes(r.stdout); ensure(r.returncode != 0,name); passed(name,exit_status=r.returncode)

    pin=sha((fixture/'manuscript/MANUSCRIPT_PINS.json').read_bytes())
    lockraw=(fixture/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()
    common=['--pins-sha',pin,'--dependency-lock-sha',sha(lockraw)]
    for label,changes in [('no-isolation',('-S','-B')),('no-no-site',('-I','-B')),('no-no-bytecode',('-I','-S')),('optimized',('-I','-S','-B','-O'))]:
        dest=out/('reject-flags-'+label)
        command(label,'build_report63.py',[*common,'--output-dir',str(dest)],absent=dest,flags=changes)
    for dpi in ('71','201','-1'):
        dest=out/('dpi-'+dpi)
        command('reject-dpi-'+dpi,'build_report63.py',[*common,'--render-dpi',dpi,'--output-dir',str(dest)],absent=dest)
    target=clone('helper-tamper'); (target/'tools/release63.py').write_bytes((target/'tools/release63.py').read_bytes()+b'\n# diagnostic tamper\n')
    dest=out/'helper-output'
    command('helper-source-pin','build_report63.py',[*common,'--output-dir',str(dest)],root=target,absent=dest)
    target=clone('standalone-tamper'); (target/'Report63.tex').write_bytes((target/'Report63.tex').read_bytes()+b'% changed\n')
    dest=out/'standalone-output'
    command('standalone-flatten-check','build_report63.py',[*common,'--output-dir',str(dest)],root=target,absent=dest)
    for name,mutate in [
      ('executable-pin',lambda lock: lock['executables']['pdftex'].__setitem__('sha256','0'*64)),
      ('system-size',lambda lock: next(iter(lock['system_inputs'].values())).__setitem__('bytes',0)),
      ('scope',lambda lock: lock.__setitem__('scope','changed')),
      ('format',lambda lock: lock.__setitem__('format','changed')),
      ('unexpected-key',lambda lock: lock.__setitem__('extra',True)),
    ]:
        target=clone(name); lock=json.loads(lockraw); mutate(lock); data=enc(lock); (target/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data); dest=out/(name+'-output')
        command('preflight-'+name,'build_report63.py',['--pins-sha',pin,'--dependency-lock-sha',sha(data),'--output-dir',str(dest)],root=target,absent=dest)
    # A valid but unexecuted pinned file must fail the exact post-run union check.
    target=clone('extra-system-input'); lock=json.loads(lockraw)
    extra=ROOT/'tools/BUILD_DEPENDENCIES_LOCK.json'
    candidates=json.loads(extra.read_bytes())['system_inputs']
    name=next(n for n in candidates if n not in lock['system_inputs'])
    lock['system_inputs'][name]=candidates[name]; data=enc(lock); (target/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data)
    dest=out/'extra-system-output'
    command('extra-system-post-union','build_report63.py',['--pins-sha',pin,'--dependency-lock-sha',sha(data),'--output-dir',str(dest)],root=target)
    ensure('All-pass executed TeX-input union differs from lock' in (out/'extra-system-post-union.stdout').read_text(),'expected post-union failure missing')
    ensure(not list(dest.glob('report63-typeset-*')),'failed temporary workspace left behind')
    passed('failure-temp-cleanup')

    # Independent PNG corpus validates exact chunk order, compression and scanlines.
    def chunk(k,b):return struct.pack('>I',len(b))+k+b+struct.pack('>I',zlib.crc32(k+b)&0xffffffff)
    sig=b'\x89PNG\r\n\x1a\n'; ih=chunk(b'IHDR',struct.pack('>IIBBBBB',1,1,8,2,0,0,0)); end=chunk(b'IEND',b'')
    def png(raw,tail=b''):return sig+ih+chunk(b'IDAT',zlib.compress(raw)+tail)+end
    valid=png(b'\x00\x11\x22\x33')
    ensure(build['validate_png'](valid,ensure)=={'width':1,'height':1},'valid png'); passed('valid-png')
    corpus={
      'no-ihdr':sig+chunk(b'IDAT',zlib.compress(b'\0'*4))+end,
      'duplicate-ihdr':sig+ih+ih+chunk(b'IDAT',zlib.compress(b'\0'*4))+end,
      'no-iend':valid[:-12], 'no-idat':sig+ih+end,'nonzero-iend':valid[:-12]+chunk(b'IEND',b'x'),
      'extra-after-iend':valid+b'x','unknown-chunk':sig+ih+chunk(b'tEXt',b'a')+valid[len(sig+ih):],
      'zero-width':sig+chunk(b'IHDR',struct.pack('>IIBBBBB',0,1,8,2,0,0,0))+valid[len(sig+ih):],
      'huge-width':sig+chunk(b'IHDR',struct.pack('>IIBBBBB',10001,1,8,2,0,0,0))+valid[len(sig+ih):],
      'wrong-color':sig+chunk(b'IHDR',struct.pack('>IIBBBBB',1,1,8,6,0,0,0))+valid[len(sig+ih):],
      'wrong-depth':sig+chunk(b'IHDR',struct.pack('>IIBBBBB',1,1,16,2,0,0,0))+valid[len(sig+ih):],
      'bad-row-filter':png(b'\x05\0\0\0'),'short-raster':png(b'\0'*3),'long-raster':png(b'\0'*5),
      'zlib-trailing':png(b'\0'*4,b'extra'),'second-zlib-stream':png(b'\0'*4,zlib.compress(b'extra')),
      'truncated-zlib':sig+ih+chunk(b'IDAT',zlib.compress(b'\0'*4)[:-2])+end,
      'late-phys':valid[:-12]+chunk(b'pHYs',struct.pack('>IIB',1,1,1))+end,
      'zero-phys':sig+ih+chunk(b'pHYs',struct.pack('>IIB',0,1,1))+valid[len(sig+ih):],
    }
    for name,b in corpus.items():
        try: build['validate_png'](b,api['require'])
        except (ValueError,zlib.error):passed('png-'+name)
        else:raise AssertionError('bad PNG accepted: '+name)

    manifest={'format':api['FORMAT'],'files':{'a/data.txt':{'mode':0o640,'mtime_ns':1234567890123456789,'bytes':3,'sha256':sha(b'abc')}},'directories':{'a':{'mode':0o750,'mtime_ns':1234567890123456700}}}
    for name,mutate in [
      ('reserved-directory',lambda m:(m['files'].__setitem__(api['MANIFEST']+'/child',m['files'].pop('a/data.txt')),m['directories'].__setitem__(api['MANIFEST'],m['directories'].pop('a')))),
      ('self-manifest',lambda m:m['files'].__setitem__(api['MANIFEST'],m['files']['a/data.txt'])),
      ('file-dir-overlap',lambda m:m['directories'].__setitem__('a/data.txt',{'mode':0o755,'mtime_ns':1})),
      ('missing-parent',lambda m:m['directories'].clear()),
      ('empty-directory',lambda m:m['directories'].__setitem__('empty',{'mode':0o755,'mtime_ns':1})),
      ('setuid-mode',lambda m:m['files']['a/data.txt'].__setitem__('mode',0o4640)),
      ('bool-mode',lambda m:m['files']['a/data.txt'].__setitem__('mode',True)),
      ('negative-time',lambda m:m['files']['a/data.txt'].__setitem__('mtime_ns',-1)),
      ('bool-time',lambda m:m['files']['a/data.txt'].__setitem__('mtime_ns',True)),
      ('negative-size',lambda m:m['files']['a/data.txt'].__setitem__('bytes',-1)),
      ('extra-row-field',lambda m:m['files']['a/data.txt'].__setitem__('extra',0)),
      ('parent-is-file',lambda m:m['files'].__setitem__('a',{'mode':0o644,'mtime_ns':1,'bytes':0,'sha256':sha(b'')})),
    ]:
        m=copy.deepcopy(manifest); mutate(m); rejects('manifest-'+name,api['validate_manifest'],m)

    def mkzip(path, m=manifest, data=b'abc', transform=None, raw=None):
        raw=enc(m) if raw is None else raw
        entries=[('Report63/'+api['MANIFEST'],raw,stat.S_IFREG|0o644),('Report63/a/data.txt',data,stat.S_IFREG|0o640)]
        if transform: entries=transform(entries)
        with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED) as z:
            for n,b,mode in entries:
                info=zipfile.ZipInfo(n,date_time=(2026,10,4,0,0,0));info.create_system=3;info.external_attr=mode<<16;z.writestr(info,b)
        return sha(raw)
    good=out/'minimal-valid.zip'; mpin=mkzip(good); extracted=out/'minimal-extracted'
    command('minimal-exact-metadata-extract','release63.py',['extract','--archive',str(good),'--manifest-sha256',mpin,'--output-dir',str(extracted)],success=True)
    ensure(api['inventory'](extracted,exclude_manifest=True)=={k:manifest[k] for k in ('files','directories')},'exact metadata restoration');passed('minimal-mode-nanosecond-restoration')
    variants={
      'traversal-extra':lambda e:e+[('../escape',b'x',stat.S_IFREG|0o644)],
      'absolute-extra':lambda e:e+[('/escape',b'x',stat.S_IFREG|0o644)],
      'duplicate':lambda e:e+[e[-1]],
      'reverse-order':lambda e:list(reversed(e)),
      'extra-directory':lambda e:e+[('Report63/extra/',b'',stat.S_IFDIR|0o755)],
      'symlink-member':lambda e:[e[0],(e[1][0],e[1][1],stat.S_IFLNK|0o640)],
      'incorrect-mode':lambda e:[e[0],(e[1][0],e[1][1],stat.S_IFREG|0o600)],
      'missing-file':lambda e:e[:1],
      'file-bytes-tamper':lambda e:[e[0],(e[1][0],b'bad',e[1][2])],
      'backslash':lambda e:[e[0],(e[1][0].replace('/','\\'),e[1][1],e[1][2])],
    }
    for name,transform in variants.items():
        p=out/(name+'.zip'); mp=mkzip(p,transform=transform); dest=out/(name+'-extract')
        command('archive-'+name,'release63.py',['extract','--archive',str(p),'--manifest-sha256',mp,'--output-dir',str(dest)],absent=dest)
    for name,raw in [('duplicate-json',b'{"format":"Report63 release manifest v1","format":"x","files":{},"directories":{}}'),('malformed-json',b'{')]:
        p=out/(name+'.zip'); mp=mkzip(p,raw=raw); dest=out/(name+'-extract')
        command('archive-'+name,'release63.py',['extract','--archive',str(p),'--manifest-sha256',mp,'--output-dir',str(dest)],absent=dest)
    reserved=copy.deepcopy(manifest);reserved['files']={api['MANIFEST']+'/child':manifest['files']['a/data.txt']};reserved['directories']={api['MANIFEST']:manifest['directories']['a']}
    p=out/'reserved.zip';mp=mkzip(p,m=reserved);dest=out/'reserved-extract'
    command('archive-reserved-manifest-directory','release63.py',['extract','--archive',str(p),'--manifest-sha256',mp,'--output-dir',str(dest)],absent=dest)
    # Exact ZIP CRC check uses an uncompressed diagnostic member with one flipped byte.
    corrupt=bytearray(good.read_bytes());loc=corrupt.find(b'abc');ensure(loc>=0,'stored diagnostic member missing');corrupt[loc]^=1
    p=out/'bad-crc.zip';p.write_bytes(corrupt);dest=out/'bad-crc-extract'
    command('archive-crc','release63.py',['extract','--archive',str(p),'--manifest-sha256',mpin,'--output-dir',str(dest)],absent=dest)
    after={name:api['snapshot'](ROOT/name) for name in ('science','audits','dependencies')}
    ensure(before==after,'real frozen release changed');passed('real-frozen-source-preservation')
    result={'status':'PASS','scope':'Independent release-only adversarial checks on diagnostic copies; no mathematical source program executed','source_bindings':EXPECTED,'test_count':len(results),'tests':results,'real_frozen_inputs_preserved':True}
    (HERE/'INDEPENDENT_TEST_RECEIPT.json').write_bytes(enc(result));print(enc(result).decode())


if __name__=='__main__':
    main()
