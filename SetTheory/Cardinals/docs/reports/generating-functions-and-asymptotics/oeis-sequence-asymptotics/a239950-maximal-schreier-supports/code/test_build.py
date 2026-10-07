#!/usr/bin/env python3
"""Tailored Report195 safety tests; --integration adds real deterministic builds.

Default guards are fast and do not run TeX or regenerate the 1500-term table.
No test relies on assert, so -O executes all checks. Integration tests build in
normal/-O modes, extract a validated archive, and replay/rebuild that extraction.
"""
from __future__ import annotations
import argparse
import ast
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
from unittest import mock
import zipfile

sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
sys.path.insert(0,str(ROOT/'code'))
import build
import verify_manifest as manifest
import reproduce
import partition_exact
import check_exact


class Checks:
    def __init__(self):
        self.accepted=[]
        self.rejected=[]

    def good(self,label,condition):
        if not condition:
            raise ValueError('guard failed: '+label)
        self.accepted.append(label)

    def bad(self,label,call):
        try:
            call()
        except (ValueError,OSError,TypeError,subprocess.TimeoutExpired):
            self.rejected.append(label)
            return
        raise ValueError('expected rejection: '+label)


def run_guards():
    c=Checks()
    for name in manifest.SOURCES:
        if name.endswith('.py'):
            tree=ast.parse(manifest.read_regular(ROOT/name))
            c.good('no optimization-disabled assertions: '+name,
                   not any(isinstance(node,ast.Assert) for node in ast.walk(tree)))
    for byte in tuple(range(9))+tuple(range(11,32)):
        c.bad('source C0 byte '+str(byte),lambda byte=byte:build.validate_text_payload('Report195.tex',b'text'+bytes([byte])))
    build.validate_text_payload('Report195.tex',b'valid\ttext\n')
    c.good('source permits tabs and newlines',True)
    c.bad('source invalid UTF-8',lambda:build.validate_text_payload('Report195.tex',b'\xff'))
    prefix=manifest.load_json(manifest.read_regular(ROOT/'data/oeis_prefix.json'))
    tiny=partition_exact.counts(57)
    check_exact.check_prefix(tiny,prefix)
    c.good('positive DP agrees with all 58 observed terms',True)
    for n in range(19):
        brute=sum(bool(p) and p[0]==len(set(p)) for p in partition_exact.partitions(n))
        c.good('independent model through '+str(n),brute==tiny[n])
    for value in (-1,1501,True,1.5,'35',None):
        c.bad('invalid DP bound '+repr(value),lambda value=value:partition_exact.counts(value))
    wrong=dict(prefix);wrong['terms']=prefix['terms'][:-1]
    c.bad('truncated observed prefix',lambda:check_exact.check_prefix(tiny,wrong))
    wrong=dict(prefix);wrong['terms']=prefix['terms'].copy();wrong['terms'][5]+=1
    c.bad('changed observed prefix',lambda:check_exact.check_prefix(tiny,wrong))
    c.bad('short zero certificate input',lambda:check_exact.zero_certificate(tiny))
    c.good('rational first correction sign',check_exact.sign_certificate()['Q_at_larger_bound']=='48373/2000000')
    with tempfile.TemporaryDirectory(prefix='report195-guards-') as temporary:
        root=Path(temporary)
        source=root/'source';source.mkdir()
        (source/'data').mkdir();(source/'data/value').write_bytes(b'12345')
        c.good('bounded regular read',manifest.read_regular(source/'data/value',5)==b'12345')
        c.bad('oversized regular read',lambda:manifest.read_regular(source/'data/value',4))
        for name in ('','.', '..','../x','/absolute','a/../b','./x','a//b','a/./b','a\\b','C:/x','x\ny','x\x00y','x.pyc','__pycache__/x'):
            c.bad('unsafe relative inventory path '+repr(name),lambda name=name:manifest.safe_name(name))
        (root/'linked').symlink_to(source,target_is_directory=True)
        (source/'linked-file').symlink_to(source/'data/value')
        c.bad('symlink source root',lambda:manifest.scan(root/'linked'))
        c.bad('symlink file read',lambda:manifest.read_regular(source/'linked-file'))
        c.bad('symlink file scan',lambda:manifest.scan(source))
        (source/'linked-file').unlink()
        (source/'dangling').symlink_to(root/'absent')
        c.bad('dangling source link',lambda:manifest.scan(source))
        (source/'dangling').unlink()
        if hasattr(os,'mkfifo'):
            os.mkfifo(source/'pipe')
            c.bad('FIFO read',lambda:manifest.read_regular(source/'pipe'))
            c.bad('FIFO scan',lambda:manifest.scan(source))
            (source/'pipe').unlink()
        valid=root/'fresh'
        c.good('fresh absolute outside output',manifest.fresh_output(valid,source)==valid)
        (root/'occupied').mkdir();(root/'occupied/sentinel').write_bytes(b'keep')
        (root/'file').write_bytes(b'keep')
        (root/'dangling').symlink_to(root/'absent')
        for label,path in [('relative',Path('relative')),('traversal',source/'..'/'escape'),
                           ('within package',source/'new'),('existing directory',root/'occupied'),
                           ('existing file',root/'file'),('existing dangling link',root/'dangling'),
                           ('linked parent',root/'linked'/'out'),('missing parent',root/'absent'/'out')]:
            c.bad('unsafe output '+label,lambda path=path:manifest.fresh_output(path,source))
        c.good('existing output preserved',(root/'occupied/sentinel').read_bytes()==b'keep')
        c.bad('exclusive write does not overwrite',lambda:build.write_new(root/'file',b'changed'))
        c.good('existing file preserved',(root/'file').read_bytes()==b'keep')
        (source/'empty').mkdir()
        c.bad('empty unexpected directory',lambda:manifest.inventory(source))
        (source/'empty').rmdir()
        for cache in ('__pycache__','.pytest_cache','.cache'):
            (source/cache).mkdir()
            c.bad('cache directory '+cache,lambda:manifest.scan(source))
            (source/cache).rmdir()
        for raw in ('{"x":1,"x":2}','{"outer":{"x":1,"x":2}}','{"x":NaN}','{"x":Infinity}','{"x":1.2}'):
            c.bad('invalid JSON '+raw,lambda raw=raw:manifest.load_json(raw))
        c.bad('nonfinite canonical JSON',lambda:build.canonical({'x':float('nan')}))
        # A complete synthetic release tests the *closed* inventory and manifest.
        release=root/'release';release.mkdir()
        for name in manifest.RELEASE_FILES:
            target=release/name;target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(('fixture: '+name+'\n').encode())
        def rehash():
            (release/manifest.MANIFEST).write_bytes(build.canonical(manifest.document(release)))
        rehash()
        c.good('closed valid release',manifest.verify(release)['files_checked']==len(manifest.RELEASE_FILES))
        original=(release/'Report195.pdf').read_bytes()
        (release/'Report195.pdf').write_bytes(b'changed')
        c.bad('modified release payload',lambda:manifest.verify(release))
        (release/'Report195.pdf').write_bytes(original)
        (release/'unlisted.txt').write_bytes(b'extra');rehash()
        c.bad('rehashed extra still rejected',lambda:manifest.verify(release))
        (release/'unlisted.txt').unlink();rehash()
        (release/'Report195.pdf').unlink()
        c.bad('missing release payload',lambda:manifest.verify(release))
        (release/'Report195.pdf').write_bytes(original);rehash()
        reference=(release/manifest.MANIFEST).read_bytes()
        for label,mutate in [('boolean report',lambda d:d.update(report=True)),
                             ('wrong schema',lambda d:d.update(schema='other')),
                             ('wrong algorithm',lambda d:d.update(algorithm='md5')),
                             ('extra top field',lambda d:d.update(extra=True)),
                             ('boolean bytes',lambda d:d['files']['Report195.pdf'].update(bytes=True)),
                             ('wrong digest',lambda d:d['files']['Report195.pdf'].update(sha256='0'*64)),
                             ('extra row field',lambda d:d['files']['Report195.pdf'].update(extra=True))]:
            data=manifest.load_json(reference);mutate(data)
            (release/manifest.MANIFEST).write_bytes(build.canonical(data))
            c.bad('manifest '+label,lambda:manifest.verify(release))
        (release/manifest.MANIFEST).write_bytes(reference)
        with mock.patch.object(manifest,'MAX_TOTAL_BYTES',1):
            c.bad('aggregate byte limit',lambda:manifest.verify(release))
        for name in manifest.OPTIONAL:
            (release/name).write_bytes(b'exact symbolic fixture\n')
            rehash()
            if name==manifest.OPTIONAL[0]:
                c.bad('partial optional transcript inventory',lambda:manifest.verify(release))
        c.good('complete optional transcript inventory',
               manifest.verify(release)['files_checked']==len(manifest.RELEASE_FILES+manifest.OPTIONAL))
        for name in manifest.OPTIONAL:
            (release/name).unlink()
        rehash()
        zips=[root/'first.zip',root/'second.zip']
        for output in zips:
            build.archive(release,output)
        c.good('deterministic archive bytes',zips[0].read_bytes()==zips[1].read_bytes())
        with zipfile.ZipFile(zips[0]) as zipped:
            c.good('archive closed sorted inventory',zipped.namelist()==sorted((*manifest.RELEASE_FILES,manifest.MANIFEST)))
            c.good('archive fixed metadata',all(i.date_time==build.ZIP_TIME and i.compress_type==zipfile.ZIP_STORED
                and i.external_attr>>16==stat.S_IFREG|0o644 for i in zipped.infolist()))
        c.bad('archive refuses replacement',lambda:build.archive(release,zips[0]))
        c.bad('archive refuses package output',lambda:build.archive(release,release/'new.zip'))
        # Exercise the two-pass compiler contract without launching TeX here.
        tex=root/'tex';tex.mkdir()
        calls=[]
        def compiler(command,cwd,env,timeout=900):
            calls.append(command)
            for extension in ('aux','toc','out'):
                (tex/('Report195.'+extension)).write_bytes(b'stable')
            (tex/'Report195.log').write_text('Clean TeX run\n')
            (tex/'Report195.pdf').write_bytes(b'%PDF-1.5\nfixture')
            return ''
        with mock.patch.object(build,'run',side_effect=compiler):
            c.good('two-pass compiler accepts stable clean PDF',build.compile_pdf(tex,{})==b'%PDF-1.5\nfixture')
        c.good('exactly two TeX invocations',len(calls)==2)
        c.good('TeX shell escape disabled',all('-no-shell-escape' in command for command in calls))
        for label,message in [('undefined reference','There were undefined references'),
                              ('undefined citation','There were undefined citations'),
                              ('rerun needed','Rerun to get cross-references right'),
                              ('duplicate label','There were multiply-defined labels'),
                              ('overfull box','Overfull \\hbox (1.0pt too wide)'),
                              ('missing character','Missing character: There is no x'),
                              ('package warning','Package sample Warning: test')]:
            def bad_log(command,cwd,env,timeout=900,message=message):
                compiler(command,cwd,env,timeout)
                (tex/'Report195.log').write_text(message+'\n')
                return ''
            with mock.patch.object(build,'run',side_effect=bad_log):
                c.bad('TeX rejects '+label,lambda:build.compile_pdf(tex,{}))
        def unstable(command,cwd,env,timeout=900):
            compiler(command,cwd,env,timeout)
            (tex/'Report195.aux').write_text(str(len(calls)))
            return ''
        with mock.patch.object(build,'run',side_effect=unstable):
            c.bad('TeX unstable auxiliaries',lambda:build.compile_pdf(tex,{}))
        def invalid_pdf(command,cwd,env,timeout=900):
            compiler(command,cwd,env,timeout)
            (tex/'Report195.pdf').write_bytes(b'not a PDF')
            return ''
        with mock.patch.object(build,'run',side_effect=invalid_pdf):
            c.bad('TeX invalid PDF signature',lambda:build.compile_pdf(tex,{}))
        # Source acceptance permits sources or a verified extracted release only.
        source_fixture=root/'source-fixture';source_fixture.mkdir()
        for name in manifest.SOURCES:
            target=source_fixture/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b'fixture')
        build.validate_source(source_fixture)
        c.good('closed source tree accepted',True)
        build.validate_source(release)
        c.good('verified extracted release accepted',True)
        (source_fixture/'unlisted').write_bytes(b'extra')
        c.bad('source extra file',lambda:build.validate_source(source_fixture))
        (source_fixture/'unlisted').unlink()
        (source_fixture/'generated').mkdir()
        c.bad('source empty generated directory',lambda:build.validate_source(source_fixture))
    return {'status':'PASS','accepted':c.accepted,'rejected':c.rejected,
            'accepted_count':len(c.accepted),'rejected_count':len(c.rejected),
            'scope':'Report195 safety guards and small independent exact checks; real builds require --integration'}


def integration(symbolic=False):
    before=reproduce.snapshot(ROOT)
    with tempfile.TemporaryDirectory(prefix='report195-integration-') as temporary:
        root=Path(temporary)
        env={'PATH':os.environ.get('PATH',os.defpath),'LC_ALL':'C.UTF-8','TZ':'UTC',
             'PYTHONHASHSEED':'0','PYTHONDONTWRITEBYTECODE':'1'}
        outputs=[]
        def invoke(source,destination,optimized=False):
            flags=['-I','-S','-B']+(['-O'] if optimized else [])
            command=[sys.executable,*flags,str(source/'build.py'),'--output',str(destination)]
            if symbolic:
                command.append('--symbolic')
            raw=build.run(command,source,env)
            result=manifest.load_json(raw)
            manifest.need(result['status']=='PASS','integration build failed')
            return {name:manifest.read_regular(destination/name,manifest.MAX_TOTAL_BYTES+65536)
                    for name in ('Report195.tex','Report195.pdf','Report195_code.zip','ARTIFACTS.json')}
        for mode,optimized in [('normal',False),('optimized',True)]:
            outputs.append(invoke(ROOT,root/mode,optimized))
        manifest.need(outputs[0]==outputs[1],'normal/-O real build artifacts differ')
        extracted=root/'extracted';extracted.mkdir()
        with zipfile.ZipFile(root/'normal/Report195_code.zip') as zipped:
            names=zipped.namelist()
            expected=(*manifest.RELEASE_FILES,*manifest.OPTIONAL,manifest.MANIFEST) if symbolic else (*manifest.RELEASE_FILES,manifest.MANIFEST)
            manifest.need(len(names)==len(set(names)) and set(names)==set(expected),
                          'integration extraction inventory mismatch')
            for info in zipped.infolist():
                manifest.safe_name(info.filename)
                manifest.need(info.external_attr>>16==stat.S_IFREG|0o644,'nonregular ZIP entry')
                target=extracted/info.filename;target.parent.mkdir(parents=True,exist_ok=True)
                build.write_new(target,zipped.read(info))
        manifest.verify(extracted)
        replay=reproduce.run(extracted,root/'extracted-replay',symbolic)
        manifest.need(replay['status']=='PASS','extracted replay failed')
        for name in ('exact_checks.json','exact_terms.txt'):
            manifest.need(manifest.read_regular(extracted/'generated'/name)==
                          manifest.read_regular(root/'extracted-replay/normal'/name),
                          'extracted regeneration differs: '+name)
        if symbolic:
            for name in manifest.OPTIONAL:
                manifest.need(manifest.read_regular(extracted/name)==
                              manifest.read_regular(root/'extracted-replay'/Path(name).name),
                              'extracted symbolic regeneration differs: '+name)
        rebuilt=invoke(extracted,root/'rebuilt')
        manifest.need(rebuilt==outputs[0],'extracted rebuild differs from original')
        manifest.need(reproduce.snapshot(ROOT)==before,'integration altered source')
        return {'status':'PASS','normal_and_optimized_builds_byte_identical':True,
                'extracted_package_replay_matches':True,'extracted_package_rebuild_byte_identical':True,
                'symbolic_requested':symbolic,
                'artifacts':{name:{'bytes':len(data),'sha256':build.sha(data)} for name,data in sorted(outputs[0].items())}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integration',action='store_true')
    parser.add_argument('--symbolic',action='store_true',help='include regenerated SymPy checks in --integration builds')
    args=parser.parse_args()
    try:
        manifest.need(not args.symbolic or args.integration,'--symbolic requires --integration')
        result=integration(args.symbolic) if args.integration else run_guards()
        sys.stdout.buffer.write(build.canonical(result))
    except (ValueError,OSError,TypeError,subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    sys.exit(main())
