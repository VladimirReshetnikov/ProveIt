#!/usr/bin/env python3
"""Fast explicit build-safety tests, also valid under python -O.

Compiler and pipeline tests use local deterministic fakes and never recursively
invoke a complete build. A subprocess independently checks initial imports.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
from unittest.mock import patch
import zipfile

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import build
from companion import ValidationError, json_bytes, require, write_new


def expect_error(kinds, function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except kinds as error:
        return error
    raise ValidationError('expected failure was not raised: '+function.__name__)


def forbidden(*args, **kwargs):
    raise RuntimeError('invalid destination reached external build work')


def fingerprint(path):
    path=Path(path)
    if path.is_symlink(): return ('symlink',os.readlink(path))
    if path.is_dir(): return ('directory',tuple(sorted(p.name for p in path.iterdir())))
    if path.is_file(): return ('file',path.read_bytes())
    return ('absent',)


def test_destinations(work, passed):
    regular=work/'existing.bin';regular.write_bytes(b'KEEP THIS FILE\n')
    symlink=work/'existing-link';symlink.symlink_to(regular)
    broken=work/'broken-link';broken.symlink_to(work/'absent-link-target')
    directory=work/'existing-directory';directory.mkdir()
    (directory/'keep.txt').write_bytes(b'KEEP THIS DIRECTORY\n')
    existing={'regular':regular,'symlink':symlink,'broken_symlink':broken,'directory':directory}
    tree=work/'archive-input';tree.mkdir();(tree/'entry.txt').write_text('entry\n')
    for label,target in existing.items():
        before=fingerprint(target)
        expect_error(OSError,write_new,target,b'REPLACEMENT')
        require(fingerprint(target)==before,'write_new changed '+label)
        passed.append('write_new_preserves_'+label)
        expect_error((OSError,ValidationError),build.make_zip_bytes_tree,tree,target)
        require(fingerprint(target)==before,'archive changed '+label)
        passed.append('archive_preserves_'+label)
        with patch.object(build,'prepare_tex',forbidden),patch.object(build,'run',forbidden):
            expect_error(ValidationError,build.build,target)
            alternate=work/('new-for-'+label+'.zip')
            expect_error(ValidationError,build.build,alternate,target)
        require(fingerprint(target)==before and not alternate.exists(),'occupied destination changed')
        passed.extend(['build_preserves_'+label,'pdf_preserves_'+label])
    require(regular.read_bytes()==b'KEEP THIS FILE\n','symlink target changed')
    require((directory/'keep.txt').read_bytes()==b'KEEP THIS DIRECTORY\n','directory content changed')
    require(not (work/'absent-link-target').exists(),'broken link target created')
    fresh=work/'new-file.bin';write_new(fresh,b'new data\n')
    require(fresh.read_bytes()==b'new data\n','exclusive write failed')
    passed.append('write_new_creates_new_file')
    aliasdir=work/'alias-component';aliasdir.mkdir()
    parentlink=work/'parent-alias';parentlink.symlink_to(aliasdir,target_is_directory=True)
    cases=[(work/'same.zip',work/'same.zip','identical'),
           (work/'same.zip',aliasdir/'..'/'same.zip','dotdot_alias'),
           (aliasdir/'same.zip',parentlink/'same.zip','symlink_parent_alias')]
    with patch.object(build,'prepare_tex',forbidden),patch.object(build,'run',forbidden):
        for zip_path,pdf_path,label in cases:
            expect_error(ValidationError,build.build,zip_path,pdf_path)
            require(not zip_path.exists() and not pdf_path.exists(),'duplicate output published')
            passed.append('duplicate_destinations_'+label+'_rejected')
        for target,label in [(work/'missing-parent'/'out.zip','missing_parent'),
                             (regular/'out.zip','nondirectory_parent'),
                             (work/'malicious\x00name.zip','nul_character')]:
            expect_error((ValidationError,ValueError,OSError),build.build,target)
            passed.append('invalid_zip_path_'+label+'_rejected')
            alternate=work/('valid-for-'+label+'.zip')
            expect_error((ValidationError,ValueError,OSError),build.build,alternate,target)
            require(not alternate.exists(),'invalid PDF destination published ZIP')
            passed.append('invalid_pdf_path_'+label+'_rejected')


def test_archive(work, passed):
    tree=work/'tree';tree.mkdir();(tree/'nested').mkdir()
    files={'z.txt':b'zeta\n','a.txt':b'alpha\n','nested/b.bin':bytes(range(256))}
    for name,data in files.items():(tree/name).write_bytes(data)
    expected={name:hashlib.sha256(data).hexdigest() for name,data in files.items()}
    require(build.manifest(tree)==expected,'manifest membership/hashes differ')
    require(list(build.manifest(tree))==sorted(files),'manifest unsorted')
    write_new(tree/'SHA256SUMS.json',json_bytes(expected))
    require(build.manifest(tree)==expected,'manifest includes itself')
    first,second=work/'one.zip',work/'two.zip'
    build.make_zip_bytes_tree(tree,first)
    for path in tree.rglob('*'):
        if path.is_file():os.chmod(path,0o600);os.utime(path,(946684800,946684800))
    build.make_zip_bytes_tree(tree,second)
    require(first.read_bytes()==second.read_bytes(),'ZIP depends on metadata')
    with zipfile.ZipFile(first) as archive:
        names=archive.namelist()
        require(names==sorted(names) and len(names)==len(set(names)),'ZIP order/uniqueness wrong')
        require(set(names)==set(files)|{'SHA256SUMS.json'},'unexpected membership')
        require(archive.testzip() is None,'ZIP CRC failure')
        for item in archive.infolist():
            require(item.date_time==build.ZIP_TIME and item.create_system==3,'ZIP timestamp/platform changed')
            require(item.external_attr>>16==0o100644,'ZIP permissions changed')
            require(item.compress_type==zipfile.ZIP_STORED and not item.extra and not item.comment,'ZIP metadata changed')
            require(not PurePosixPath(item.filename).is_absolute() and '..' not in PurePosixPath(item.filename).parts,'unsafe member')
        require(json.loads(archive.read('SHA256SUMS.json'))==expected,'stored manifest changed')
        for name,digest in expected.items():require(hashlib.sha256(archive.read(name)).hexdigest()==digest,'stored hash mismatch')
    require(datetime.datetime.fromtimestamp(build.SOURCE_DATE_EPOCH,datetime.timezone.utc).timetuple()[:6]==build.ZIP_TIME,'timestamp mismatch')
    passed.extend(['manifest_sha256_and_membership','manifest_sorted_and_excludes_self',
                   'zip_identical_despite_source_metadata','zip_sorted_unique_safe_members',
                   'zip_fixed_timestamp_platform_permissions','zip_stored_no_extra_metadata',
                   'archive_crc_and_manifest_hashes','consistent_source_date_epoch'])
    external=work/'outside.txt';external.write_bytes(b'DO NOT PACKAGE\n')
    for label,target,isdir in [('file',external,False),('broken',work/'absent',False),('directory',tree,True)]:
        unsafe=work/('unsafe-'+label);unsafe.mkdir()
        (unsafe/'link').symlink_to(target,target_is_directory=isdir)
        expect_error(ValidationError,build.manifest,unsafe)
        expect_error(ValidationError,build.make_zip_bytes_tree,unsafe,work/('unsafe-'+label+'.zip'))
        passed.extend(['manifest_rejects_'+label+'_symlink','archive_rejects_'+label+'_symlink'])


def test_source_layout(work, passed):
    names=build.SOURCE_FILES
    require(isinstance(names,(list,tuple)) and len(names)==len(set(names)),'source list not unique')
    for name in names:
        require(isinstance(name,str) and name,'invalid source name')
        p=PurePosixPath(name)
        require(not p.is_absolute() and '..' not in p.parts and '\\' not in name and '\x00' not in name and p.as_posix()==name,'unsafe source name')
    require({'Report172.tex','README.md','requirements.txt','build.py','code/companion.py','code/test_companion.py','code/test_build.py'}<=set(names),'missing reproducibility source')
    passed.extend(['source_paths_safe_and_unique','source_list_includes_reproducibility_files'])
    root=work/'missing-source-root';root.mkdir()
    zip_path,pdf_path=work/'missing-source.zip',work/'missing-source.pdf'
    with patch.object(build,'ROOT',root),patch.object(build,'SOURCE_FILES',['missing.tex']),patch.object(build.shutil,'which',return_value='/fake/compiler'),patch.object(build,'prepare_tex',forbidden),patch.object(build,'run',forbidden):
        expect_error(ValidationError,build.build,zip_path,pdf_path)
    require(not zip_path.exists() and not pdf_path.exists(),'missing source published')
    passed.append('missing_source_rejected_without_publication')
    target=work/'actual-source.tex';target.write_text('source\n');(root/'linked.tex').symlink_to(target)
    with patch.object(build,'ROOT',root),patch.object(build,'SOURCE_FILES',['linked.tex']),patch.object(build.shutil,'which',return_value='/fake/compiler'),patch.object(build,'prepare_tex',forbidden),patch.object(build,'run',forbidden):
        expect_error(ValidationError,build.build,zip_path,pdf_path)
    require(not zip_path.exists() and not pdf_path.exists(),'symlink source published')
    passed.append('symlink_source_rejected_without_publication')
    with patch.object(build.shutil,'which',return_value=None),patch.object(build,'prepare_tex',forbidden),patch.object(build,'run',forbidden):
        expect_error(ValidationError,build.build,zip_path,pdf_path)
    require(not zip_path.exists() and not pdf_path.exists(),'missing compiler published')
    passed.append('missing_compiler_rejected_without_publication')
    (root/'safe.txt').write_text('safe\n')
    outside=work/'outside-sources';outside.mkdir();(outside/'safe.txt').write_text('outside\n')
    (root/'linked-directory').symlink_to(outside,target_is_directory=True)
    malformed=[(['../escape'],'parent'),(['nested/../safe.txt'],'nested_parent'),
               (['/absolute'],'absolute'),(['.'],'dot'),([''],'empty'),
               (['nested\\safe.txt'],'backslash'),(['bad\x00name'],'nul'),
               (['nested//safe.txt'],'double_slash'),(['./safe.txt'],'dot_prefix'),
               (['safe.txt','safe.txt'],'duplicate'),([None],'nonstr'),
               (['linked-directory/safe.txt'],'symlink_parent')]
    for invalid,label in malformed:
        with patch.object(build,'ROOT',root),patch.object(build,'SOURCE_FILES',invalid),patch.object(build.shutil,'which',return_value='/fake/compiler'),patch.object(build,'prepare_tex',forbidden),patch.object(build,'run',forbidden):
            expect_error(ValidationError,build.build,zip_path,pdf_path)
        require(not zip_path.exists() and not pdf_path.exists(),'unsafe source published')
        passed.append('source_path_'+label+'_rejected')


def test_compiler(work, passed):
    source=work/'source.tex';source.write_text('test source\n')
    cases=[('aux_stable_two_passes','',None,'valid',2),
           ('aux_stable_three_passes','','aux','valid',3),
           ('toc_stable_three_passes','','toc','valid',3),
           ('out_stable_three_passes','','out','valid',3),
           ('overfull_hbox_rejected','Overfull \\hbox (3.0pt too wide)',None,'valid',None),
           ('overfull_vbox_rejected','Overfull \\vbox (3.0pt too high)',None,'valid',None),
           ('missing_glyph_rejected','Missing character: There is no X',None,'valid',None),
           ('undefined_references_rejected','There were undefined references',None,'valid',None),
           ('reference_rerun_rejected','Rerun to get cross-references right',None,'valid',None),
           ('undefined_citations_rejected','There were undefined citations',None,'valid',None),
           ('six_pass_limit_enforced','','forever','valid',None),
           ('invalid_pdf_rejected','',None,'invalid',None),
           ('empty_pdf_rejected','',None,'empty',None),
           ('missing_pdf_rejected','',None,'missing',None)]
    for label,defect,changing,pdf_kind,expected in cases:
        tex=work/label;tex.mkdir();calls=[]
        def fake_run(command,cwd,env,timeout=600):
            calls.append(list(command))
            require(Path(cwd)==tex and '-no-shell-escape' in command and '-halt-on-error' in command,'compiler flags/cwd wrong')
            for suffix in ['aux','toc','out']:
                data=str(len(calls)) if changing=='forever' else ('first' if changing==suffix and len(calls)==1 else 'stable')
                (tex/('Report172.'+suffix)).write_text(data)
            (tex/'Report172.log').write_text(defect)
            if pdf_kind!='missing':(tex/'Report172.pdf').write_bytes({'valid':b'%PDF-test','invalid':b'invalid','empty':b''}[pdf_kind])
            return ''
        with patch.object(build,'run',fake_run):
            if expected is None:expect_error(ValidationError,build.compile_pdf,source,tex,{})
            else:require(build.compile_pdf(source,tex,{})==expected,'wrong stabilization passes')
        require(2<=len(calls)<=6,'wrong compiler pass count')
        if changing=='forever':require(len(calls)==6,'six-pass limit not reached')
        require((tex/'Report172.tex').read_bytes()==source.read_bytes(),'source changed')
        passed.append(label)
    tex=work/'compiler-failure';tex.mkdir()
    with patch.object(build.subprocess,'run',return_value=subprocess.CompletedProcess(['fake'],7,stdout='deliberate compiler failure')):
        error=expect_error(ValidationError,build.compile_pdf,source,tex,{})
    require('deliberate compiler failure' in str(error),'compiler diagnostic lost')
    passed.append('nonzero_compiler_exit_rejected_with_diagnostic')
    tex=work/'compiler-timeout';tex.mkdir()
    with patch.object(build.subprocess,'run',side_effect=subprocess.TimeoutExpired('fake',180)):
        expect_error((subprocess.TimeoutExpired,ValidationError),build.compile_pdf,source,tex,{})
    passed.append('compiler_timeout_propagated')


def test_mocked_pipeline(work, passed):
    root=work/'pipeline-source';root.mkdir();source_names=list(build.SOURCE_FILES)
    for name in source_names:
        p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'mock source: '+name.encode()+b'\n')
    for mode in ['compiler_failure','success','zip_race','pdf_race']:
        zip_path,pdf_path=work/(mode+'.zip'),work/(mode+'.pdf');calls=[];temporary_roots=[]
        def fake_prepare(texwork,env):
            temporary_roots.append(Path(texwork).parent)
            require(env['SOURCE_DATE_EPOCH']==str(build.SOURCE_DATE_EPOCH),'missing fixed epoch')
            require(env['TZ']=='UTC' and env['PYTHONHASHSEED']=='0' and env['PYTHONDONTWRITEBYTECODE']=='1','unstable build environment')
            return 'mock TeX'
        def fake_run(command,cwd,env,timeout=600):
            calls.append(list(command))
            if '--output' in command:
                target=Path(cwd)/command[command.index('--output')+1]
                require(target.parent.is_dir(),'generated directory missing');write_new(target,b'{"mock":true}\n');return ''
            if '--version' in command:return 'mock tool version\n'
            raise ValidationError('unexpected command')
        def fake_compile(source,texwork,env):
            require(Path(source).read_bytes()==(root/'Report172.tex').read_bytes(),'staged source differs')
            if mode=='compiler_failure':raise ValidationError('deliberate mocked pipeline compiler failure')
            write_new(Path(texwork)/'Report172.pdf',b'%PDF-mock pipeline\n')
            if mode=='zip_race':write_new(zip_path,b'CONCURRENT ZIP\n')
            if mode=='pdf_race':write_new(pdf_path,b'CONCURRENT PDF\n')
            return 2
        with patch.object(build,'ROOT',root),patch.object(build.shutil,'which',return_value='/fake/compiler'),patch.object(build,'prepare_tex',fake_prepare),patch.object(build,'run',fake_run),patch.object(build,'compile_pdf',fake_compile):
            if mode=='compiler_failure':
                error=expect_error(ValidationError,build.build,zip_path,pdf_path)
                require('deliberate mocked pipeline' in str(error),'did not reach compiler failure')
                require(not zip_path.exists() and not pdf_path.exists(),'failed compile published')
            elif mode=='zip_race':
                expect_error(FileExistsError,build.build,zip_path)
                require(zip_path.read_bytes()==b'CONCURRENT ZIP\n','concurrent ZIP clobbered')
            elif mode=='pdf_race':
                expect_error(FileExistsError,build.build,zip_path,pdf_path)
                require(pdf_path.read_bytes()==b'CONCURRENT PDF\n' and not zip_path.exists(),'PDF race clobbered/published ZIP')
            else:
                result=build.build(zip_path,pdf_path)
                require(result['sha256']==hashlib.sha256(zip_path.read_bytes()).hexdigest() and result['bytes']==zip_path.stat().st_size,'result hash/size wrong')
                with zipfile.ZipFile(zip_path) as archive:
                    names=archive.namelist()
                    require(set(source_names)<=set(names) and {'Report172.pdf','BUILD-INFO.json','SHA256SUMS.json'}<=set(names),'package incomplete')
                    require(archive.read('Report172.pdf')==pdf_path.read_bytes(),'published PDFs differ')
                    hashes=json.loads(archive.read('SHA256SUMS.json'))
                    require(set(hashes)==set(names)-{'SHA256SUMS.json'},'manifest incomplete')
                    for name,digest in hashes.items():require(hashlib.sha256(archive.read(name)).hexdigest()==digest,'mocked hash mismatch')
        require(temporary_roots and all(not p.exists() for p in temporary_roots),'temporary tree not cleaned')
        tests=[command for command in calls if 'code/test_build.py' in command]
        require(len(tests)==2 and any('-O' in c for c in tests) and any('-O' not in c for c in tests),'normal/optimized tests missing')
        passed.append('mocked_pipeline_'+mode)


def test_initial_import_readonly(work, passed):
    source=work/'readonly-import-source';(source/'code').mkdir(parents=True)
    for name in ['build.py','code/companion.py']:(source/name).write_bytes((build.ROOT/name).read_bytes())
    target=work/'import-existing.zip';target.write_bytes(b'PRESERVE IMPORT TARGET\n')
    before={p.relative_to(source).as_posix():p.read_bytes() for p in source.rglob('*') if p.is_file()}
    env=dict(os.environ);env.pop('PYTHONDONTWRITEBYTECODE',None)
    result=subprocess.run([sys.executable,str(source/'build.py'),'--output',str(target)],capture_output=True,text=True,env=env,timeout=30)
    require(result.returncode!=0 and 'refusing existing destination' in result.stderr,'import test did not reach destination check')
    after={p.relative_to(source).as_posix():p.read_bytes() for p in source.rglob('*') if p.is_file()}
    require(before==after and not list(source.rglob('__pycache__')),'initial import modified source tree')
    require(target.read_bytes()==b'PRESERVE IMPORT TARGET\n','initial import clobbered target')
    passed.append('initial_import_creates_no_source_bytecode')


def run_tests():
    passed=[]
    with tempfile.TemporaryDirectory(prefix='report172-build-test-') as temporary:
        work=Path(temporary)
        test_destinations(work,passed);test_archive(work,passed);test_source_layout(work,passed)
        test_compiler(work,passed);test_mocked_pipeline(work,passed);test_initial_import_readonly(work,passed)
    return {'schema':'Report172-build-tests-v1','optimization_level':sys.flags.optimize,
            'status':'passed','count':len(passed),'tests':passed}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    if args.output and (args.output.exists() or args.output.is_symlink()):parser.error('refusing existing output')
    data=json_bytes(run_tests())
    if args.output:write_new(args.output,data)
    else:sys.stdout.buffer.write(data)
if __name__=='__main__':main()
