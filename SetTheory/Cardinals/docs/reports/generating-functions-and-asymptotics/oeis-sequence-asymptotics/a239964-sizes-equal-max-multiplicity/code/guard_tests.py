#!/usr/bin/env python3
"""Fail-closed guard tests and genuine ZIP-extracted rebuilds for Report196.

Default tests unit guards, then four complete builds: source normal/-O and
separately ZIP-extracted normal/-O. --unit-only avoids recursive build tests.
--full1000 makes all four builds recompute the entire 1,001-term reference.
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
import zipfile

sys.dont_write_bytecode=True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import build as builder


def need(condition,message):
    if not condition: raise ValueError(message)


def unit_tests():
    passed=[]
    def rejected(name,action):
        try: action()
        except (ValueError,OSError): passed.append(name)
        else: raise ValueError('guard accepted invalid input: '+name)
    with tempfile.TemporaryDirectory(prefix='report196-guards-') as temporary:
        root=Path(temporary)
        counter=0
        def fixture():
            nonlocal counter
            counter+=1
            source=root/('source%d'%counter);source.mkdir()
            for name in builder.SOURCES:
                path=source/name;path.parent.mkdir(parents=True,exist_ok=True)
                builder.write_new(path,b'fixture\n')
            builder.freeze_source(source)
            return source
        source=fixture()
        builder.validate_source(source)
        need(builder.fresh_output(root/'fresh',source)==root/'fresh','fresh destination refused')
        passed.extend(('valid_closed_source_manifest','fresh_disjoint_destination'))
        for name in ('existing_file','existing_directory','existing_symlink','dangling_symlink'):
            target=root/name
            if name=='existing_file': target.write_bytes(b'unchanged')
            elif name=='existing_directory': target.mkdir()
            else: target.symlink_to(source if name=='existing_symlink' else root/'missing')
            rejected(name,lambda t=target:builder.fresh_output(t,source))
        need((root/'existing_file').read_bytes()==b'unchanged','existing destination was altered')
        rejected('source_descendant',lambda:builder.fresh_output(source/'output',source))
        rejected('destination_parent_traversal',lambda:builder.fresh_output(root/'missing'/'..'/'out',source))
        link=root/'linked_parent';link.symlink_to(root,target_is_directory=True)
        rejected('symlink_destination_ancestor',lambda:builder.fresh_output(link/'out',source))
        rejected('symlink_source_root',lambda:builder.validate_source(root/'existing_symlink'))
        rejected('missing_destination_parent',lambda:builder.fresh_output(root/'no_parent'/'out',source))
        cases=(('absolute_name','/escape'),('parent_name','../escape'),('embedded_parent','data/../escape'),
               ('backslash_name','data\\escape'),('drive_name','C:escape'),('duplicate_slash','data//escape'),
               ('dot_component','data/./escape'),('cache_name','__pycache__/x.pyc'),('hidden_name','.x'),
               ('control_name','data/\nx'),('empty_name',''))
        for name,path in cases: rejected(name,lambda p=path:builder.safe_name(p))
        for name,mutation in (
            ('modified_source_hash',lambda s:(s/'verify.py').write_bytes(b'changed\n')),
            ('missing_source_file',lambda s:(s/'verify.py').unlink()),
            ('extra_source_file',lambda s:(s/'extra.txt').write_bytes(b'extra\n')),
            ('extra_empty_directory',lambda s:(s/'empty').mkdir()),
            ('cache_directory',lambda s:(s/'__pycache__').mkdir()),
            ('unmanifested_pdf',lambda s:(s/'Report196.pdf').write_bytes(b'%PDF-')),
            ('missing_manifest',lambda s:(s/builder.SOURCE_MANIFEST).unlink()),
            ('source_symlink',lambda s:((s/'verify.py').unlink(),(s/'verify.py').symlink_to(root/'existing_file'))),
            ('source_directory_symlink',lambda s:(shutil.rmtree(s/'data'),(s/'data').symlink_to(source/'data',target_is_directory=True))),
        ):
            test=fixture();mutation(test)
            rejected(name,lambda s=test:builder.validate_source(s))
        for name,alter in (
            ('manifest_missing_entry',lambda d:d['files'].pop('verify.py')),
            ('manifest_extra_entry',lambda d:d['files'].update({'extra.txt':{'bytes':0,'sha256':'0'*64}})),
            ('manifest_boolean_size',lambda d:d['files']['verify.py'].update({'bytes':True})),
            ('manifest_negative_size',lambda d:d['files']['verify.py'].update({'bytes':-1})),
            ('manifest_invalid_digest',lambda d:d['files']['verify.py'].update({'sha256':'X'*64})),
            ('manifest_wrong_report',lambda d:d.update({'report':195})),
            ('manifest_wrong_schema',lambda d:d.update({'schema':'wrong'})),
            ('manifest_wrong_self_exclusion',lambda d:d.update({'self_excluded':'verify.py'})),
        ):
            test=fixture();path=test/builder.SOURCE_MANIFEST
            document=builder.load_json(path.read_bytes());alter(document);path.write_bytes(builder.canonical(document))
            rejected(name,lambda s=test:builder.validate_source(s))
        for name,payload in (('duplicate_json_key',b'{"a":1,"a":2}'),('nan_json',b'{"a":NaN}'),
                             ('float_json',b'{"a":1.0}'),('infinity_json',b'{"a":Infinity}')):
            rejected(name,lambda p=payload:builder.load_json(p))
        # A real complete manifest must cover generated output and the source manifest.
        complete=fixture()
        for name in builder.GENERATED:
            path=complete/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(b'generated\n')
        names=set(builder.SOURCES)|{builder.SOURCE_MANIFEST}|set(builder.GENERATED)
        (complete/builder.MANIFEST).write_bytes(builder.canonical(builder.manifest_document(complete,names,'complete')))
        builder.validate_source(complete);passed.append('valid_closed_complete_manifest')
        (complete/'generated/verification.json').write_bytes(b'tampered\n')
        rejected('complete_generated_hash',lambda:builder.validate_source(complete))
        # Simulate a same-size edit specifically between digest validation and
        # the final payload read. Only verified bytes may be returned/copied.
        changing=fixture();saved_reader=builder.read_regular;reads=0
        def changing_reader(path,limit=builder.MAX_FILE):
            nonlocal reads
            data=saved_reader(path,limit)
            if Path(path)==changing/'verify.py':
                reads+=1
                if reads>=3: return b'changed\n'
            return data
        builder.read_regular=changing_reader
        try: rejected('changed_payload_after_validation',lambda:builder.validate_source(changing))
        finally: builder.read_regular=saved_reader
        # No security or mathematical check is disabled by optimization.
        for name in ('build.py','verify.py','guard_tests.py','symbolic_checks.py'):
            tree=ast.parse((ROOT/name).read_text())
            need(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)),'assert-based guard in '+name)
        passed.append('no_assert_guards')
    return {'schema':'report196-guard-tests-v1','status':'PASS','unit_guards':passed,
            'unit_guard_count':len(passed),'extracted_rebuilds_run':False}


def extract_checked(archive,destination):
    """Extract only a new closed, regular-file package; never use extractall."""
    destination.mkdir(exist_ok=False)
    expected=set(builder.SOURCES)|{builder.SOURCE_MANIFEST}|set(builder.GENERATED)|{builder.MANIFEST}
    with zipfile.ZipFile(archive) as source:
        members=source.infolist()
        need(len(members)==len(expected) and {i.filename for i in members}==expected,'ZIP inventory differs')
        for item in members:
            builder.safe_name(item.filename)
            need(stat.S_ISREG(item.external_attr>>16) and not item.is_dir(),'nonregular ZIP entry')
            need(item.file_size<=builder.MAX_FILE,'ZIP entry too large')
            path=destination/item.filename;path.parent.mkdir(parents=True,exist_ok=True)
            builder.write_new(path,source.read(item))
    builder.validate_source(destination)


def rebuild_tests(full1000=False):
    builder.validate_source(ROOT)
    original=builder.snapshot(ROOT)
    with tempfile.TemporaryDirectory(prefix='report196-rebuild-tests-',dir=ROOT.parent) as temporary:
        temp=Path(temporary)
        def run(source,destination,optimized):
            flags=['-I','-S','-B']+(['-O'] if optimized else [])
            command=[sys.executable,*flags,str(source/'build.py'),str(destination)]
            if full1000: command.append('--full1000')
            result=subprocess.run(command,cwd=temp,capture_output=True,text=True,timeout=7200)
            need(result.returncode==0,'actual rebuild failed: '+(result.stdout+result.stderr)[-12000:])
            document=builder.load_json(result.stdout)
            need(document.get('status')=='PASS','actual rebuild did not report PASS')
            return document
        roots=[temp/name for name in ('source_normal','source_optimized','extracted_normal','extracted_optimized')]
        summaries=[run(ROOT,roots[0],False),run(ROOT,roots[1],True)]
        first=builder.snapshot(roots[0])
        need(builder.snapshot(roots[1])==first,'normal/-O full builds differ')
        for index,optimized in ((2,False),(3,True)):
            extracted=temp/('unpacked%d'%index)
            extract_checked(roots[0]/'Report196_code.zip',extracted)
            before=builder.snapshot(extracted)
            summaries.append(run(extracted,roots[index],optimized))
            need(builder.snapshot(extracted)==before,'extracted source changed')
            need(builder.snapshot(roots[index])==first,'ZIP-extracted rebuild differs')
        need(all(item==summaries[0] for item in summaries),'rebuild summaries differ')
        need(builder.snapshot(ROOT)==original,'original sources changed')
        return {'extracted_rebuilds_run':True,'actual_build_count':4,'full1000_recomputed':full1000,
                'source_normal_optimized_equal':True,'extracted_normal_optimized_equal':True,
                'all_complete_output_trees_byte_identical':True,'all_source_trees_preserved':True,
                'pdf_sha256':summaries[0]['pdf_sha256'],'zip_sha256':summaries[0]['zip_sha256']}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--unit-only',action='store_true')
    parser.add_argument('--full1000',action='store_true')
    parser.add_argument('--output',type=Path,help='new JSON result file')
    args=parser.parse_args()
    need(not (args.unit_only and args.full1000),'--full1000 requires rebuild tests')
    if args.output: need(not args.output.exists() and not args.output.is_symlink(),'result output already exists')
    result=unit_tests()
    if not args.unit_only: result.update(rebuild_tests(args.full1000))
    payload=builder.canonical(result)
    if args.output: builder.write_new(args.output,payload)
    sys.stdout.buffer.write(payload)


if __name__=='__main__':
    try: main()
    except (OSError,ValueError,subprocess.SubprocessError) as error:
        print('guard tests failed: '+str(error),file=sys.stderr)
        raise SystemExit(2)
