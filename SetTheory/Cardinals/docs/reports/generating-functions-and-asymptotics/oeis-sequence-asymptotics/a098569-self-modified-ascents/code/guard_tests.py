#!/usr/bin/env python3
"""Finite boundary, filesystem, manifest and archive guards for Report242.

Run normally and with -O. No assertions implement validation. Disposable fixture
files are outside the sources; no Python or TeX supplied by a fixture is run.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
import ast
import hashlib
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import warnings
import zipfile
from common import ROOT, ARTIFACT_STEM, REPORT_NUMBER, child_environment, emit, new_file_path, python_command, require
from exact_counts import row, counts, triangle, integer_record, polynomial_rows, collision_moment_rows, verify
from algebra_checks import contraction, contraction_terms, gaussian_moment
from saddle_diagnostics import run_case, saddle, verify as verify_saddles
from reproduce_zip import archive_contents


def tests():
    passed = []
    spec = importlib.util.spec_from_file_location('selfmodified_build', ROOT/'build.py')
    build = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(build)
    def reject(label, call):
        try:
            call()
        except (ValueError, OSError, RuntimeError, zipfile.BadZipFile):
            passed.append(label)
            return
        raise RuntimeError('guard failed: '+label)
    for fun,lower,upper in ((row,0,2000),(counts,0,2000),(polynomial_rows,0,40),
                             (collision_moment_rows,0,40),(verify,26,40),(contraction,0,3),(contraction_terms,0,3),
                             (gaussian_moment,0,32),(run_case,100,2000),(saddle,100,2000),
                             (verify_saddles,100,2000)):
        for value in (lower-1,upper+1,True,1.0,'1',None):
            reject(fun.__name__+' rejects '+repr(value),lambda f=fun,v=value:f(v))
    for fun in (row,polynomial_rows,contraction,contraction_terms):
        for value in (None,0,1,'true',1.0):
            reject(fun.__name__+' binary flag rejects '+repr(value),lambda f=fun,v=value:f(1,v))
    for value in (-1,2000,True,1.0,'1',None):
        reject('triangle row rejects '+repr(value),lambda v=value:triangle(v,0))
    for value in (-1,3,True,1.0,'1',None):
        reject('triangle column rejects '+repr(value),lambda v=value:triangle(2,v))
    for value in (-1,True,1.0,'1',None):
        reject('integer record rejects '+repr(value),lambda v=value:integer_record(v))
    reject('integer byte record finite bit cutoff',lambda:integer_record(1<<40001))
    for fun in (run_case,saddle):
        for value in ('1','NaN','inf','-inf','0.0',0,True,None):
            reject(fun.__name__+' mark rejects '+repr(value),lambda f=fun,v=value:f(100,v))
    for value in (None,0,1,'true'):
        reject('saddle binary flag rejects '+repr(value),lambda v=value:saddle(100,'0',v))
    reject('binary contraction cutoff',lambda:contraction(3,True))
    reject('binary term enumeration cutoff',lambda:contraction_terms(3,True))
    require(counts(0)==(1,1) and row(0)==[1] and row(0,True)==[1],'empty count convention')
    require(collision_moment_rows(0)=={0:[(1,0,0)]},'empty collision moments')
    require(collision_moment_rows(2)[1]==[(1,0,0)] and collision_moment_rows(2)[2]==[(1,1,0),(1,0,0)],'collision zero-residual and singleton-cell boundaries')
    require(row(2,True)==[0,1] and triangle(0,0)==1,'binary infeasibility and triangle origin')
    require(gaussian_moment(0)==1 and gaussian_moment(1)==0 and gaussian_moment(6)==15,'Gaussian moment boundaries')
    require(contraction(0)==1 and contraction(0,True)==1,'zeroth contractions')
    require(integer_record(0)['unsigned_big_endian_sha256']==hashlib.sha256(bytes([0])).hexdigest(),'zero byte hash convention')
    require('decimal' not in integer_record(1<<3000),'large count must not become a decimal string')
    passed.append('empty, infeasible binary, triangle and Gaussian boundary conventions')
    passed.append('large exact counts hashed as bytes without decimal conversion')
    for value in (-1,3,True,1.0):
        reject('Python optimization level rejects '+repr(value),lambda v=value:python_command(v))
    for value in (0,10000,True,242.0,241):
        reject('report number rejects '+repr(value),lambda v=value:build.compile_pdf(Path('/unused'),v))
    reject('decimal digit cap',lambda:int('1'*641))
    for path in sorted(ROOT.rglob('*.py')):
        require(not any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(path.read_text()))),
                'validation must not use assert: '+path.name)
    passed.append('all public Python sources contain no assert statements')
    require('-B' in python_command(), 'child Python must disable bytecode')
    require('int_max_str_digits=640' in python_command(), 'child command must set decimal cap explicitly')
    require(child_environment()['PYTHONINTMAXSTRDIGITS']=='640','child decimal cap lost')
    require(child_environment()['PYTHONOPTIMIZE']=='0','ambient optimization level must be cleared')
    passed.append('Python child -B, explicit -X digitcap640, and optimization configured')
    hostile_env = child_environment()
    hostile_env.update(PYTHONDONTWRITEBYTECODE='0',PYTHONINTMAXSTRDIGITS='0',PYTHONOPTIMIZE='2')
    for level in (0,1,2):
        probe = ('import sys;sys.exit(0 if sys.get_int_max_str_digits()==640 '
                 'and sys.dont_write_bytecode and sys.flags.optimize==%d else 2)'%level)
        result = subprocess.run(python_command(level)+['-E','-c',probe],env=hostile_env,
                                capture_output=True,check=False,timeout=30)
        require(result.returncode==0,'explicit child flags lost under -E and hostile environment')
        passed.append('Python level %d with -E preserves bytecode and decimal-cap flags'%level)
    for command in (['pdftex','-ini'],['pdflatex','-fmt=./pdflatex.fmt']):
        tree = ast.parse((ROOT/'build.py').read_text())
        lists = [node for node in ast.walk(tree) if isinstance(node,ast.List)]
        matching = [node for node in lists if len(node.elts)>=2 and all(
                    isinstance(node.elts[i],ast.Constant) and node.elts[i].value==command[i]
                    for i in range(2))]
        require(matching and all(any(isinstance(x,ast.Constant) and x.value=='-no-shell-escape'
                                    for x in node.elts) for node in matching),'TeX shell escape guard')
    passed.append('private format and document TeX commands disable shell escape')
    temporary_root=Path('/tmp')
    require(temporary_root.is_dir() and not temporary_root.is_symlink(), 'external /tmp directory required')
    require(temporary_root != ROOT and ROOT not in temporary_root.parents, 'temporary root must be outside sources')
    for source in (ROOT/'build.py',ROOT/'code/guard_tests.py'):
        tree=ast.parse(source.read_text())
        calls=[node for node in ast.walk(tree) if isinstance(node,ast.Call) and
               isinstance(node.func,ast.Attribute) and node.func.attr=='TemporaryDirectory']
        require(calls and all(any(keyword.arg=='dir' for keyword in node.keywords) for node in calls),
                'temporary directories require explicit external parents')
    passed.append('TeX and guard scratch have explicit external parents independent of TMPDIR')
    with tempfile.TemporaryDirectory(prefix='report242-guards-',dir=temporary_root) as tmp:
        work = Path(tmp)
        existing = work/'existing'; existing.write_text('untouched',encoding='utf-8')
        directory = work/'directory'; directory.mkdir()
        live = work/'live'; live.symlink_to(directory,target_is_directory=True)
        dangling = work/'dangling'; dangling.symlink_to(work/'missing',target_is_directory=True)
        paths = ['',str(existing),str(directory),str(ROOT/'forbidden.json'),
                 str(ROOT/'code/count_receipt.json'),str(ROOT/'code/algebra_receipt.json'),
                 str(ROOT/'code/guard_receipt.json'),str(live/'out'),str(dangling/'out'),
                 str(work)+'/directory/../out',str(work)+'/./out',
                 str(work/'missing-parent/out'),str(work/'back\\slash')]
        for i,path in enumerate(paths):
            reject('file output path guard %d'%i,lambda p=path:new_file_path(p))
            reject('build output path guard %d'%i,lambda p=path:build.new_output(p))
        for value in (True,1,None,b'bytes'):
            reject('output path type '+repr(value),lambda v=value:new_file_path(v))
            reject('build output path type '+repr(value),lambda v=value:build.new_output(v))
            reject('TeX logs path type '+repr(value),lambda v=value:build.compile_pdf(v))
        for index,value in enumerate((str(ROOT),str(ROOT/'code'),str(live),str(dangling),str(existing),str(work/'absent'))):
            reject('TeX logs path rejects invalid case %d'%index,lambda v=value:build.compile_pdf(v))
        destination = work/'valid.json'; emit({'ok':True},str(destination))
        reject('exclusive file creation refuses reuse',lambda:emit({'ok':False},str(destination)))
        require(existing.read_text()=='untouched' and 'true' in destination.read_text(),'existing file changed')
        passed.append('preexisting files remain unchanged')
        commands = [[str(ROOT/'code/exact_counts.py'),'--max-n','41'],
                    [str(ROOT/'code/exact_counts.py'),'--max-n','1'*641],
                    [str(ROOT/'code/exact_counts.py'),'--output',str(existing)],
                    [str(ROOT/'code/algebra_checks.py'),'--output',str(live/'bad')],
                    [str(ROOT/'code/algebra_checks.py'),'--unknown'],
                    [str(ROOT/'code/saddle_diagnostics.py'),'--max-n','2001'],
                    [str(ROOT/'code/saddle_diagnostics.py'),'--output',str(existing)],
                    [str(ROOT/'code/reproduce_zip.py'),'--archive',str(work/'absent.zip'),'--output-dir',str(existing)],
                    [str(ROOT/'build.py'),'--output-dir',str(dangling/'bad')],
                    [str(ROOT/'build.py'),'--verify-only','--output-dir',str(work/'unused')],
                    [str(ROOT/'build.py'),'--report-number','241','--verify-only']]
        for i,command in enumerate(commands):
            result = subprocess.run(python_command()+command,env=child_environment(),capture_output=True,check=False,timeout=30)
            require(result.returncode != 0,'CLI accepted invalid case %d'%i)
            passed.append('CLI rejects invalid case %d'%i)
        require(not (work/'unused').exists(),'invalid CLI created output')
        required = tuple(sorted(build.REQUIRED))+('sections/example.tex',)
        serial = 0
        def fixture():
            nonlocal serial
            serial += 1
            root = work/('manifest-fixture-%d'%serial); root.mkdir()
            lines = []
            for name in required:
                target = root/name; target.parent.mkdir(exist_ok=True)
                target.write_bytes(b'inert fixture\n')
                lines.append(hashlib.sha256(target.read_bytes()).hexdigest()+'  '+name)
            (root/'MANIFEST.sha256').write_text('\n'.join(lines)+'\n',encoding='utf-8')
            build.ROOT = root
            return root
        original_root = build.ROOT
        try:
            fixture(); build.verify(); passed.append('valid complete manifest verifies')
            mutations = [('changed bytes',lambda root:(root/'README.md').write_text('changed')),
                         ('extra file',lambda root:(root/'extra').write_text('extra')),
                         ('extra empty directory',lambda root:(root/'extra').mkdir()),
                         ('missing file',lambda root:(root/'README.md').unlink()),
                         ('nonregular source',lambda root:os.mkfifo(root/'fifo')),
                         ('symlink file',lambda root:(root/'extra').symlink_to(root/'README.md')),
                         ('symlink directory',lambda root:(root/'extra').symlink_to(root/'code',target_is_directory=True))]
            for label,mutate in mutations:
                root = fixture(); mutate(root); reject('manifest rejects '+label,build.verify)
            bad_lines = ['0'*64+'  ../escape','0'*64+'  ./dot','0'*64+'  /absolute',
                         '0'*64+'  code\\bad','0'*64+'  MANIFEST.sha256','g'*64+'  file','malformed line']
            for i,line in enumerate(bad_lines):
                root = fixture(); manifest = root/'MANIFEST.sha256'
                manifest.write_text(manifest.read_text()+line+'\n')
                reject('manifest rejects malformed entry %d'%i,build.verify)
            root = fixture(); manifest = root/'MANIFEST.sha256'
            manifest.write_text(manifest.read_text()+manifest.read_text().splitlines()[0]+'\n')
            reject('manifest rejects duplicate entry',build.verify)
            root = fixture()
            with (root/'oversized').open('wb') as handle:handle.truncate(32*1024*1024+1)
            reject('manifest inventory rejects source byte cutoff',build.verify)
            root = fixture()
            for index in range(1001):(root/('directory-%d'%index)).mkdir()
            reject('manifest inventory rejects source entry cutoff',build.verify)
            root = fixture(); (root/'MANIFEST.sha256').write_text('x'*131073)
            reject('manifest size cutoff',build.verify)
            root = fixture(); external=root/'external-paper.pdf';external.write_bytes(b'not public')
            manifest=root/'MANIFEST.sha256';manifest.write_text(manifest.read_text()+hashlib.sha256(external.read_bytes()).hexdigest()+'  external-paper.pdf\n')
            reject('manifest rejects nonpublic file even with matching hash',build.verify)
            root = fixture(); (root/'MANIFEST.sha256').write_text('')
            reject('manifest rejects empty entries',build.verify)
            root = fixture(); (root/'README.md').unlink(); manifest=root/'MANIFEST.sha256'
            manifest.write_text('\n'.join(line for line in manifest.read_text().splitlines()
                                          if not line.endswith('  README.md'))+'\n')
            reject('manifest rejects missing required file even with matching hashes',build.verify)
        finally:
            build.ROOT = original_root
        # Test archive parser boundaries with inert bytes only.
        def archive_fixture(name,entries):
            path = work/name
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',UserWarning)
                with zipfile.ZipFile(path,'x',compression=zipfile.ZIP_STORED) as archive:
                    for member,mode,method in entries:
                        info=zipfile.ZipInfo(member,(2026,10,5,0,0,0));info.create_system=3
                        info.external_attr=mode<<16;info.compress_type=method
                        archive.writestr(info,b'inert\n')
            return path
        prefix = [(ARTIFACT_STEM+'/build.py',0o100644,0),(ARTIFACT_STEM+'/MANIFEST.sha256',0o100644,0)]
        archive_contents(archive_fixture('good.zip',prefix));passed.append('valid inert ZIP format accepted')
        bad_members = [('traversal',ARTIFACT_STEM+'/../escape',0o100644,0),
                       ('absolute','/'+ARTIFACT_STEM+'/escape',0o100644,0),
                       ('dot',ARTIFACT_STEM+'/./escape',0o100644,0),
                       ('backslash',ARTIFACT_STEM+'/code\\escape',0o100644,0),
                       ('wrong root','Other/escape',0o100644,0),
                       ('control character',ARTIFACT_STEM+'/line\nbreak',0o100644,0),
                       ('duplicate',ARTIFACT_STEM+'/build.py',0o100644,0),
                       ('symlink',ARTIFACT_STEM+'/link',0o120777,0),
                       ('directory',ARTIFACT_STEM+'/code/',0o40755,0),
                       ('compressed',ARTIFACT_STEM+'/compressed',0o100644,zipfile.ZIP_DEFLATED)]
        for i,(label,name,mode,method) in enumerate(bad_members):
            path=archive_fixture('bad%d.zip'%i,prefix+[(name,mode,method)])
            reject('ZIP rejects '+label,lambda p=path:archive_contents(p))
        path=archive_fixture('missing.zip',[(ARTIFACT_STEM+'/README.md',0o100644,0)])
        reject('ZIP rejects missing build and manifest',lambda:archive_contents(path))
        path=archive_fixture('many.zip',[(ARTIFACT_STEM+'/member%d'%i,0o100644,0) for i in range(501)])
        reject('ZIP rejects excessive member count',lambda:archive_contents(path))
        link=work/'archive-link.zip';link.symlink_to(work/'good.zip')
        reject('ZIP rejects symlink input',lambda:archive_contents(link))
        nested=directory/'inside.zip';nested.write_bytes((work/'good.zip').read_bytes())
        reject('ZIP rejects symlink ancestor',lambda:archive_contents(live/'inside.zip'))
        path=archive_fixture('wrong-date.zip',prefix)
        with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_STORED) as archive:
            info=zipfile.ZipInfo(ARTIFACT_STEM+'/build.py',(2025,1,1,0,0,0))
            info.create_system=3;info.external_attr=0o100644<<16;archive.writestr(info,b'inert')
        reject('ZIP rejects wrong timestamp',lambda:archive_contents(path))
        path=archive_fixture('archive-comment.zip',prefix)
        with zipfile.ZipFile(path,'a') as archive:archive.comment=b'forbidden'
        reject('ZIP rejects archive comment',lambda:archive_contents(path))
    return {'status':'PASS','report_number':REPORT_NUMBER,'guard_count':len(passed),'guards':passed,
            'integer_decimal_digit_cap':sys.get_int_max_str_digits(),
            'scope':'Finite boundary and filesystem guard tests; not a general security proof or protection against hostile concurrent filesystem mutation.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args=parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(tests(),args.output)


if __name__=='__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError,zipfile.BadZipFile,subprocess.TimeoutExpired) as exc:
        raise SystemExit(str(exc))
