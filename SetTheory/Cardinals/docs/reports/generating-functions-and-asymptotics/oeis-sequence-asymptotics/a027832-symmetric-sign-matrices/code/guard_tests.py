#!/usr/bin/env python3
"""Finite boundary, filesystem, manifest and archive guards for Report239.

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
from common import ROOT, ARTIFACT_STEM, child_environment, emit, new_file_path, python_command, require
from exact_counts import (capped_graph_count, mixed_graph_count, sign_matrix_count,
    brute_sign_matrices, brute_mixed_graphs, verify)
from diagnostics import capped_moments, fixed_saddle, diagnostics
from constant_certificate import certified_constants
from reproduce_zip import archive_contents


def tests():
    passed = []
    spec = importlib.util.spec_from_file_location('sign_matrix_build', ROOT/'build.py')
    build = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(build)
    def reject(label, call):
        try:
            call()
        except (ValueError, OSError, RuntimeError, zipfile.BadZipFile):
            passed.append(label)
            return
        raise RuntimeError('guard failed: '+label)
    # Bounds and type checks must run before arithmetic, enumeration or I/O.
    for label,fun,maximum,minimum in (
            ('sign matrices',sign_matrix_count,17,0),
            ('direct signs',brute_sign_matrices,5,0),
            ('exact verify',verify,17,1),
            ('diagnostics',diagnostics,2001,21),
            ('constant certificate',certified_constants,40,20)):
        for value in (minimum-1,maximum+1,True,1.0,'1',None):
            reject(label+' rejects '+repr(value),lambda f=fun,v=value:f(v))
    for value in (None,'1',True,(),):
        if value == ():
            require(capped_graph_count(value)==1,'empty capped graph count')
        else:
            reject('caps rejects '+repr(value),lambda v=value:capped_graph_count(v))
    for value in ([True],[1.0],[1],[0]*13,[-1,0]):
        reject('caps rejects '+repr(value),lambda v=value:capped_graph_count(v))
    for fun,max_M in ((mixed_graph_count,18),(brute_mixed_graphs,6)):
        for M,k,f in ((-1,0,0),(max_M+1,0,0),(True,0,0),(2.0,0,0),
                      (2,-1,0),(2,2,0),(2,True,0),(2,1.0,0),
                      (2,1,-1),(2,1,3),(2,1,True),(2,1,1.0)):
            reject(fun.__name__+' rejects '+repr((M,k,f)),lambda fn=fun,a=M,b=k,c=f:fn(a,b,c))
    reject('mixed caps above practical domain',lambda:mixed_graph_count(18,9,1))
    for M,k in ((7,3),(2002,1000),(True,0),(8.0,3),(8,True),(8,3.0),(8,2)):
        reject('saddle rejects '+repr((M,k)),lambda a=M,b=k:fixed_saddle(a,b))
    for b,r,k in ((0,.5,0),(2001,.5,0),(True,.5,0),(2.0,.5,0),
                  (2,.5,-1),(2,.5,3),(2,.5,True),(2,.5,1.0),
                  (2,0,1),(2,1,1),(2,True,1),(2,float('nan'),1),
                  (2,float('inf'),1),(2,'0.5',1)):
        reject('moments rejects '+repr((b,r,k)),lambda a=b,p=r,c=k:capped_moments(a,p,c))
    for value in (-1,3,True,1.0):
        reject('Python optimization level rejects '+repr(value),lambda v=value:python_command(v))
    for value in (0,10000,True,239.0,238):
        reject('report number rejects '+repr(value),lambda v=value:build.compile_pdf(Path('/unused'),v))
    import exact_counts
    old_states,old_transitions=exact_counts.MAX_STATES,exact_counts.MAX_TRANSITIONS
    try:
        exact_counts.MAX_STATES=0
        reject('state budget stops recursion',lambda:capped_graph_count([1,1,1]))
        exact_counts.MAX_STATES=old_states
        exact_counts.MAX_TRANSITIONS=0
        reject('transition budget stops recursion',lambda:capped_graph_count([1,1,1]))
    finally:
        exact_counts.MAX_STATES=old_states
        exact_counts.MAX_TRANSITIONS=old_transitions
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
                                capture_output=True,check=False)
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
    with tempfile.TemporaryDirectory(prefix='sign_matrix-guards-') as tmp:
        work = Path(tmp)
        existing = work/'existing'; existing.write_text('untouched',encoding='utf-8')
        directory = work/'directory'; directory.mkdir()
        live = work/'live'; live.symlink_to(directory,target_is_directory=True)
        dangling = work/'dangling'; dangling.symlink_to(work/'missing',target_is_directory=True)
        paths = ['',str(existing),str(directory),str(ROOT/'forbidden.json'),
                 str(ROOT/'code/count_receipt.json'),str(ROOT/'code/diagnostic_receipt.json'),
                 str(ROOT/'code/guard_receipt.json'),str(live/'out'),str(dangling/'out'),
                 str(work)+'/directory/../out',str(work)+'/./out',
                 str(work/'missing-parent/out'),str(work/'back\\slash')]
        for i,path in enumerate(paths):
            reject('file output path guard %d'%i,lambda p=path:new_file_path(p))
            reject('build output path guard %d'%i,lambda p=path:build.new_output(p))
        destination = work/'valid.json'; emit({'ok':True},str(destination))
        reject('exclusive file creation refuses reuse',lambda:emit({'ok':False},str(destination)))
        require(existing.read_text()=='untouched' and 'true' in destination.read_text(),'existing file changed')
        passed.append('preexisting files remain unchanged')
        commands = [[str(ROOT/'code/exact_counts.py'),'--n','641'],
                    [str(ROOT/'code/exact_counts.py'),'--output',str(existing)],
                    [str(ROOT/'code/diagnostics.py'),'--output',str(live/'bad')],
                    [str(ROOT/'code/constant_certificate.py'),'--unknown'],
                    [str(ROOT/'code/reproduce_zip.py'),'--archive',str(work/'absent.zip'),'--output-dir',str(existing)],
                    [str(ROOT/'build.py'),'--output-dir',str(dangling/'bad')],
                    [str(ROOT/'build.py'),'--verify-only','--output-dir',str(work/'unused')],
                    [str(ROOT/'build.py'),'--report-number','237','--verify-only']]
        for i,command in enumerate(commands):
            result = subprocess.run(python_command()+command,env=child_environment(),capture_output=True,check=False)
            require(result.returncode != 0,'CLI accepted invalid case %d'%i)
            passed.append('CLI rejects invalid case %d'%i)
        require(not (work/'unused').exists(),'invalid CLI created output')
        required = ('README.md','SOURCES.md','article.tex',ARTIFACT_STEM+'.pdf','build.py',
                    'code/common.py','code/exact_counts.py',
                    'code/constant_certificate.py','code/oeis_prefix.json','code/diagnostics.py','code/guard_tests.py',
                    'code/reproduce_zip.py','code/count_receipt.json','code/diagnostic_receipt.json',
                    'code/certificate_receipt.json','code/guard_receipt.json',
                    'requirements.txt','COMPUTATION.md','sections/example.tex')
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
    return {'status':'PASS','guard_count':len(passed),'guards':passed,
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
    except (ValueError,RuntimeError,OSError,ArithmeticError,zipfile.BadZipFile) as exc:
        raise SystemExit(str(exc))
