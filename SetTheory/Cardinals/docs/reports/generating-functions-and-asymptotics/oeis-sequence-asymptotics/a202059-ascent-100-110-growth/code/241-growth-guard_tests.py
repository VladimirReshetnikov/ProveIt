#!/usr/bin/env python3
"""Finite boundary, filesystem, manifest and archive guards for Report241.

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
from exact_counts import (checked_word, ascent_count, is_ascent, literal_avoidance,
                          fast_avoidance, raw_ascent_words, recurrence_count,
                          triple_class_prefix, verify)
from construction import (stage_sizes, block_count, family_count, specification,
                          chunk_increasing, chunk_permutations, constructed_family,
                          fresh_record_padding, sampled_word, verify as verify_construction)
from upper_bound import (encode_word, decode_word, finite_upper_bound, vandermonde_bound,
                         verify as verify_upper)
from reproduce_zip import archive_contents


def tests():
    passed = []
    spec = importlib.util.spec_from_file_location('ascent_build', ROOT/'build.py')
    build = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(build)
    def reject(label, call):
        try:
            call()
        except (ValueError, OSError, RuntimeError, zipfile.BadZipFile):
            passed.append(label)
            return
        raise RuntimeError('guard failed: '+label)
    for fun,maximum in ((finite_upper_bound,64),(verify_upper,9)):
        for value in (-1,maximum+1,True,1.0,'1',None):
            reject(fun.__name__+' argument rejects '+repr(value),lambda f=fun,v=value:f(v))
    for fun,argument in ((encode_word,()),(decode_word,(0,(),(),(),()))):
        for value in (99,101,111,True,100.0,'100',None):
            reject(fun.__name__+' pattern rejects '+repr(value),lambda f=fun,a=argument,v=value:f(a,v))
    for value in (None,'012',True,[True],[1.0],[-1],[100001],[0]*65,(0,2)):
        reject('encode word rejects '+repr(value),lambda v=value:encode_word(v,100))
    reject('100 encoding rejects pattern occurrence',lambda:encode_word((0,1,0,0),100))
    reject('110 encoding rejects pattern occurrence',lambda:encode_word((0,1,1,0),110))
    malformed_encodings=(None,[],(),(True,(),(),(),()),(65,(),(),(),()),
        (1,[],(),(1,),((0,),)),(1,(True,),(0,),(1,), ((),)),
        (3,(1,0),(0,0),(3,),((0,),)),(2,(1,),(True,),(2,),((0,),)),
        (1,(),(),(True,),((0,),)),(2,(),(),(1,),((0,),)),
        (1,(),(),(1,),(0,)),(2,(),(),(2,),((0,0),)),
        (1,(),(),(1,),((True,),)),(1,(),(),(1,),((1,),)),
        (1,(0,),(0,),(1,), ((),)),(2,(),(),(1,1),((0,),(1,))))
    for index,value in enumerate(malformed_encodings):
        reject('decode malformed encoding %d'%index,lambda v=value:decode_word(v,100))
    reject('110 first/non-first status mismatch',lambda:decode_word((2,(0,),(0,),(1,1),((),(0,))),110))
    reject('100 last/non-last status mismatch',lambda:decode_word((2,(1,),(0,),(1,1),((0,),())),100))
    for value in (-1,64,True,1.0,'1',None):
        reject('Vandermonde r rejects '+repr(value),lambda v=value:vandermonde_bound(v,(1,),(1,)))
    for value in (None,'1',True,[True],[1.0],[-1],[65],[1]*65):
        reject('Vandermonde lengths reject '+repr(value),lambda v=value:vandermonde_bound(0,v,()))
    for value in (None,'1',True,[True],[1.0],[-1],[2],[]):
        reject('Vandermonde retained sizes reject '+repr(value),lambda v=value:vandermonde_bound(0,(1,),v))
    reject('Vandermonde excessive total length',lambda:vandermonde_bound(1,(64,1),(64,0)))
    reject('Vandermonde wrong retained total',lambda:vandermonde_bound(1,(2,),(2,)))
    reject('Vandermonde excessive run count',lambda:vandermonde_bound(0,(1,1),(1,1)))
    require(finite_upper_bound(0)==1 and vandermonde_bound(0,(),())==(1,1,1), 'empty upper-bound convention')
    for pattern in (100,110):
        require(decode_word(encode_word((),pattern),pattern)==(), 'empty encoding convention')
        require(decode_word(encode_word((0,0,0),pattern),pattern)==(0,0,0), 'repeated-zero encoding')
    passed.append('empty and repeated-zero structural encodings decode exactly')
    # Public numerical entry points validate types and bounds before enumeration.
    for label, fun, minimum, maximum in (
            ('raw words', raw_ascent_words, 0, 9),
            ('triple class', triple_class_prefix, 0, 11),
            ('count verifier', verify, 0, 9),
            ('construction verifier', verify_construction, 1, 7)):
        for value in (minimum-1, maximum+1, True, 1.0, '1', None):
            reject(label+' rejects '+repr(value), lambda f=fun,v=value:f(v))
    for fun, minimum, maximum in ((stage_sizes,1,2000), (specification,1,2000),
                                  (block_count,0,128),(family_count,1,64),
                                  (constructed_family,1,7)):
        for value in (minimum-1,maximum+1,True,1.0,'1',None):
            reject(fun.__name__+' first argument rejects '+repr(value), lambda f=fun,v=value:f(v,2))
        for value in (1,129,True,2.0,'2',None):
            reject(fun.__name__+' chunk bound rejects '+repr(value), lambda f=fun,v=value:f(1,v))
    for value in (-1,16,True,1.0,'1',None):
        reject('recurrence length rejects '+repr(value), lambda v=value:recurrence_count(v,100))
    for value in (99,101,111,True,100.0,'100',None):
        reject('recurrence pattern rejects '+repr(value), lambda v=value:recurrence_count(1,v))
    for value in (-1,16,True,1.0,'1',None):
        reject('verify recurrence argument rejects '+repr(value),lambda v=value:verify(0,v,0))
    for value in (-1,12,True,1.0,'1',None):
        reject('verify triple argument rejects '+repr(value),lambda v=value:verify(0,0,v))
    for fun in (checked_word,ascent_count,is_ascent,literal_avoidance,fast_avoidance):
        for value in (None,'012',True,[True],[1.0],[-1],[100001]):
            reject(fun.__name__+' word rejects '+repr(value),lambda f=fun,v=value:f(v))
    for value in (-1,100001,True,1.0,'1',None):
        reject('word bound rejects '+repr(value),lambda v=value:checked_word((),v))
    reject('word length finite cutoff',lambda:checked_word([0]*100001))
    reject('literal cubic-work cutoff',lambda:literal_avoidance([0]*81))
    for fun in (chunk_increasing,chunk_permutations):
        for value in (1,129,True,2.0,'2',None):
            reject(fun.__name__+' chunk bound rejects '+repr(value),lambda f=fun,v=value:f((),v))
        for value in (None,'012',True,[True],[1.0],[-1],[100001]):
            reject(fun.__name__+' labels reject '+repr(value),lambda f=fun,v=value:f(v,2))
    reject('chunk permutation label uniqueness',lambda:chunk_permutations((0,0),2))
    reject('chunk permutation size cutoff',lambda:chunk_permutations(tuple(range(9)),2))
    reject('chunk predicate size cutoff',lambda:chunk_increasing(tuple(range(129)),2))
    for value in (-1,100001,True,1.0,'1',None):
        reject('padding rejects '+repr(value),lambda v=value:fresh_record_padding((0,),v))
    reject('padding word-length sum cutoff',lambda:fresh_record_padding((0,),100000))
    reject('padding rejects illegal ascent input',lambda:fresh_record_padding((0,2),1))
    for value in (-1,2**32,True,1.0,'1',None):
        reject('sample seed rejects '+repr(value),lambda v=value:sampled_word(1,2,v))
    for value in (0,2001,True,1.0,'1',None):
        reject('sample size rejects '+repr(value),lambda v=value:sampled_word(v,2,0))
    for value in (1,129,True,2.0,'2',None):
        reject('sample chunk rejects '+repr(value),lambda v=value:sampled_word(1,v,0))
    reject('construction combined size cutoff',lambda:stage_sizes(2000,128))
    reject('sample combined size cutoff',lambda:sampled_word(2000,128,0))
    import construction
    old_family,old_label=construction.MAX_FAMILY,construction.MAX_LABEL
    try:
        construction.MAX_FAMILY=0
        reject('family budget stops enumeration',lambda:constructed_family(1,2))
        construction.MAX_LABEL=0
        reject('padding label budget stops extension',lambda:fresh_record_padding((0,),1))
    finally:
        construction.MAX_FAMILY,construction.MAX_LABEL=old_family,old_label
    require(is_ascent(()) and ascent_count(())==0 and literal_avoidance(())==(True,True,True),
            'empty-word convention')
    require(fast_avoidance((0,0,0))==(False,True,True),'000 boundary')
    require(fast_avoidance((1,0,0))==(True,False,True),'100 boundary')
    require(fast_avoidance((1,1,0))==(True,True,False),'110 boundary')
    require(fast_avoidance((2,0,1,0))[1] is False,'100 must be a subsequence')
    require(fast_avoidance((2,1,2,0))[2] is False,'110 must be a subsequence')
    require(not is_ascent((0,0,2)) and is_ascent((0,1,2)), 'entering ascent excluded from bound')
    require(list(constructed_family(1,2))==[(0,0,1,2)],'m=1 doubled-seed edge case')
    require(block_count(0,2)==1 and list(chunk_permutations((),2))==[()], 'empty block convention')
    passed.append('empty word, m=1, strict-ascent and arbitrary-subsequence positive boundaries')
    for value in (-1,3,True,1.0):
        reject('Python optimization level rejects '+repr(value),lambda v=value:python_command(v))
    for value in (0,10000,True,241.0,240):
        reject('report number rejects '+repr(value),lambda v=value:build.compile_pdf(Path('/unused'),v))
    import exact_counts
    old_states,old_transitions=exact_counts.MAX_STATES,exact_counts.MAX_TRANSITIONS
    try:
        exact_counts.MAX_STATES=0
        reject('state budget stops recurrence',lambda:recurrence_count(2,100))
        exact_counts.MAX_STATES=old_states
        exact_counts.MAX_TRANSITIONS=0
        reject('transition budget stops recurrence',lambda:recurrence_count(2,110))
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
    with tempfile.TemporaryDirectory(prefix='ascent-guards-',dir=temporary_root) as tmp:
        work = Path(tmp)
        existing = work/'existing'; existing.write_text('untouched',encoding='utf-8')
        directory = work/'directory'; directory.mkdir()
        live = work/'live'; live.symlink_to(directory,target_is_directory=True)
        dangling = work/'dangling'; dangling.symlink_to(work/'missing',target_is_directory=True)
        paths = ['',str(existing),str(directory),str(ROOT/'forbidden.json'),
                 str(ROOT/'code/count_receipt.json'),str(ROOT/'code/construction_receipt.json'),
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
        commands = [[str(ROOT/'code/exact_counts.py'),'--raw-n','641'],
                    [str(ROOT/'code/exact_counts.py'),'--raw-n','1'*641],
                    [str(ROOT/'code/exact_counts.py'),'--output',str(existing)],
                    [str(ROOT/'code/construction.py'),'--output',str(live/'bad')],
                    [str(ROOT/'code/construction.py'),'--unknown'],
                    [str(ROOT/'code/upper_bound.py'),'--max-n','10'],
                    [str(ROOT/'code/upper_bound.py'),'--output',str(existing)],
                    [str(ROOT/'code/reproduce_zip.py'),'--archive',str(work/'absent.zip'),'--output-dir',str(existing)],
                    [str(ROOT/'build.py'),'--output-dir',str(dangling/'bad')],
                    [str(ROOT/'build.py'),'--verify-only','--output-dir',str(work/'unused')],
                    [str(ROOT/'build.py'),'--report-number','240','--verify-only']]
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
