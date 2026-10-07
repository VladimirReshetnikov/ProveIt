#!/usr/bin/env python3
"""Offline, deterministic, fail-closed builder for the Report197 package.

Normal use: python3 -I -S -B build.py NEW_ABSENT_DESTINATION
Author freeze: python3 -I -S -B build.py --freeze-source
Inspect: python3 -I -S -B build.py --check
A manifest is an integrity record, not a signature or proof of provenance.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
SOURCES = ('Report197.tex','README.txt','build.py','guard_tests.py','verify.py','symbolic_checks.py','data/exact_A373271.txt')
SOURCE_MANIFEST = 'SOURCE_MANIFEST.json'
MANIFEST = 'MANIFEST.json'
GENERATED = ('Report197.pdf','generated/verification.json','generated/exact_terms.txt',
             'generated/guard_results.json','generated/BUILD_INFO.json')
BASENAME = 'Report197'
EPOCH = 1791072000
ZIP_TIME = (2026,10,4,0,0,0)
MAX_FILE = 16*1024*1024
MAX_TOTAL = 32*1024*1024


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2)+'\n').encode('utf-8')


def unique_object(pairs):
    result={}
    for key,value in pairs:
        need(key not in result,'duplicate JSON key: '+key)
        result[key]=value
    return result


def forbidden_number(value):
    raise ValueError('noninteger JSON number: '+value)


def load_json(data):
    return json.loads(data, object_pairs_hook=unique_object,
                      parse_constant=forbidden_number, parse_float=forbidden_number)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_name(name):
    need(type(name) is str and bool(name),'empty or non-string package path')
    need(not any(ord(c)<32 or ord(c)==127 for c in name) and '\\' not in name and ':' not in name,
         'unsafe package path')
    path=PurePosixPath(name)
    need(bool(path.parts) and not path.is_absolute() and path.as_posix()==name and
         all(part not in ('.','..') for part in path.parts),'unsafe package path')
    need(not any(part.startswith('.') or part=='__pycache__' or part.endswith(('.pyc','.pyo'))
                 for part in path.parts),'hidden or cache path refused')
    return path


def check_directory(path):
    path=Path(path).absolute()
    need('..' not in path.parts,'parent traversal in directory path')
    for component in (*reversed(path.parents),path):
        need(stat.S_ISDIR(component.lstat().st_mode),'missing/non-directory/symlink ancestor: '+str(component))
    return path


def read_regular(path, limit=MAX_FILE):
    path=Path(path)
    check_directory(path.parent)
    initial=path.lstat()
    need(stat.S_ISREG(initial.st_mode) and initial.st_size<=limit,'not a bounded regular file: '+str(path))
    flags=os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_NONBLOCK',0)
    with os.fdopen(os.open(path,flags),'rb') as stream:
        opened=os.fstat(stream.fileno())
        need(stat.S_ISREG(opened.st_mode) and opened.st_size<=limit and
             (initial.st_dev,initial.st_ino)==(opened.st_dev,opened.st_ino),'file changed while opening')
        data=stream.read(limit+1)
        need(len(data)==opened.st_size and len(data)<=limit,'file changed or grew while reading')
    return data


def scan(root):
    root=check_directory(root)
    files,dirs={},set()
    def visit(directory):
        with os.scandir(directory) as entries:
            ordered=sorted(entries,key=lambda x:x.name)
        for entry in ordered:
            path=Path(entry.path); name=path.relative_to(root).as_posix()
            safe_name(name)
            mode=entry.stat(follow_symlinks=False).st_mode
            if stat.S_ISDIR(mode):
                dirs.add(name); visit(path)
            else:
                need(stat.S_ISREG(mode),'symlink or special file refused: '+name)
                files[name]=path
    visit(root)
    return files,dirs


def expected_dirs(names):
    return {parent.as_posix() for name in names for parent in PurePosixPath(name).parents
            if parent.as_posix()!='.'}


def digests(root, names):
    result={}
    for name in sorted(names):
        safe_name(name)
        data=read_regular(Path(root)/name)
        result[name]={'bytes':len(data),'sha256':sha(data)}
    need(sum(item['bytes'] for item in result.values())<=MAX_TOTAL,'package exceeds size limit')
    return result


def manifest_document(root,names,kind):
    return {'schema':'report197-'+kind+'-manifest-v1','report':197,'algorithm':'sha256',
            'self_excluded':SOURCE_MANIFEST if kind=='source' else MANIFEST,
            'files':digests(root,names)}


def check_manifest(root,filename,names,kind):
    document=load_json(read_regular(Path(root)/filename,256*1024))
    need(type(document) is dict and set(document)=={'schema','report','algorithm','self_excluded','files'},
         'manifest schema keys differ')
    need(type(document['report']) is int and document['report']==197 and
         document['schema']=='report197-'+kind+'-manifest-v1' and document['algorithm']=='sha256' and
         document['self_excluded']==filename,'manifest identity differs')
    records=document['files']
    need(type(records) is dict and set(records)==set(names),'manifest inventory differs')
    for name,item in records.items():
        safe_name(name)
        need(type(item) is dict and set(item)=={'bytes','sha256'},'invalid manifest record')
        need(type(item['bytes']) is int and 0<=item['bytes']<=MAX_FILE and
             type(item['sha256']) is str and re.fullmatch('[0-9a-f]{64}',item['sha256']) is not None,
             'invalid manifest size or digest')
    need(records==digests(root,names),'manifest size/hash mismatch')
    need(read_regular(Path(root)/filename)==canonical(document),'manifest JSON is not canonical')
    return document


def validate_source(root=ROOT):
    root=check_directory(root)
    files,dirs=scan(root)
    source_set=set(SOURCES)|{SOURCE_MANIFEST}
    release_set=source_set|set(GENERATED)|{MANIFEST}
    need(set(files) in (source_set,release_set),'unlisted/missing package files: '+repr(sorted(set(files)^source_set)))
    need(dirs==expected_dirs(files),'empty/unexpected package directory')
    source_document=check_manifest(root,SOURCE_MANIFEST,SOURCES,'source')
    for name in SOURCES:
        data=read_regular(root/name)
        data.decode('utf-8')
        need(not any(byte<32 and byte not in (9,10) for byte in data),'control byte in source: '+name)
    if set(files)==release_set:
        check_manifest(root,MANIFEST,release_set-{MANIFEST},'complete')
    payload={name:read_regular(root/name) for name in SOURCES+(SOURCE_MANIFEST,)}
    need(payload[SOURCE_MANIFEST]==canonical(source_document),'source manifest changed during read')
    need(all({'bytes':len(payload[name]),'sha256':sha(payload[name])}==source_document['files'][name]
             for name in SOURCES),'source payload changed after manifest validation')
    return payload


def snapshot(root):
    files,dirs=scan(root)
    return {'files':digests(root,files),'directories':sorted(dirs)}


def fresh_output(value,source=ROOT):
    path=Path(value).absolute()
    need('..' not in path.parts,'parent traversal in destination')
    check_directory(path.parent)
    try: path.lstat()
    except FileNotFoundError: pass
    else: raise ValueError('destination already exists (including a symlink): '+str(path))
    source=check_directory(source)
    need(path!=source and source not in path.parents and path not in source.parents,
         'destination overlaps source')
    return path


def write_new(path,data):
    path=Path(path)
    check_directory(path.parent)
    with path.open('xb') as stream: stream.write(data)


def freeze_source(root=ROOT):
    root=check_directory(root)
    files,dirs=scan(root)
    need(set(files)==set(SOURCES) and dirs==expected_dirs(SOURCES),'freeze requires exact source-only inventory and absent manifest')
    write_new(root/SOURCE_MANIFEST,canonical(manifest_document(root,SOURCES,'source')))
    validate_source(root)


def clean_environment(root):
    for name in ('home','tmp','texvar','texconfig','texcache','texhome','fonts'):
        (root/name).mkdir()
    return {'PATH':os.environ.get('PATH',os.defpath),'HOME':str(root/'home'),'TMPDIR':str(root/'tmp'),
            'SOURCE_DATE_EPOCH':str(EPOCH),'FORCE_SOURCE_DATE':'1','TZ':'UTC','LC_ALL':'C.UTF-8',
            'PYTHONHASHSEED':'0','PYTHONDONTWRITEBYTECODE':'1',
            'TEXMFVAR':str(root/'texvar'),'TEXMFCONFIG':str(root/'texconfig'),
            'TEXMFCACHE':str(root/'texcache'),'TEXMFHOME':str(root/'texhome'),'VARTEXFONTS':str(root/'fonts'),
            'openin_any':'p','openout_any':'p','shell_escape':'f'}


def run(command,cwd,env,timeout=3600):
    result=subprocess.run(command,cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout,shell=False)
    need(result.returncode==0,'command failed: '+' '.join(map(str,command))+'\n'+(result.stdout+result.stderr)[-12000:])
    return result.stdout


def prepare_tex(work,env):
    need(shutil.which('pdflatex',path=env['PATH']) and shutil.which('kpsewhich',path=env['PATH']),
         'installed pdflatex and kpsewhich required')
    probe=subprocess.run(['kpsewhich','pdflatex.fmt'],cwd=work,env=env,capture_output=True,text=True,timeout=30)
    if probe.returncode==0 and probe.stdout.strip(): return
    need(shutil.which('pdftex',path=env['PATH']),'installed pdftex required to initialize private format')
    dist=Path(run(['kpsewhich','-var-value=TEXMFDIST'],work,env).strip())
    need(dist.is_dir(),'installed TeX tree missing')
    trees=[dist]
    sibling=dist.parent.parent/'texmf'
    if sibling.is_dir(): trees.append(sibling)
    env['TEXMF']='{'+','.join(map(str,trees))+'}'
    env['TEXFORMATS']=str(work)+os.pathsep
    run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
         '-jobname=pdflatex','pdflatex.ini'],work,env)
    need((work/'pdflatex.fmt').is_file(),'private TeX format not produced')
    maps=[]
    for name in ('cm.map','cmextra.map','latxfont.map','symbols.map','lm.map'):
        path=Path(run(['kpsewhich',name],work,env).strip())
        need(path.is_file(),'installed font map missing: '+name)
        maps.append(path.read_bytes())
    write_new(work/'pdftex.map',b'\n'.join(maps)+b'\n')


def runtime_versions(work,env):
    """Actual stable toolchain identity; intentionally independent of -O mode."""
    tex=run(['pdflatex','--version'],work,env)
    kpathsea=run(['kpsewhich','--version'],work,env)
    return {'python_implementation':sys.implementation.name,
            'python_version':sys.version,
            'python_platform':sys.platform,
            'python_integer_bits_per_digit':sys.int_info.bits_per_digit,
            'pdftex_version':tex.splitlines()[0],
            'pdftex_version_output_sha256':sha(tex.encode('utf-8')),
            'kpathsea_version':kpathsea.splitlines()[0],
            'kpathsea_version_output_sha256':sha(kpathsea.encode('utf-8'))}


def compile_pdf(work,env,source):
    write_new(work/'Report197.tex',source)
    wrapper=b'\\pdfinfoomitdate=1\n\\pdftrailerid{}\n\\pdfsuppressptexinfo=-1\n\\input{Report197.tex}\n'
    write_new(work/'wrapper.tex',wrapper)
    prepare_tex(work,env)
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
             '-file-line-error','-jobname=Report197','wrapper.tex']
    last=None
    for passes in range(1,5):
        run(command,work,env)
        state=tuple((work/('Report197.'+suffix)).read_bytes() if (work/('Report197.'+suffix)).exists() else b''
                    for suffix in ('aux','toc','out'))
        if passes>=2 and state==last: break
        last=state
    else: raise ValueError('TeX auxiliary files did not stabilize within four passes')
    log=(work/'Report197.log').read_text(errors='replace')
    bad=[line for line in log.splitlines() if any(token in line for token in
         ('Overfull','Missing character:','undefined references','undefined citations',
          'Rerun to get cross-references right','Label(s) may have changed','multiply-defined labels'))]
    need(not bad,'TeX defects: '+'; '.join(bad))
    pdf=read_regular(work/'Report197.pdf')
    need(pdf.startswith(b'%PDF-'),'TeX did not produce a PDF')
    return pdf,passes


def archive(package,target):
    target=fresh_output(target,package)
    validate_source(package)
    files,_=scan(package)
    with zipfile.ZipFile(target,'x',compression=zipfile.ZIP_STORED) as zipped:
        for name,path in sorted(files.items()):
            info=zipfile.ZipInfo(name,ZIP_TIME)
            info.create_system=3;info.external_attr=(stat.S_IFREG|0o644)<<16
            info.compress_type=zipfile.ZIP_STORED
            zipped.writestr(info,read_regular(path))


def build(destination,root=ROOT):
    root=check_directory(root)
    output=fresh_output(destination,root)
    before=snapshot(root)
    sources=validate_source(root)
    need(snapshot(root)==before,'source changed during validation')
    with tempfile.TemporaryDirectory(prefix='report197-build-',dir=output.parent) as temporary:
        stage=Path(temporary); package=stage/'package';package.mkdir()
        tex=stage/'tex';tex.mkdir()
        env=clean_environment(stage)
        for name,data in sources.items():
            target=package/name;target.parent.mkdir(parents=True,exist_ok=True);write_new(target,data)
        validate_source(package)
        generated=package/'generated';generated.mkdir()
        checks=[]
        for optimized in (False,True):
            flags=['-I','-S','-B']+(['-O'] if optimized else [])
            checks.append(run([sys.executable,*flags,str(package/'guard_tests.py'),'--unit-only'],stage,env))
        need(checks[0]==checks[1],'normal/-O guard results differ')
        guard=load_json(checks[0]);need(guard.get('status')=='PASS','guard test status failed')
        write_new(generated/'guard_results.json',checks[0].encode('utf-8'))
        flags=['-I','-S','-B']
        command=[sys.executable,*flags,str(package/'verify.py'),'--output',str(stage/'verification.json'),
                 '--terms-output',str(stage/'exact_terms.txt')]
        ordinary=run(command,stage,env)
        optimized=run([sys.executable,'-I','-S','-B','-O',str(package/'verify.py')],stage,env)
        need(ordinary==optimized,'normal/-O verification results differ')
        write_new(generated/'verification.json',read_regular(stage/'verification.json'))
        write_new(generated/'exact_terms.txt',read_regular(stage/'exact_terms.txt'))
        result=load_json(read_regular(generated/'verification.json'))
        need(read_regular(generated/'verification.json')==ordinary.encode('utf-8'),'verification receipt differs from stdout')
        need(result.get('status')=='PASS' and result.get('all2001_recomputed') is True,'verification result differs')
        pdf,passes=compile_pdf(tex,env,sources['Report197.tex'])
        write_new(package/'Report197.pdf',pdf)
        write_new(generated/'BUILD_INFO.json',canonical({'schema':'report197-build-v1','report':197,
            'sequence':'A373271','source_date_epoch':EPOCH,'tex_passes':passes,'shell_escape':False,
            'all2001_recomputed':True,'normal_and_optimized_guards_agree':True,'normal_and_optimized_verification_agree':True,
            'runtime_versions':runtime_versions(tex,env),
            'dependencies':'Python standard library and installed pdfLaTeX stack','network_required':False,
            'reproducibility':'Byte-identical for identical sources and installed Python/TeX stack; no cross-version PDF promise'}))
        package_names=set(SOURCES)|{SOURCE_MANIFEST}|set(GENERATED)
        write_new(package/MANIFEST,canonical(manifest_document(package,package_names,'complete')))
        validate_source(package)
        zipped=stage/'Report197_code.zip';archive(package,zipped)
        need(snapshot(root)==before,'source tree changed during build')
        # mkdir is the exclusive publication boundary. Existing objects are never replaced.
        output.mkdir(exist_ok=False)
        for name,data in {'Report197.tex':sources['Report197.tex'],'Report197.pdf':pdf,
                          'Report197_code.zip':read_regular(zipped,MAX_TOTAL+1024*1024)}.items():
            write_new(output/name,data)
        shutil.copytree(package,output/'package',symlinks=False)
        files,_=scan(output)
        artifact={'schema':'report197-artifacts-v1','report':197,'algorithm':'sha256',
                  'self_excluded':'ARTIFACTS.json','files':digests(output,files)}
        write_new(output/'ARTIFACTS.json',canonical(artifact))
        need(snapshot(root)==before,'source tree changed during publication')
    return {'status':'PASS','report':197,'all2001_recomputed':True,
            'pdf_sha256':sha(pdf),'zip_sha256':sha(read_regular(output/'Report197_code.zip',MAX_TOTAL+1024*1024))}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination',nargs='?')
    parser.add_argument('--freeze-source',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    need(sum((bool(args.destination),args.freeze_source,args.check))==1,'choose one destination, --freeze-source, or --check')
    if args.freeze_source:
        freeze_source();result={'status':'PASS','source_manifest_written':SOURCE_MANIFEST}
    elif args.check:
        validate_source();result={'status':'PASS','source_manifest_verified':True}
    else: result=build(args.destination)
    sys.stdout.buffer.write(canonical(result))


if __name__=='__main__':
    try: main()
    except (OSError,ValueError,subprocess.SubprocessError) as error:
        print('build refused/failed: '+str(error),file=sys.stderr)
        raise SystemExit(2)
