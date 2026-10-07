#!/usr/bin/env python3
"""Build Report195 offline in private temporary storage, then publish exclusively.

Generic filesystem, isolated-TeX and deterministic-ZIP patterns are adapted
from the authored Report194 builder. This report's replay pipeline is separate.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
ROOT=Path(__file__).absolute().parent
sys.path.insert(0,str(ROOT))
import verify_manifest as manifest
import reproduce
SOURCES=manifest.SOURCES
GENERATED=manifest.GENERATED
BASENAME='Report195'
EPOCH=1791072000
ZIP_TIME=(2026,10,4,0,0,0)


def need(condition,message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return reproduce.canonical(value)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_new(path,data):
    with Path(path).open('xb') as stream:
        stream.write(data)


def run(command,cwd,env,timeout=900):
    result=subprocess.run(command,cwd=cwd,env=env,capture_output=True,
                          text=True,timeout=timeout,shell=False)
    need(result.returncode==0,'command failed: '+' '.join(map(str,command))+'\n'+
         (result.stdout+result.stderr)[-12000:])
    return result.stdout

def environment(temp):
    """Fixed metadata, private TeX caches, no inherited TeX/Python overrides."""
    temp = Path(temp)
    for name in ('home', 'tmp', 'texvar', 'texconfig', 'texcache', 'texhome', 'fonts'):
        (temp / name).mkdir()
    env = {
        'PATH': os.environ.get('PATH', os.defpath),
        'HOME': str(temp / 'home'), 'TMPDIR': str(temp / 'tmp'),
        'SOURCE_DATE_EPOCH': str(EPOCH), 'FORCE_SOURCE_DATE': '1',
        'TZ': 'UTC', 'LC_ALL': 'C.UTF-8',
        'PYTHONHASHSEED': '0', 'PYTHONDONTWRITEBYTECODE': '1',
        'TEXMFVAR': str(temp / 'texvar'),
        'TEXMFCONFIG': str(temp / 'texconfig'),
        'TEXMFCACHE': str(temp / 'texcache'),
        'TEXMFHOME': str(temp / 'texhome'),
        'VARTEXFONTS': str(temp / 'fonts'),
        'openin_any': 'p', 'openout_any': 'p', 'shell_escape': 'f',
    }
    if os.name == 'nt' and 'SystemRoot' in os.environ:
        env['SystemRoot'] = os.environ['SystemRoot']
    return env


def prepare_tex(work, env):
    need(shutil.which('pdflatex', path=env['PATH']) and
         shutil.which('kpsewhich', path=env['PATH']),
         'pdflatex and kpsewhich are required')
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], cwd=work, env=env,
                           capture_output=True, text=True, timeout=30, shell=False)
    if probe.returncode == 0 and probe.stdout.strip():
        return
    need(shutil.which('pdftex', path=env['PATH']),
         'pdftex is needed to initialize a local format')
    dist = Path(run(['kpsewhich', '-var-value=TEXMFDIST'], work, env).strip())
    need(dist.is_dir(), 'installed TeX tree not found')
    trees = [dist]
    sibling = dist.parent.parent / 'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{' + ','.join(map(str, trees)) + '}'
    env['TEXFORMATS'] = str(work) + os.pathsep
    run(['pdftex', '-ini', '-etex', '-no-shell-escape',
         '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex',
         'pdflatex.ini'], work, env)
    need((work / 'pdflatex.fmt').is_file(), 'local format was not produced')
    maps = []
    for name in ('cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'lm.map'):
        path = Path(run(['kpsewhich', name], work, env).strip())
        need(path.is_file(), 'installed map not found: ' + name)
        maps.append(path.read_bytes())
    write_new(work / 'pdftex.map', b'\n'.join(maps) + b'\n')


def compile_pdf(work, env):
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', '-jobname=' + BASENAME,
               'Report195.tex']
    states = []
    for passno in range(2):
        run(command, work, env)
        states.append(tuple((work / (BASENAME + '.' + suffix)).read_bytes()
                      if (work / (BASENAME + '.' + suffix)).exists() else b''
                      for suffix in ('aux', 'toc', 'out')))
    need(states[0] == states[1], 'TeX auxiliary files did not stabilize in two passes')
    log = (work / (BASENAME + '.log')).read_text(errors='replace')
    need(not any(message in log for message in
                 ('There were undefined references', 'There were undefined citations',
                  'Rerun to get cross-references right', 'Label(s) may have changed',
                  'There were multiply-defined labels')),
         'unresolved or multiply-defined TeX references')
    defects = [line for line in log.splitlines()
               if re.search(r'\b(?:Overfull|Warning)\b|Missing character:', line, re.I)
               and not (line.startswith('Package: infwarerr ')
                        and 'Providing info/warning/error messages (HO)' in line)]
    need(not defects, 'TeX layout defects: ' + '; '.join(defects))
    data = manifest.read_regular(work / (BASENAME + '.pdf'))
    need(data.startswith(b'%PDF-'), 'invalid PDF')
    return data



def validate_text_payload(name,data):
    need(type(data) is bytes,'source payload must be bytes: '+name)
    data.decode('utf-8')
    need(not any(byte<32 and byte not in (9,10) for byte in data),
         'forbidden C0 control byte in source: '+name)


def validate_source(root):
    root=manifest.check_directory(root)
    files,directories=manifest.scan(root)
    expected=set(SOURCES)
    if manifest.MANIFEST in files:
        manifest.verify(root)
        expected.update(GENERATED)
        expected.add(manifest.MANIFEST)
        if manifest.OPTIONAL[0] in files:
            expected.update(manifest.OPTIONAL)
    need(set(files)==expected,'source inventory mismatch; missing='+
         repr(sorted(expected-set(files)))+'; extra='+repr(sorted(set(files)-expected)))
    expected_dirs={p.as_posix() for name in expected for p in Path(name).parents if p.as_posix()!='.'}
    need(directories==expected_dirs,'empty or unexpected source directory')
    manifest.inventory(root)
    for name in SOURCES:
        validate_text_payload(name,manifest.read_regular(root/name))


def python_guard(root,env,optimized):
    flags=['-I','-S','-B']+(['-O'] if optimized else [])
    raw=run([sys.executable,*flags,str(root/'test_build.py')],root,env)
    result=manifest.load_json(raw)
    need(type(result) is dict and result.get('status')=='PASS','build guards failed')
    return canonical(result)


def collect_replay(directory,result,symbolic):
    files,dirs=manifest.scan(directory)
    names={'RESULT.json','normal/exact_checks.json','normal/exact_terms.txt',
           'optimized/exact_checks.json','optimized/exact_terms.txt'}
    if symbolic:
        names.update(Path(name).name for name in manifest.OPTIONAL)
    need(set(files)==names and dirs=={'normal','optimized'},'replay inventory mismatch')
    need(manifest.read_regular(directory/'RESULT.json')==canonical(result),'replay result mismatch')
    need(result.get('status')=='PASS' and result.get('mandatory_standard_library_only') is True
         and result.get('normal_and_optimized_byte_identical') is True
         and result.get('symbolic_requested') is symbolic and result.get('maximum_n')==1500,
         'replay declaration mismatch')
    payload={}
    for name in ('exact_checks.json','exact_terms.txt'):
        data=manifest.read_regular(directory/'normal'/name)
        need(data==manifest.read_regular(directory/'optimized'/name),'replay normal/-O bytes differ')
        need(result['files'][name]=={'bytes':len(data),'sha256':sha(data)},'replay digest mismatch')
        payload[name]=data
    if symbolic:
        expected={}
        for source_name in manifest.OPTIONAL:
            name=Path(source_name).name
            data=manifest.read_regular(directory/name)
            expected[name]={'bytes':len(data),'sha256':sha(data)}
            payload[name]=data
        need(result['symbolic']=={'files':expected,'normal_and_optimized_byte_identical':True},
             'symbolic receipt mismatch')
    return payload


def archive(package,target):
    target=manifest.fresh_output(target,package)
    manifest.verify(package)
    files,_=manifest.scan(package)
    with zipfile.ZipFile(target,'x',compression=zipfile.ZIP_STORED) as zipped:
        for name,path in sorted(files.items()):
            info=zipfile.ZipInfo(name,ZIP_TIME)
            info.create_system=3
            info.external_attr=(stat.S_IFREG|0o644)<<16
            info.compress_type=zipfile.ZIP_STORED
            zipped.writestr(info,manifest.read_regular(path))


def build(output,symbolic=False):
    output=manifest.fresh_output(output,ROOT)
    validate_source(ROOT)
    before=reproduce.snapshot(ROOT)
    sources={name:manifest.read_regular(ROOT/name) for name in SOURCES}
    with tempfile.TemporaryDirectory(prefix='report195-build-',dir=output.parent) as temporary:
        temp=Path(temporary)
        package,tex=temp/'package',temp/'tex'
        package.mkdir();tex.mkdir()
        env=environment(temp)
        for name,data in sources.items():
            target=package/name
            target.parent.mkdir(parents=True,exist_ok=True)
            write_new(target,data)
        guards=[python_guard(package,env,optimized) for optimized in (False,True)]
        need(guards[0]==guards[1],'normal/-O build guards differ')
        verification=reproduce.run(package,temp/'replay',symbolic)
        payload=collect_replay(temp/'replay',verification,symbolic)
        generated=package/'generated';generated.mkdir()
        for name,data in payload.items():
            write_new(generated/name,data)
        write_new(generated/'verification.json',canonical(verification))
        write_new(generated/'build_guards.json',guards[0])
        prepare_tex(tex,env)
        write_new(tex/'Report195.tex',sources['Report195.tex'])
        pdf=compile_pdf(tex,env)
        write_new(package/'Report195.pdf',pdf)
        write_new(generated/'BUILD_INFO.json',canonical({
            'schema':'report195-build-v1','report':195,'date':'2026-10-04',
            'sequence':'A239950','mandatory_arithmetic':'integer and Fraction only',
            'mandatory_dependencies':'Python standard library; installed pdfLaTeX stack',
            'symbolic_requested':symbolic,'network_required':False,'shell_escape':False,
            'tex_passes':2,'source_date_epoch':EPOCH,'normal_and_optimized_checks_agree':True,
            'reproducibility':'Byte-identical for the same sources and installed Python/TeX stack; no cross-version PDF promise'}))
        write_new(package/manifest.MANIFEST,canonical(manifest.document(package)))
        manifest.verify(package)
        zipped=temp/'Report195_code.zip'
        archive(package,zipped)
        need(reproduce.snapshot(ROOT)==before,'source changed during build')
        # Atomic exclusive directory creation is the publication boundary.
        # A conflicting file, directory or dangling link is never replaced.
        output.mkdir(exist_ok=False)
        artifacts={'Report195.tex':sources['Report195.tex'],'Report195.pdf':pdf,
                   'Report195_code.zip':manifest.read_regular(zipped,manifest.MAX_TOTAL_BYTES+65536)}
        for name,data in artifacts.items():
            write_new(output/name,data)
        rows={name:{'bytes':len(data),'sha256':sha(data)} for name,data in sorted(artifacts.items())}
        write_new(output/'ARTIFACTS.json',canonical({'schema':'report195-artifacts-v1',
                  'report':195,'algorithm':'sha256','files':rows}))
    return {'status':'PASS','artifacts':rows}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path,help='fresh absolute directory outside package; parent must exist')
    parser.add_argument('--symbolic',action='store_true',help='explicitly regenerate optional SymPy verification')
    args=parser.parse_args()
    try:
        sys.stdout.buffer.write(canonical(build(args.output,args.symbolic)))
    except (ValueError,OSError,TypeError,subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    sys.exit(main())
