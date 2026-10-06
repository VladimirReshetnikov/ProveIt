#!/usr/bin/env python3
"""Build Report175 offline in isolated temporary storage; never replace an output."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parent
EPOCH = 1790985600
ZIP_TIME = (2026, 10, 3, 0, 0, 0)
# Explicit source inventory: unrelated files, third-party PDFs, and caches cannot leak in.
SOURCES = (
    'report.tex', 'README.md', 'SOURCES.md', 'build.py', 'test_build.py',
    'verify_manifest.py', 'verify.py', 'guard_tests.py', 'data/certificates.json',
    'regenerate.py', 'README_CODE.md', 'data/verified_results.json', 'data/guard_results.json',
    'data/default_results.json', 'data/regeneration_results.txt',
)

class BuildError(RuntimeError):
    pass


def need(condition, message):
    if not condition:
        raise BuildError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True)+'\n').encode()


def write_new(path, data):
    with Path(path).open('xb') as stream:
        stream.write(data)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_source(name, root=ROOT):
    rel = Path(name)
    need(name and '\x00' not in name and '\\' not in name and not rel.is_absolute()
         and '..' not in rel.parts and rel.as_posix() == name, 'unsafe source path')
    for i in range(1, len(rel.parts)+1):
        need(not (root.joinpath(*rel.parts[:i])).is_symlink(), 'source symlink: '+name)
    path = root / rel
    need(path.is_file(), 'missing regular source: '+name)
    return path


def inventory(root):
    result = {}
    for path in sorted(root.rglob('*')):
        need(not path.is_symlink(), 'package symlink')
        need(path.is_dir() or path.is_file(), 'nonregular package entry')
        if path.is_file() and path.name != 'SHA256SUMS.json':
            result[path.relative_to(root).as_posix()] = sha(path.read_bytes())
    return result


def run(command, cwd, env, timeout=300):
    p = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    need(p.returncode == 0, 'command failed: '+' '.join(map(str,command))+'\n'+(p.stdout+p.stderr)[-12000:])
    return p.stdout


def environment(temp):
    env = {k:v for k,v in os.environ.items() if not k.startswith('TEX') and k not in ('PDFTEX','BIBINPUTS','BSTINPUTS')}
    env.update(SOURCE_DATE_EPOCH=str(EPOCH), FORCE_SOURCE_DATE='1', TZ='UTC',
               LC_ALL='C.UTF-8', PYTHONHASHSEED='0', PYTHONDONTWRITEBYTECODE='1',
               TEXMFVAR=str(temp/'texvar'), TEXMFCONFIG=str(temp/'texconfig'),
               TEXMFCACHE=str(temp/'texcache'))
    return env


def prepare_tex(work, env):
    need(shutil.which('pdflatex') and shutil.which('kpsewhich'), 'pdflatex and kpsewhich are required')
    p = subprocess.run(['kpsewhich','pdflatex.fmt'], env=env, capture_output=True, text=True)
    if p.returncode == 0 and p.stdout.strip():
        return
    need(shutil.which('pdftex'), 'pdftex is needed to initialize a local format')
    dist = Path(run(['kpsewhich','-var-value=TEXMFDIST'],work,env).strip())
    need(dist.is_dir(), 'installed TeX tree not found')
    trees = [dist]
    sibling = dist.parent.parent/'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{'+','.join(map(str,trees))+'}'
    env['TEXFORMATS'] = str(work)+os.pathsep
    run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
         '-halt-on-error','-jobname=pdflatex','pdflatex.ini'],work,env)
    need((work/'pdflatex.fmt').is_file(), 'local format was not produced')
    maps = []
    for name in ('cm.map','cmextra.map','latxfont.map','symbols.map','lm.map'):
        path = Path(run(['kpsewhich',name],work,env).strip())
        need(path.is_file(), 'installed map not found: '+name)
        maps.append(path.read_bytes())
    write_new(work/'pdftex.map',b'\n'.join(maps)+b'\n')


def compile_pdf(work, env):
    command = ['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
               '-file-line-error','-jobname=Report175','report.tex']
    old = None
    for passno in range(6):
        run(command,work,env)
        state = tuple((work/('Report175.'+s)).read_bytes() if (work/('Report175.'+s)).exists() else b''
                      for s in ('aux','toc','out'))
        if passno and state == old:
            break
        old = state
    else:
        raise BuildError('TeX auxiliary files did not stabilize')
    log = (work/'Report175.log').read_text(errors='replace')
    need(not any(x in log for x in ('There were undefined references','There were undefined citations',
                                   'Rerun to get cross-references right')), 'unresolved TeX references')
    defects = re.findall(r'(?:Overfull[^\n]*|Missing character:[^\n]*)',log,re.I)
    need(not defects, 'TeX layout defects: '+'; '.join(defects))
    data = (work/'Report175.pdf').read_bytes()
    need(data.startswith(b'%PDF-'), 'invalid PDF')
    return data


def run_python(package, script, args, env, optimized=False):
    flags = ['-I','-B']+(['-O'] if optimized else [])
    bootstrap = ('import runpy,sys; root=sys.argv.pop(1); script=sys.argv.pop(1); '
                 'sys.path.insert(0,root); sys.argv[0]=root+"/"+script; '
                 'runpy.run_path(sys.argv[0],run_name="__main__")')
    return json.loads(run([sys.executable,*flags,'-c',bootstrap,str(package),script,*args],package,env,900))


def archive(package, target):
    with zipfile.ZipFile(target,'x',compression=zipfile.ZIP_STORED) as zf:
        for path in sorted(package.rglob('*')):
            need(not path.is_symlink(), 'archive symlink')
            if not path.is_file():
                continue
            info = zipfile.ZipInfo(path.relative_to(package).as_posix(), ZIP_TIME)
            info.create_system = 3
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_STORED
            zf.writestr(info,path.read_bytes())


def build(output, extended=False):
    output = Path(output).absolute()
    need(not os.path.lexists(output), 'refusing existing output directory: '+str(output))
    need(output.parent.is_dir(), 'output parent must exist')
    need(len(SOURCES)==len(set(SOURCES)), 'duplicate source path')
    sources = {name:safe_source(name).read_bytes() for name in SOURCES}
    with tempfile.TemporaryDirectory(prefix='report175-build-',dir=output.parent) as tmp:
        temp = Path(tmp); package=temp/'package'; tex=temp/'tex'; package.mkdir();tex.mkdir()
        env = environment(temp)
        for name,data in sources.items():
            dst = package/name; dst.parent.mkdir(parents=True,exist_ok=True); write_new(dst,data)
        generated = package/'generated'; generated.mkdir()
        args = ['--extended'] if extended else []
        runs = [run_python(package,'verify.py',args,env,opt) for opt in (False,True)]
        need(runs[0] == runs[1], 'ordinary and optimized mathematical results differ')
        write_new(generated/'verification.json',canonical(runs[0]))
        guards = [run_python(package,'guard_tests.py',args,env,opt) for opt in (False,True)]
        need(guards[0] == guards[1], 'ordinary and optimized corruption guards differ')
        write_new(generated/'verification_guards.json',canonical(guards[0]))
        buildtests = [run_python(package,'test_build.py',[],env,opt) for opt in (False,True)]
        need(buildtests[0] == buildtests[1], 'ordinary and optimized build guards differ')
        write_new(generated/'build_guards.json',canonical(buildtests[0]))
        prepare_tex(tex,env); write_new(tex/'report.tex',sources['report.tex'])
        pdf = compile_pdf(tex,env); write_new(package/'Report175.pdf',pdf)
        write_new(generated/'BUILD_INFO.json',canonical({
            'report':175,'date':'2026-10-03','extended':extended,
            'normal_and_optimized_agree':True,'network_required':False,'shell_escape':False,
            'source_date_epoch':EPOCH,
            'reproducibility':'Byte-identical with the same source and installed Python/TeX stack; no cross-version PDF identity is promised.'}))
        write_new(package/'SHA256SUMS.json',canonical(inventory(package)))
        receipt=run_python(package,'verify_manifest.py',[],env)
        need(receipt.get('status')=='PASS','manifest verification failed')
        zipped=temp/'Report175.zip';archive(package,zipped)
        # Reserve the final directory only after every expensive check succeeds.
        # mkdir is exclusive: a racing existing output is never replaced.
        output.mkdir(exist_ok=False)
        for name,data in [('Report175.pdf',pdf),('Report175.tex',sources['report.tex']),
                          ('Report175.zip',zipped.read_bytes())]:
            write_new(output/name,data)
        result={p.name:{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in sorted(output.iterdir())}
        write_new(output/'ARTIFACTS.json',canonical(result))
    return {'status':'PASS','artifacts':result}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path,help='new output directory; parent must already exist')
    parser.add_argument('--extended',action='store_true',help='run exact checks through h=6 rather than h=4')
    args=parser.parse_args()
    try:
        print(json.dumps(build(args.output,args.extended),sort_keys=True,indent=2))
    except (BuildError,OSError,subprocess.TimeoutExpired) as exc:
        print('Build failed: '+str(exc),file=sys.stderr);sys.exit(1)

if __name__=='__main__':
    main()
