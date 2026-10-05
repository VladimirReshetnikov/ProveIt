#!/usr/bin/env python3
"""Deterministic Report 232 full build with immutable sources and new output only."""
import sys
sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(640)
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import stat
import subprocess
import tempfile
import zipfile

SOURCE = Path(__file__).resolve().parent
SOURCE_FILES = ('README.md','build.py','certificates.py','guard_tests.py',
                'inverse_checks.py','report.tex','fixtures/exact.json','fixtures/inverse.json')
EPOCH = '1791158400'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def snapshot(root):
    result = {}
    for base, directories, files in os.walk(root, followlinks=False):
        for name in directories:
            require(not (Path(base)/name).is_symlink(), 'Source directory symlinks are not permitted')
        for name in files:
            path = Path(base)/name
            require(not path.is_symlink() and path.is_file(), 'Source members must be regular files')
            result[path.relative_to(root).as_posix()] = sha(path.read_bytes())
    return result



def verify_packaged_manifest(initial):
    manifest = SOURCE/'SHA256SUMS'
    require(manifest.is_file() and not manifest.is_symlink(), 'Source manifest is required')
    expected = {}
    for line in manifest.read_text().splitlines():
        require('  ' in line, 'Malformed source manifest')
        checksum, name = line.split('  ',1)
        require(len(checksum)==64 and all(c in '0123456789abcdef' for c in checksum),
                'Malformed manifest digest')
        require(name and not name.startswith('/') and '\\' not in name and
                all(part not in ('','.','..') for part in name.split('/')) and
                name not in expected and name != 'SHA256SUMS', 'Malformed manifest path')
        expected[name] = checksum
    actual = {name:digest for name,digest in initial.items() if name != 'SHA256SUMS'}
    require(actual == expected, 'Packaged source manifest mismatch')


def safe_output(raw):
    require(isinstance(raw,str) and raw.strip() != '', 'A nonempty output path is required')
    output = Path(os.path.abspath(raw))
    # lexists catches dangling links, unlike exists. Check before resolve.
    require(not os.path.lexists(output), 'Output target already exists, including symlinks')
    require(output.parent.is_dir(), 'Output parent must be an existing directory')
    for component in [output.parent, *output.parent.parents]:
        require(not component.is_symlink(), 'Output parent path may not cross a symlink')
    target = output.resolve(strict=False)
    require(target != SOURCE and SOURCE not in target.parents, 'Output must be outside the source tree')
    require(target not in SOURCE.parents, 'Output may not contain the source tree')
    return output


def python_argv(script):
    return [sys.executable, '-B', *(['-O'] if not __debug__ else []), str(SOURCE/script)]


def run(command,cwd,env):
    result = subprocess.run(command,cwd=cwd,env=env,stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,timeout=600,check=False)
    if result.returncode:
        raise RuntimeError('Command failed: '+str(command)+'\n'+
                           result.stdout.decode(errors='replace')[-6000:]+'\n'+
                           result.stderr.decode(errors='replace')[-6000:])
    return result


def deterministic_zip(path,members):
    with zipfile.ZipFile(path,mode='x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
        for name,data in sorted(members.items()):
            item = zipfile.ZipInfo('Report232/'+name,date_time=(2026,10,5,0,0,0))
            item.create_system = 3
            item.external_attr = (stat.S_IFREG | 0o644) << 16
            item.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(item,data,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, help='New directory outside source tree; parent must exist')
    args = parser.parse_args()
    output = safe_output(args.output)
    initial = snapshot(SOURCE)
    verify_packaged_manifest(initial)
    for member in SOURCE_FILES:
        require(member in initial,'Missing packaged source: '+member)
    require(shutil.which('pdflatex') is not None, 'pdfLaTeX is required')
    # Atomic creation prevents overwriting even if the target appears after validation.
    output.mkdir(mode=0o755,exist_ok=False)
    env = dict(os.environ)
    env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONINTMAXSTRDIGITS='640',
               SOURCE_DATE_EPOCH=EPOCH,FORCE_SOURCE_DATE='1',TZ='UTC')
    logs, generated = {}, {}
    try:
        with tempfile.TemporaryDirectory(prefix='report232-build-') as temporary:
            work = Path(temporary)
            if Path('/usr/share/texlive/texmf-dist').exists() and not env.get('TEXMF'):
                env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf,/var/lib/texmf}'
            env['TEXMFVAR'] = str(work/'texmf-var')
            env['TEXMFCONFIG'] = str(work/'texmf-config')
            for checker, fixture in [('certificates.py','exact'),('inverse_checks.py','inverse')]:
                result = run(python_argv(checker),work,env)
                expected = (SOURCE/'fixtures'/f'{fixture}.json').read_bytes()
                require(result.stdout == expected,'Regenerated '+fixture+' fixture differs from packaged expected output')
                generated[fixture] = result.stdout
                logs[fixture] = result.stderr.decode(errors='strict')
            tex = (SOURCE/'report.tex').read_bytes()
            (work/'Report232.tex').write_bytes(tex)
            run(['pdftex','-ini','-etex','-jobname=pdflatex','-progname=pdflatex',
                 '-interaction=nonstopmode','-halt-on-error','pdflatex.ini'],work,env)
            for repeat in range(3):
                run(['pdflatex','-fmt=./pdflatex.fmt','-no-shell-escape','-interaction=nonstopmode',
                     '-halt-on-error','-file-line-error','Report232.tex'],work,env)
            log = (work/'Report232.log').read_text(errors='replace')
            require('Overfull \\hbox' not in log and 'Overfull \\vbox' not in log,'TeX overfull box detected')
            require('undefined references' not in log and 'Label(s) may have changed' not in log,
                    'Unresolved TeX references')
            require('Missing character:' not in log,'Missing font glyph')
            require('undefined citations' not in log,'Unresolved TeX citations')
            pdf = (work/'Report232.pdf').read_bytes()
            require(pdf.startswith(b'%PDF-'),'No valid PDF header')
            (output/'Report232.pdf').write_bytes(pdf)
            (output/'Report232.tex').write_bytes(tex)
            for name,data in generated.items(): (output/(name+'.json')).write_bytes(data)
            (output/'tex-build.log').write_text(log)
            (output/'inverse-checks.log').write_text(logs['inverse'])
            members = {name:(SOURCE/name).read_bytes() for name in SOURCE_FILES}
            members['Report232.pdf'] = pdf
            manifest = ''.join(sha(data)+'  '+name+'\n' for name,data in sorted(members.items()))
            members['SHA256SUMS'] = manifest.encode()
            deterministic_zip(output/'Report232-source.zip',members)
            final = snapshot(SOURCE)
            require(final == initial,'Source member bytes or inventory changed during build')
            hashes = {p.name:sha(p.read_bytes()) for p in sorted(output.iterdir()) if p.is_file()}
            receipt = {'status':'PASS','source_members_unchanged':True,
                       'source_inventory_sha256':sha(json.dumps(initial,sort_keys=True).encode()),
                       'source_member_hashes':initial,'artifact_sha256':hashes,
                       'python':platform.python_version(),'optimization':not __debug__,
                       'sympy':__import__('sympy').__version__,'mpmath':__import__('mpmath').__version__,
                       'decimal_integer_digit_limit':sys.get_int_max_str_digits(),
                       'child_python_bytecode_disabled':True,'source_date_epoch':EPOCH,
                       'checks':['all graph polynomials regenerated by partition inversion',
                                 'exact full B1 and B2','independent permutation moments n4..9',
                                 'independent packing comparisons','camel n9 boundary counterexample',
                                 'exact inverse identities','100-digit finite-model diagnostics',
                                 'three-pass no-shell-escape PDF build','no overfull TeX boxes']}
            (output/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    finally:
        require(snapshot(SOURCE) == initial,'Source changed, including after failure')
    print(json.dumps({'status':'PASS','output':str(output),'pdf_sha256':sha((output/'Report232.pdf').read_bytes()),
                      'zip_sha256':sha((output/'Report232-source.zip').read_bytes())},sort_keys=True))


if __name__ == '__main__':
    main()
