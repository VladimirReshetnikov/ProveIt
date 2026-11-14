#!/usr/bin/env python3
"""Compile unchanged TeX using installed Debian TeX Live packages.

Use normal pdflatex when the installation works. This optional fallback is
for an installation with dangling generated-file/index links. It creates a
private configuration, English language setup, font map, and pdflatex format.
The default cache is a temporary directory outside this deliverable and is
removed on exit. --cache-dir permits explicitly retaining an external cache.
No system files or report TeX sources are changed. Python's standard library,
pdftex/pdflatex, and the installed report packages/fonts are required.
"""
from pathlib import Path
import argparse,contextlib,os,shutil,subprocess,tempfile

DIST=Path('/usr/share/texlive/texmf-dist')
DEBIAN=Path('/usr/share/texmf')

def run(args,cwd,env,log):
    with log.open('w') as f:
        p=subprocess.run(args,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT)
    if p.returncode:
        print(log.read_text(errors='replace')[-12000:])
        raise SystemExit(p.returncode)
    print(f'PASS: {log.name}')

def build(report,cache):
    local=cache/'texmf';config=cache/'config';web=local/'web2c/pdftex'
    for d in [local,config,web,local/'tex/generic/config',local/'fonts/map/pdftex/local']:
        d.mkdir(parents=True,exist_ok=True)
    (config/'texmf.cnf').write_text(
        f'TEXMF = {{{local},/etc/texmf,{DEBIAN},{DIST}}}\n'
        f'TEXMFVAR = {local}\nTEXMFCONFIG = {config}\n'
        f'TEXMFDBS = {local}\n')
    shutil.copyfile(DIST/'tex/generic/config/language.us',local/'tex/generic/config/language.dat')
    maps=[DEBIAN/'fonts/map/dvips/lm/lm.map']
    maps+=sorted((DIST/'fonts/map/dvips/amsfonts').glob('*.map'))
    (local/'fonts/map/pdftex/local/pdftex.map').write_text('\n'.join(p.read_text() for p in maps))
    env=os.environ.copy()
    env['TEXMFCNF']=f'{config}:/etc/texmf/web2c:{DIST}/web2c'
    if not (web/'pdflatex.fmt').exists():
        run(['pdftex','-ini','-etex','-progname=pdflatex','-jobname=pdflatex',
             '-interaction=nonstopmode','-halt-on-error','pdflatex.ini'],web,env,cache/'format-build.log')
    for i in range(1,3):
        run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error',report.name],
            report.parent,env,cache/f'latex-pass{i}.log')
    print(f'PDF: {report.with_suffix(".pdf")}')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',nargs='?',type=Path,
                    default=Path(__file__).resolve().parents[1]/'report.tex')
    ap.add_argument('--cache-dir',type=Path,
                    help='Optional external cache directory; default is disposable temporary storage.')
    args=ap.parse_args();report=args.source.resolve()
    if not report.is_file():ap.error(f'Source does not exist: {report}')
    if args.cache_dir:
        cache=args.cache_dir.resolve()
        if report.parent==cache or report.parent in cache.parents:
            ap.error('Choose a cache directory outside the deliverable.')
        build(report,cache)
    else:
        with tempfile.TemporaryDirectory(prefix='pa-report-tex-') as td:
            build(report,Path(td))

if __name__=='__main__':main()
