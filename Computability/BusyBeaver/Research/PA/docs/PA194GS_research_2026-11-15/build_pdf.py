#!/usr/bin/env python3
"""Build the report with existing TeX packages, without network installation.

A normal configured TeX distribution uses pdflatex directly. Minimal images
that contain TeX sources but no format/font map get temporary local versions.
"""
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent


def locate(name):
    run=subprocess.run(['kpsewhich',name],text=True,capture_output=True)
    return run.stdout.strip() if run.returncode==0 else ''


def checked(command,cwd,env=None):
    result=subprocess.run(command,cwd=cwd,env=env,text=True,
                          stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout[-14000:],file=sys.stderr)
        raise SystemExit(result.returncode)
    return result.stdout


def main():
    assert shutil.which('pdflatex') and shutil.which('kpsewhich'), 'A TeX distribution is required'
    checked([sys.executable,'-B',str(ROOT/'generate_report_tables.py')],ROOT)
    with tempfile.TemporaryDirectory(prefix='pa194gs-tex-') as temp:
        work=Path(temp)
        args=['pdflatex','-interaction=nonstopmode','-halt-on-error']
        env=os.environ.copy()
        if not locate('pdflatex.fmt'):
            checked(['pdftex','-ini','-etex','-interaction=nonstopmode',
                     '-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],work)
            args.append('-fmt='+str(work/'pdflatex'))
        if not locate('pdftex.map'):
            maps=[locate(name) for name in
                  ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map')]
            assert all(maps), 'Latin Modern and AMS font maps are required'
            (work/'pdftex.map').write_text('\n'.join(Path(p).read_text() for p in maps))
            env['TEXFONTMAPS']=str(work)+'//:'+env.get('TEXFONTMAPS','')
        for _ in range(3):
            output=checked(args+['report.tex'],ROOT/'report',env)
        assert 'Overfull' not in output, 'Inspect an overfull report box'
        assert 'undefined' not in output.lower(), 'Inspect an undefined report reference'
        print('\n'.join(line for line in output.splitlines()
                        if line.startswith('Output written') or line.startswith('Transcript written')))


if __name__=='__main__':
    main()
