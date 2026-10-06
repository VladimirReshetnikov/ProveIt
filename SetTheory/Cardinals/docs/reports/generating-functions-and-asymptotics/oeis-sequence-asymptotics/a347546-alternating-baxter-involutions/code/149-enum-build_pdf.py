#!/usr/bin/env python3
"""Build Report149.pdf in a fresh pinned directory with deterministic metadata."""
import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
from release_tools import fresh_directory, regular_bytes, write_member


def run(output):
    root = Path(__file__).absolute().parent
    tex = regular_bytes(root / 'Report149.tex')
    with fresh_directory(output) as (_, descriptor):
        work = '/proc/self/fd/' + str(descriptor)
        write_member(descriptor, 'Report149.tex', tex)
        environment = {'PATH': os.environ.get('PATH', '/usr/bin:/bin'),
                       'LC_ALL': 'C', 'TZ': 'UTC',
                       'SOURCE_DATE_EPOCH': '1790985600', 'FORCE_SOURCE_DATE': '1',
                       'TEXMF': '{/usr/share/texlive/texmf-dist,/usr/share/texmf}',
                       'TEXFORMATS': work + '//:'}
        for variable in ('HOME', 'TEXMFHOME', 'TEXMFVAR', 'TEXMFCONFIG', 'TEXMFCACHE', 'XDG_CACHE_HOME'):
            os.mkdir(variable.lower(), mode=0o700, dir_fd=descriptor)
            environment[variable] = work + '/' + variable.lower()
        build_log = os.open('console.txt', os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                            0o600, dir_fd=descriptor)
        with os.fdopen(build_log, 'wb') as console:
            common = dict(cwd=work, env=environment, pass_fds=(descriptor,),
                          stdout=console, stderr=subprocess.STDOUT, check=True)
            subprocess.run(['pdftex', '-ini', '-etex', '-no-shell-escape',
                            '-interaction=nonstopmode', '-halt-on-error',
                            '-jobname=pdflatex', 'pdflatex.ini'], **common)
            document = r'\pdfmapfile{}\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report149.tex}'
            previous = None
            for attempt in range(6):
                subprocess.run(['pdflatex', '-no-shell-escape', '-halt-on-error',
                                '-interaction=nonstopmode', '-file-line-error', document], **common)
                with open(work + '/Report149.aux', 'rb') as aux:
                    state = aux.read()
                if attempt > 0 and state == previous:
                    break
                previous = state
            else:
                raise RuntimeError('TeX references did not stabilize')
        with open(work + '/Report149.log', encoding='utf-8', errors='replace') as log:
            settled = log.read()
        if re.search(r'\bwarning(?=[:\s(])|overfull|underfull|missing character:', settled, re.I):
            raise RuntimeError('Settled TeX log has a warning or layout defect')
        with open(work + '/Report149.pdf', 'rb') as pdf:
            if not pdf.read(5) == b'%PDF-':
                raise RuntimeError('Missing or invalid PDF')
    print('Built Report149.pdf successfully')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    run(args.output_dir)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as problem:
        print('PDF build failed: ' + str(problem), file=sys.stderr)
        sys.exit(1)
