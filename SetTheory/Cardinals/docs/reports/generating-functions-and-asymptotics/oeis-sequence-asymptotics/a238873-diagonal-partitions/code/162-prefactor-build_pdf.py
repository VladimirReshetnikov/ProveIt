#!/usr/bin/env python3
"""Build Report162 in an exclusive clean directory with deterministic metadata."""
import argparse
import os
from pathlib import Path
import re
import resource
import stat
import subprocess
import sys
from release_tools import fresh_directory, regular_bytes, write_member

MAX_GENERATED_BYTES = 16 * 1024 * 1024


def _limit_child_files():
    resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_GENERATED_BYTES, MAX_GENERATED_BYTES))


def _read_generated(directory_fd, name, limit):
    fd = os.open(name, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW, dir_fd=directory_fd)
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
            raise ValueError('Generated file is nonregular or exceeds byte limit: ' + name)
        content = stream.read(limit + 1)
        if len(content) > limit:
            raise ValueError('Generated file exceeds byte limit: ' + name)
        return content


def build(destination):
    source = regular_bytes(Path(__file__).absolute().parent / 'Report162.tex', 1024 * 1024)
    with fresh_directory(destination) as (_, fd):
        pinned = '/proc/self/fd/' + str(fd)
        write_member(fd, 'Report162.tex', source)
        environment = {
            'PATH': os.environ.get('PATH', '/usr/bin:/bin'),
            'LC_ALL': 'C', 'TZ': 'UTC', 'SOURCE_DATE_EPOCH': '1790985600',
            'FORCE_SOURCE_DATE': '1',
            'TEXMF': '{/usr/share/texlive/texmf-dist,/usr/share/texmf}',
            'TEXFORMATS': pinned + '//:',
        }
        for key in ('HOME', 'TEXMFHOME', 'TEXMFVAR', 'TEXMFCONFIG', 'TEXMFCACHE', 'XDG_CACHE_HOME'):
            os.mkdir(key.lower(), 0o700, dir_fd=fd)
            environment[key] = pinned + '/' + key.lower()
        output_fd = os.open('console.txt', os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                            0o600, dir_fd=fd)
        with os.fdopen(output_fd, 'wb') as console:
            common = dict(cwd=pinned, env=environment, pass_fds=(fd,),
                          stdout=console, stderr=subprocess.STDOUT, check=True, timeout=180, preexec_fn=_limit_child_files)
            subprocess.run(['pdftex', '-ini', '-etex', '-no-shell-escape',
                            '-interaction=nonstopmode', '-halt-on-error',
                            '-jobname=pdflatex', 'pdflatex.ini'], **common)
            document = (r'\pdfmapfile{}\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}'
                        r'\pdfmapfile{+symbols.map}\pdfmapfile{+euler.map}\pdfmapfile{+lm.map}\input{Report162.tex}')
            previous = None
            for iteration in range(6):
                subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                                '-halt-on-error', '-file-line-error', document], **common)
                state = tuple(_read_generated(fd, 'Report162.' + suffix, 1024 * 1024)
                              for suffix in ('aux', 'toc', 'out'))
                if iteration and state == previous:
                    break
                previous = state
            else:
                raise RuntimeError('References did not stabilize after six passes')
        log = _read_generated(fd, 'Report162.log', MAX_GENERATED_BYTES).decode('utf-8', errors='replace')
        if re.search(r'\bwarning(?=[:\s(])|overfull|underfull|missing character:', log, re.I):
            raise RuntimeError('Settled TeX log contains a warning or layout defect')
        if not _read_generated(fd, 'Report162.pdf', MAX_GENERATED_BYTES).startswith(b'%PDF-'):
            raise RuntimeError('Invalid PDF output')
    print('Built Report162.pdf with settled, clean references')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args()
    build(args.output_dir)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print('Build failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
