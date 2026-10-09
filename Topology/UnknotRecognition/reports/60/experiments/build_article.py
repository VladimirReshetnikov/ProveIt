#!/usr/bin/env python3
"""Build the article in an isolated temporary directory, then publish outputs.

Requires latexmk, pdflatex, and bibtex. All TeX inputs and figures are shipped.
Capturing process output until completion avoids exposing a partial build log.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


def atomic_bytes(path, contents):
    temporary = path.with_name(path.name + '.new')
    temporary.write_bytes(contents)
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    article = root / 'article'
    with tempfile.TemporaryDirectory(prefix='proveit_article_') as scratch:
        scratch = Path(scratch)
        for pattern in ('*.tex', '*.bib'):
            for source in article.glob(pattern):
                shutil.copy2(source, scratch / source.name)
        shutil.copytree(article / 'figures', scratch / 'figures')
        env = dict(os.environ)
        env['SOURCE_DATE_EPOCH'] = str(int(datetime(2026, 10, 9, tzinfo=timezone.utc).timestamp()))
        env['FORCE_SOURCE_DATE'] = '1'
        command = ['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                   'unknot_research.tex']
        proc = subprocess.run(command, cwd=scratch, env=env,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        final_log = (scratch / 'unknot_research.log').read_text(errors='replace') if (scratch / 'unknot_research.log').exists() else ''
        unresolved = bool(re.search(r'(?:Citation|Reference).*undefined|There were undefined references', final_log))
        overfull = re.findall(r'Overfull \\[hv]box[^\n]*', final_log)
        output = scratch / 'unknot_research.pdf'
        summary = {'command': command, 'returncode': proc.returncode,
                   'unresolved_references': unresolved, 'overfull_boxes': overfull,
                   'source_date_epoch': env['SOURCE_DATE_EPOCH']}
        for name in ('unknot_research.pdf', 'unknot_research.bbl', 'unknot_research.log'):
            source = scratch / name
            if source.exists():
                atomic_bytes(article / name, source.read_bytes())
        atomic_bytes(root / 'results' / 'article_build.log', proc.stdout)
        if output.exists():
            data = output.read_bytes()
            summary.update(pdf_bytes=len(data), pdf_sha256=hashlib.sha256(data).hexdigest())
        (root / 'results' / 'article_build.json').write_text(json.dumps(summary, indent=2) + '\n')
        print(json.dumps(summary))
        if proc.returncode or unresolved:
            raise SystemExit('Article build failed or has unresolved references')


if __name__ == '__main__':
    main()
