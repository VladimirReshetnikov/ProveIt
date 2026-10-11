#!/usr/bin/env python3
"""Extract the repository-ready core from the standalone article.

Run from any working directory. Does not access or modify GitHub.
"""
from __future__ import annotations
from pathlib import Path
import re

here = Path(__file__).resolve().parent
source = (here.parent / 'article.tex').read_text(encoding='utf-8')
start, end = '% INTEGRATION-BEGIN', '% INTEGRATION-END'
if source.count(start) != 1 or source.count(end) != 1:
    raise ValueError('The article must contain exactly one pair of core markers.')
core = source.split(start, 1)[1].split(end, 1)[0].strip()
if not core or '\\documentclass' in core or '\\begin{document}' in core:
    raise ValueError('Invalid integration region.')
header = ('% Generated from article.tex; regenerate with integration/extract_core.py.\n'
          '% Load beta-crossing-preamble.tex and provide theorem environments.\n'
          '% Mathematical source uses namespace bc:.\n')
(here / '07-beta-crossing-identities.tex').write_text(header + core + '\n', encoding='utf-8')
commands = re.findall(r'^\\newcommand\{\\bc[^\n]+$', source, re.MULTILINE)
if not commands:
    raise ValueError('No helper macros found.')
preamble = ('% Standard parent dependencies: amsmath, amssymb, amsthm, mathtools, bm.\n'
            '% The parent manuscript supplies its theorem/proof environments.\n'
            '\\RequirePackage{bm}\n')
preamble += '\n'.join(line.replace('\\newcommand', '\\providecommand', 1) for line in commands) + '\n'
(here / 'beta-crossing-preamble.tex').write_text(preamble, encoding='utf-8')
bib = source.split('\\begin{thebibliography}{99}', 1)[1].split('\\end{thebibliography}', 1)[0]
bib = bib.replace('\\raggedright', '', 1).strip()
(here / 'beta-crossing-references.tex').write_text('% Merge these entries into the parent bibliography.\n' + bib + '\n', encoding='utf-8')
print('Generated core, helper macros, and bibliography fragment.')
