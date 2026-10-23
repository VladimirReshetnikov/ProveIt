#!/usr/bin/env python3
"""Assemble the standalone TeX source from the editable section files."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent.parent
text = (ROOT / 'sections/report_wrapper.tex').read_text(encoding='utf-8')

def include(match):
    name = match.group(1)
    return '% BEGIN ' + name + '\n' + (ROOT / name).read_text(encoding='utf-8') + '\n% END ' + name + '\n'

text = re.sub(r'\\input\{([^}]+)\}', include, text)
(ROOT / 'con_zfc_synthesis.tex').write_text(text, encoding='utf-8')
print('Assembled con_zfc_synthesis.tex (standalone; no external section inputs).')
