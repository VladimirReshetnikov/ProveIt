#!/usr/bin/env python3
"""Rebuild the staged TeX/PDF twice and reject PDF layout warnings."""
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile

D = Path(__file__).resolve().parent
subprocess.run(['python3', str(D/'generate_equation8_26.py')], check=True)
subprocess.run(['python3', str(D/'verify_display8_26.py')], check=True)
with tempfile.TemporaryDirectory(prefix='equation8-26-build-') as tmp:
    products = []
    for name in ('first', 'second'):
        dest = Path(tmp)/name
        dest.mkdir()
        subprocess.run(['pdflatex', '-halt-on-error', '-interaction=batchmode',
                        '-output-directory', str(dest), 'equation8-26.tex'],
                       cwd=D, check=True, stdout=subprocess.DEVNULL)
        log = (dest/'equation8-26.log').read_text(errors='replace')
        if re.search(r'overfull|underfull|warning', log, re.I):
            raise ValueError('TeX layout or font warning')
        products.append((dest/'equation8-26.pdf').read_bytes())
    if products[0] != products[1]:
        raise ValueError('PDF builds differ')
    (D/'equation8-26.pdf').write_bytes(products[0])
    print('PASS: two warning-free PDF builds match; SHA-256', hashlib.sha256(products[0]).hexdigest())
