#!/usr/bin/env python3
"""Create a standalone decimal 12-variable display draft in a fresh directory.

The graph/source/payload connections are external checks, not Lean file
theorems. The maintained root equation.tex/pdf are never modified.
"""
import argparse
from hashlib import sha256
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[2]
ROOT = DC.parents[1]
BRIDGE = DC / 'research/ordinary12-ipra-bridge'
GRAPH = DC / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'
PAYLOAD = DC / 'candidates/free-j-polarized-positive/source/positive/coefficients/payloads'
PINS = {
    GRAPH: '2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22',
    BRIDGE/'compact44-943-table-prototype/Compact943Data.lean': '10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
    BRIDGE/'compact44-coefficient-mass-prototype/CompactCoefficientMass.lean': 'ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e',
    BRIDGE/'compact44-symbolic-kernel-param-prototype/CompactSymbolicKernelOpaque.lean': 'fbef8642de957bb39493607cb67edda418f53332af5a92ee594a2a437241e0b8',
    BRIDGE/'compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean': 'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',
    BRIDGE/'compact44-high-population-prototype/CompactHighPopulation.lean': 'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d',
    BRIDGE/'compact44-concrete-mask-prototype/CompactConcreteMask.lean': '7f3c735747e88ecf1dfbf9d6b759a578ec768a857d3d553c06e8656d7be76ece',
    BRIDGE/'compact44-list-mask-prototype/CompactListMask.lean': '34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b',
    BRIDGE/'compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean': '0c2f2859c5420b3d22b73c3e5e72a7307a75d2b83d95d29eb7691f085d812148',
    PAYLOAD/'beta.bin.gz': '466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c',
    PAYLOAD/'K.bin.gz': 'b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a',
    PAYLOAD/'MC.bin.gz': '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
    PAYLOAD/'MF_source.bin.gz': '935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c5e3b',
}


def need(condition, message):
    if not condition: raise RuntimeError(message)


def digest(data): return sha256(data).hexdigest()


parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
out = args.output.resolve()
need(out.parent == HERE and not out.exists(), 'output must be a new direct child of this draft directory')
inputs = {p: p.read_bytes() for p in PINS}
for p, expected in PINS.items(): need(digest(inputs[p]) == expected, ('input pin mismatch', str(p)))
graph = json.loads(inputs[GRAPH])
need(graph['witnesses'] == ['J','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma'] and
     graph['fixed_numerals'] == ['beta','K0','MC','MF'] and graph['operations'] == 95 and
     graph['output'] == 'P12' and len(graph['source']) == 95, 'unexpected graph metadata')

data = inputs[BRIDGE/'compact44-943-table-prototype/Compact943Data.lean'].decode()
data = data.split('-- BEGIN PINNED ORDERED ROWS', 1)[1].split('-- END PINNED ORDERED ROWS', 1)[0]
rows = [tuple(map(int, x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)', data)]
need(len(rows) == 943 and all(w < 256 and n < 512 and p < 256 and s < 512
                              for w,n,p,s in rows), 'bad pinned row table')
selectors = [1 + 1024*(2**41 - (w + 256*n + 2**17*p + 2**25*s + 127*2**34))
             for w,n,p,s in rows]
need(all(0 < n < 10**14 for n in selectors), 'selector width or sign')
slots_source = inputs[BRIDGE/'compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'].decode()
slot_text = slots_source.split('def slots : List ℕ := [', 1)[1].split(']', 1)[0]
slots = [int(x.strip()) for x in slot_text.split(',')]
need(len(slots) == 41 and all(0 <= x < 4393 for x in slots), 'bad pinned slot list')

# Compute the exact displayed constants and compare their entire retained raw
# little-endian payloads, not merely their digests or a sample of positions.
rho = 2**67
beta = rho**8807 - 1
support = (set(range(943)) | set(range(983,993)) | set(range(1003,1012)) |
           set(range(1013,1032)) | {1063,1064,1095,2195,3296}) - {1}
mc = beta - sum(rho**x for x in support) - 2*rho**1063
high = (4 + sum(rho**u for u in range(1013,1023)) + sum(rho**u for u in range(1065,1074)) +
        rho**2195 + rho**3296 + (2**51-2)*(rho**4393+rho**5495) +
        (2**65-1)*sum(rho**u for u in range(8792,8805)) + (2**19-1)*rho**8805)
mf = beta + high
kernel = (rho**30 + rho**62 + rho**1100 + rho**2201 + rho**8849 +
          sum(x*(rho**(4393-i)+rho**(5495-i)) for i,x in enumerate(selectors)) +
          sum(2**(10+i)*(rho**(4393-x)+rho**(5495-x)) for i,x in enumerate(slots)))
coefficients = [('beta', beta), ('K', kernel), ('MC', mc), ('MF_source', mf)]
raw_hashes = {}
for name, value in coefficients:
    raw = gzip.decompress(inputs[PAYLOAD/f'{name}.bin.gz'])
    need(value >= 0 and value.to_bytes(len(raw), 'little') == raw, ('coefficient payload mismatch', name))
    raw_hashes[name] = digest(raw)

# The only unknowns receive twelve different plain names. Registers are
# explicitly marked as abbreviations, and every input reference is resolved
# before its use to prevent accidental new free variables.
witnesses = dict(zip(graph['witnesses'], list('abcdefghijk') + [r'\ell']))
fixed = {'beta': r'\beta', 'K0': r'\kappa', 'MC': r'\mu', 'MF': r'\nu'}
references = dict(witnesses); references.update(fixed)
lines = []
for index, row in enumerate(graph['source'], 1):
    need(len(row) == 4 and row[1] in ('+', '-', '*') and row[0] not in references,
         ('invalid row', index))
    name, op, left, right = row
    def operand(x):
        if type(x) is int:
            need(x >= 0, ('negative numeric literal', index)); return str(x)
        need(isinstance(x, str) and x in references, ('forward or unknown reference', index, x))
        return references[x]
    lhs = r'\mathtt{r%02d}' % index
    operator = r'\cdot' if op == '*' else op
    lines.append(r'\(' + lhs + ' = ' + operand(left) + ' ' + operator + ' ' + operand(right) + r'\)\\')
    references[name] = lhs
need(references[graph['output']] == r'\mathtt{r95}', 'unexpected output register')
selector_lines = [' '.join(f'{x:014d}' for x in selectors[i:i+7])
                  for i in range(0, len(selectors), 7)]
slot_lines = ','.join(map(str, slots))

tex = r'''\documentclass[9pt]{article}
\usepackage[letterpaper,margin=.42in]{geometry}
\usepackage{amsmath,amssymb,multicol}
\pdfinfoomitdate=1\pdftrailerid{}
\pagestyle{empty}\setlength{\parindent}{0pt}\setlength{\parskip}{2pt}
\setlength{\columnsep}{20pt}\setlength{\jot}{1pt}
\begin{document}
\begin{center}
{\large\bfseries A twelve-variable Diophantine candidate}\\
{\small Strictly positive integer unknowns; 95 evaluator operations.}
\end{center}
The only unknowns are \(a,b,c,d,e,f,g,h,i,j,k,\ell\in\mathbb Z_{>0}\).
Each \(\mathtt{r01},\ldots,\mathtt{r95}\) below is an abbreviation,
not an additional unknown. Evaluate the rows in order. The equation is
\(\boxed{\mathtt{r95}=0}\).

\begin{multicols}{2}\small
% BEGIN GRAPH ROWS
''' + '\n'.join(lines[:48]) + r'''
\columnbreak
''' + '\n'.join(lines[48:]) + r'''
% END GRAPH ROWS
\end{multicols}
\clearpage
\textbf{The four fixed integers.} All indices in the following formulas are
locally bound indices for constants, not unknowns. Set \(\rho=2^{67}\) and
\(\beta=\rho^{8807}-1\). Let the fixed set and ordered list be
\[
\begin{aligned}
\mathcal S={}&\bigl(\{0,\ldots,942\}\cup\{983,\ldots,992\}\cup
\{1003,\ldots,1011\}\cup\{1013,\ldots,1031\}\\
&\quad\cup\{1063,1064,1095,2195,3296\}\bigr)\setminus\{1\},\\
\lambda={}&(''' + slot_lines + r''').
\end{aligned}
\]
The list \(\lambda\) has 41 entries, numbered from zero. The fixed list
\(\sigma\) has 943 entries, also numbered from zero, and is printed in
decimal on the following pages. Then
\[
\begin{aligned}
\mu={}&\beta-\sum_{u\in\mathcal S}\rho^u-2\rho^{1063},\\
\nu={}&\beta+4+\sum_{u=1013}^{1022}\rho^u+\sum_{u=1065}^{1073}\rho^u
 +\rho^{2195}+\rho^{3296}\\
&+(2^{51}-2)(\rho^{4393}+\rho^{5495})
 +(2^{65}-1)\sum_{u=8792}^{8804}\rho^u+(2^{19}-1)\rho^{8805},\\
\kappa={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}+\rho^{8849}\\
&+\sum_{u=0}^{942}\sigma_u(\rho^{4393-u}+\rho^{5495-u})
 +\sum_{u=0}^{40}2^{10+u}(\rho^{4393-\lambda_u}+\rho^{5495-\lambda_u}).
\end{aligned}
\]
\textbf{Decimal selector list.} Read from left to right, top to bottom;
each 14-digit block is one decimal integer. Leading zeroes do not change its
value. There are exactly 943 blocks.
% BEGIN SELECTORS
\begin{verbatim}
''' + '\n'.join(selector_lines) + r'''
\end{verbatim}
% END SELECTORS
\end{document}
'''
need(len(re.findall(r'\\mathtt\{r\d\d\} =', tex)) == 95, 'rendered graph row count')
need(len(re.findall(r'\b\d{14}\b', tex.split('% BEGIN SELECTORS')[1].split('% END SELECTORS')[0])) == 943,
     'rendered selector count')

for p, old in inputs.items(): need(p.read_bytes() == old, ('input changed during generation', str(p)))
out.mkdir()
(out/'equation.tex').write_text(tex)
environment = dict(os.environ, SOURCE_DATE_EPOCH='0', FORCE_SOURCE_DATE='1', TZ='UTC')
run = subprocess.run(['pdflatex', '-halt-on-error', '-interaction=nonstopmode', '-file-line-error',
                      '-output-directory', str(out), str(out/'equation.tex')], cwd=out,
                     env=environment, capture_output=True, text=True, timeout=180)
(out/'pdflatex.stdout').write_text(run.stdout); (out/'pdflatex.stderr').write_text(run.stderr)
need(run.returncode == 0 and (out/'equation.pdf').is_file(), ('pdflatex failed', run.returncode))
need(all(p.read_bytes() == old for p, old in inputs.items()), 'input changed during build')
info = {'status': 'EXTERNAL_DISPLAY_DRAFT_ONLY', 'graph_rows': len(lines), 'selectors': len(selectors),
        'slot_count': len(slots), 'raw_coefficient_sha256': raw_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): digest(v) for p,v in inputs.items()},
        'tex_sha256': digest((out/'equation.tex').read_bytes()), 'pdf_sha256': digest((out/'equation.pdf').read_bytes()),
        'pdflatex_exit_code': run.returncode, 'scope': 'externally generated transcription, not a Lean PDF/file theorem'}
(out/'RESULT.json').write_text(json.dumps(info, indent=2, sort_keys=True)+'\n')
print(json.dumps(info, indent=2, sort_keys=True))
