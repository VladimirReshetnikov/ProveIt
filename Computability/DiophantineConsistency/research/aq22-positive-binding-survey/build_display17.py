#!/usr/bin/env python3
"""Generate and check the candidate's base-10 TeX and reproducible PDF."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

if not __debug__:
    raise RuntimeError('optimized Python is not supported')

D = Path(__file__).resolve().parent
ROOT = D.parents[1]
raw = (D / 'candidate17.json').read_bytes()
if hashlib.sha256(raw).hexdigest() != '760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81':
    raise ValueError('candidate pin')
c = json.loads(raw)
old = (ROOT / 'equation.tex').read_text()
start = old.index(r'\textbf{The four fixed integers.}')
end = old.index(r'\endgroup', old.index(r'\textbf{The integer $\mathcal A$')) + len(r'\endgroup')
constants = old[start:end]
if hashlib.sha256(constants.encode()).hexdigest() != 'e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6':
    raise ValueError('fixed-constant block pin')

inputs = ['J', 'F', 'alpha', 'f', 'g', 'T', 'X', 'Y', 'xi', 'eta', 'zeta',
          'upsilon', 'gamma', 'epsilon', 'Z', 'D', 'V']
port_names = ['beta', 'K', 'mu', 'omega']
expected_witnesses = ['J', 'F', 'alpha', 'f', 'i', 'T', 'X', 'Y', 'r', 'eta', 'zeta',
                      'y', 'gamma', 'rankVariable', 'zValueVariable', 'dValueVariable',
                      'vValueVariable']
if c['witnesses'] != expected_witnesses or c['fixed_numerals'] != ['beta', 'K0', 'MC', 'MF']:
    raise ValueError('graph interface')
if len(set(inputs + port_names)) != 21 or len(c['source']) != 99:
    raise ValueError('interface or circuit size')

def letters(n):
    result = ''
    while n:
        n, digit = divmod(n - 1, 26)
        result = chr(ord('A') + digit) + result
    return result

aliases = dict(zip(c['witnesses'] + c['fixed_numerals'], inputs + port_names))
if len({row[0] for row in c['source']}) != 99:
    raise ValueError('duplicate gates')
aliases.update({row[0]: 'h' + letters(i) for i, row in enumerate(c['source'], 1)})
if len(set(aliases.values())) != len(aliases):
    raise ValueError('colliding names')
if aliases[c['output']] != 'hCU' or c['source'][-1][0] != c['output']:
    raise ValueError('output gate')

def operand(x):
    return str(x) if isinstance(x, int) else aliases[x]

rows = [f'{i}. {aliases[name]} = {operand(a)} {op} {operand(b)}' + r'\\'
        for i, (name, op, a, b) in enumerate(c['source'], 1)]
unknowns = (r'\begin{gathered}J,F,\alpha,f,g,T,X,Y,\xi,\eta,\zeta,\upsilon,\gamma,\epsilon,Z,D,V\in\mathbb Z_{>0}.\end{gathered}')
equation = r'\boxed{\texttt{hCU}=0.}'
header = r'''\RequirePackage{fix-cm}
\documentclass[10pt]{article}
\usepackage[letterpaper,margin=.38in]{geometry}
\usepackage{amsmath,amssymb,multicol}
\pdfinfoomitdate=1\pdftrailerid{}
\pagestyle{empty}\setlength{\parindent}{0pt}\setlength{\parskip}{2pt}
\setlength{\columnsep}{13pt}\setlength{\jot}{0pt}
\setlength{\abovedisplayskip}{3pt}\setlength{\belowdisplayskip}{3pt}
\let\bigsum\sum\renewcommand{\sum}{\bigsum\nolimits}
\newcommand{\fl}[1]{\left\lfloor#1\right\rfloor}
\newcommand{\rg}[2]{\{#1,\ldots,#2\}}
\begin{document}
\begin{center}
{\large\bfseries A seventeen-variable candidate equation}\\[-1pt]
{\small Positive integer unknowns; degree 32; a 99-operation evaluator.}
\end{center}\vspace{-8pt}
\begin{multicols}{2}
\fontsize{8.6}{9.1}\selectfont
The only unknowns are the seventeen distinct positive integers
\[
''' + unknowns + r'''
\]
{\raggedright Their ASCII names in the circuit are respectively
\texttt{J, F, alpha, f, g, T, X, Y, xi, eta, zeta, upsilon, gamma, epsilon, Z, D, V}. Each name denotes one unknown.\par}
The four fixed integers are \texttt{beta}, \texttt{K}, \texttt{mu}, and
\texttt{omega}, defined below. The single equation is
\[
''' + equation + r'''
\]
Here \texttt{hCU} is the last gate of the complete circuit on the next page.
Every \texttt{h}-name denotes an integer polynomial abbreviation, not an
additional unknown. All arithmetic in the circuit is over the integers.

'''
footer = r'''
\normalfont\fontsize{7.7}{8.2}\selectfont
The fixed integer $\mathcal A$ above is written in base 10. This is a research
candidate. Exact polynomial calculations certify degree 32 and the
substitution identities. Historical paired Lean runs compiled witness
transport and an intuitionistic PRA equivalence to a translated consistency
sentence. No
minimality claim is made.
\end{multicols}
\clearpage
\begin{center}{\large\bfseries Complete 99-operation circuit}\end{center}
Each line defines one gate. The only inputs are the 17 positive integers and
the four fixed integers on the first page. The final gate \texttt{hCU} is a
sum of 8 squares; setting it to zero is the displayed equation. Gate names
are local abbreviations and are distinct from all input names.
\begin{multicols}{2}
\raggedright\ttfamily\fontsize{8}{9.2}\selectfont
% BEGIN CIRCUIT
'''
tail = r'''
% END CIRCUIT
\end{multicols}
\end{document}
'''
tex = header + constants + footer + '\n'.join(rows) + '\n' + tail

def validate(text):
    if text.count(unknowns) != 1 or text.count(equation) != 1 or text.count(constants) != 1:
        raise ValueError('interface, output equation, or constants changed')
    body = text.split('% BEGIN CIRCUIT\n', 1)[1].split('\n% END CIRCUIT', 1)[0].splitlines()
    if len(body) != 99:
        raise ValueError('circuit length')
    known = set(inputs + port_names)
    for i, (line, source) in enumerate(zip(body, c['source']), 1):
        m = re.fullmatch(r'(\d+)\. ([A-Za-z]+) = ([A-Za-z]+|\d+) ([+*\-]) ([A-Za-z]+|\d+)\\\\', line)
        if not m:
            raise ValueError(('bad gate syntax', i))
        number, target, left, op, right = m.groups()
        original, original_op, a, b = source
        if (int(number), target, left, op, right) != (i, aliases[original], operand(a), original_op, operand(b)):
            raise ValueError(('gate mismatch', i))
        if target in known or any(x not in known and not x.isdecimal() for x in (left, right)):
            raise ValueError(('gate topology', i))
        known.add(target)
    return True

validate(tex)
for changed in [tex.replace(rows[0], rows[0].replace(' * ', ' + '), 1),
                tex.replace(equation, r'\boxed{\texttt{hCT}=0.}', 1),
                tex.replace(unknowns, unknowns.replace('J,F,', 'J,J,', 1), 1),
                tex.replace(constants, constants.replace('2011', '2012', 1), 1),
                tex.replace(rows[20] + '\n', '', 1)]:
    try:
        validate(changed)
    except (ValueError, IndexError):
        pass
    else:
        raise ValueError('mutation not detected')
(D / 'equation32-17.tex').write_text(tex)

with tempfile.TemporaryDirectory(prefix='equation32-17-build-') as tmp:
    products = []
    for name in ('first', 'second'):
        dest = Path(tmp) / name
        dest.mkdir()
        subprocess.run(['pdflatex', '-halt-on-error', '-interaction=batchmode',
                        '-output-directory', str(dest), 'equation32-17.tex'],
                       cwd=D, check=True, stdout=subprocess.DEVNULL)
        log = (dest / 'equation32-17.log').read_text(errors='replace')
        if re.search(r'overfull|underfull|warning', log, re.I):
            raise ValueError('TeX layout or font warning')
        products.append((dest / 'equation32-17.pdf').read_bytes())
    if products[0] != products[1]:
        raise ValueError('PDF builds differ')
    (D / 'equation32-17.pdf').write_bytes(products[0])
    print('PASS: 17 distinct inputs, 99 exact gates, five mutation controls,')
    print('two warning-free identical PDF builds; SHA-256', hashlib.sha256(products[0]).hexdigest())
