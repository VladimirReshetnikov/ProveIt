#!/usr/bin/env python3
"""Regenerate the printed equation data; --check compares without writing.

Uses only Python's standard library.  The residual list is rendered from the
complete balanced 233-variable equation, never from its sparse companion.
The two constant specifications are extracted from their included TeX sources.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def readable_seed(text):
    text = text.replace(r"\fontsize{7.7}{8.2}\selectfont", r"\small")
    # Put the entire alphabet on its own line without changing a digit.
    text = text.replace(
        "The alphabet, in order of digit values $0,\\ldots,61$, is\n",
        "The alphabet, in order of digit values $0,\\ldots,61$, is\\par\n\\noindent\n",
    )
    # Keep the alphabet description and all seed digits together on one page.
    start = text.index(r'\textbf{The integer $\mathcal A$.}')
    end = text.index(r'\endgroup', start) + len(r'\endgroup')
    text = (text[:start] + r'\begin{samepage}' + '\n' + text[start:end]
            + '\n' + r'\end{samepage}' + text[end:])
    return text


def language():
    source = (ROOT / 'compact66/preferred4127/equation.tex').read_text()
    start = source.index(r'\textbf{The 943 indexed fixed tiles.}')
    stop = source.index(r'\normalfont', start)
    text = source[start:stop].replace(r'\textbf{The 943 indexed fixed tiles.}' + '\n', '', 1)
    preamble = (
        r'\providecommand{\fl}[1]{\left\lfloor#1\right\rfloor}' + '\n'
        + r'\providecommand{\rg}[2]{\{#1,\ldots,#2\}}' + '\n'
        + 'Every item in this appendix defines a fixed constant. All index ranges are finite.\n'
    )
    return preamble + readable_seed(text)


def term_tex(coefficient, indices, first):
    sign = '-' if coefficient < 0 else ('' if first else '+')
    magnitude = abs(coefficient)
    scalar = str(magnitude) if magnitude != 1 or not indices else ''
    if len(indices) == 2 and indices[0] == indices[1]:
        monomial = 'x_{' + str(indices[0]) + '}^{2}'
        width = 3 + len(str(indices[0]))
    else:
        monomial = ''.join('x_{' + str(i) + '}' for i in indices)
        width = sum(2 + len(str(i)) for i in indices)
    return sign + scalar + monomial, len(sign) + len(scalar) + width


def residuals():
    equation = json.loads((ROOT / 'direct233/equations/P233_balanced/equation.json').read_text())
    rows = equation['residuals']
    require(equation['domain'] == 'unrestricted integers', 'Printed equation domain')
    require(len(equation['variables']) == 233 and len(rows) == 169, 'Printed equation dimensions')
    lines = [r'\begingroup\footnotesize', r'\setlength{\jot}{1pt}']
    for index, row in enumerate(rows):
        terms = row['terms']
        require(all(isinstance(c, int) and c and len(m) <= 2 for c, m in terms), 'Integral quadratic terms')
        parts, widths = [], []
        for position, (coefficient, monomial) in enumerate(terms):
            text, width = term_tex(coefficient, monomial, position == 0)
            parts.append(text)
            widths.append(width)
        lines.append(r'\[\begin{aligned}')
        prefix = 'r_{' + str(index) + '}={}&'
        current, width = '', 7
        for text, term_width in zip(parts, widths):
            if current and width + term_width > 76:
                lines.append(prefix + current)
                prefix = r'\\ &'
                current, width = '', 0
            current += text
            width += term_width
        lines.append(prefix + current)
        lines.append(r'\end{aligned}\]')
    lines.append(r'\endgroup')
    return '\n'.join(lines) + '\n'


def verify_seed(text):
    marker = r'\begingroup\small\ttfamily'
    block = text.split(marker, 1)[1].split(r'\endgroup', 1)[0]
    printed = ''.join(re.findall(r'([A-Za-z0-9]+)\\par', block))
    tree = ast.parse((ROOT / 'compact66/preferred4127/start_only.py').read_text())
    source_seed = next(ast.literal_eval(node.value) for node in tree.body
                       if isinstance(node, ast.Assign)
                       and any(isinstance(name, ast.Name) and name.id == 'SEED' for name in node.targets))
    require(len(printed) == 436 and printed == source_seed, 'Every printed seed character')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    options = parser.parse_args()
    generated = {
        'appendices/language.tex': language(),
        'appendices/positive85_coefficients.tex': readable_seed(
            (ROOT / 'positive85/inherited/coefficient_recipe.tex').read_text()),
        'appendices/direct233_residuals.tex': residuals(),
    }
    verify_seed(generated['appendices/language.tex'])
    verify_seed(generated['appendices/positive85_coefficients.tex'])
    for filename, content in generated.items():
        target = ROOT / filename
        if options.check:
            require(target.read_bytes() == content.encode(), 'Printed artifact differs: ' + filename)
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content)
    print(json.dumps({'status': 'PASS', 'mode': 'check' if options.check else 'write',
                      'balanced_residuals': 169, 'seed_characters': 436,
                      'sha256': {name: hashlib.sha256(text.encode()).hexdigest()
                                 for name, text in generated.items()}}, indent=2))


if __name__ == '__main__':
    main()
