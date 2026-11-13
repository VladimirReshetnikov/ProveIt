#!/usr/bin/env python3
"""Check the 84-operation 2011 TeX display against the symbolic graph.

Uses exact sparse polynomials at named cuts; the TeX parser handles only this
arithmetic subset. It does not formalize TeX/PDF semantics or the fixed-port
recipe's interpretation.
"""
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')
HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
TEX = BASE / 'equation84-2011.tex'
OLD = BASE / 'equation.tex'
GRAPH = BASE / 'research/thirteen-first-norm-correction92/polynomial.json'
PARSER = BASE / 'research/adaptive-direct-ordinate86/verify_display_tex86.py'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

if sha(GRAPH) != 'a214fc19ea776e4e3880e13a7cd92260e76e71588c8c6b391669007a180ab3be':
    raise ValueError('84-row source drift')
graph = json.loads(GRAPH.read_text())
rows = graph['source']
if len(rows) != 84 or graph['output'] != 'polynomial':
    raise ValueError('unexpected graph length or output')
node = {row[0]: row[1:] for row in rows}
if len(node) != 84:
    raise ValueError('duplicate graph names')

# Reuse only the established small parser and sparse-ring class, without
# executing the other display's checks or expanding this full polynomial.
syntax = ast.parse(PARSER.read_text(), filename=str(PARSER))
selected = [n for n in syntax.body if isinstance(n, (ast.ClassDef, ast.FunctionDef))
            and n.name in {'Poly', 'Parser', 'tokenize'}]
if {n.name for n in selected} != {'Poly', 'Parser', 'tokenize'}:
    raise ValueError('parser extraction failed')
zero = (0,) * 64
namespace = {'zero': zero, 're': re,
             'commands': {'alpha','beta','gamma','Delta','eta','ell','mu','omega','tau','zeta'},
             'token_re': re.compile(r'\s+|\\[A-Za-z]+|[A-Za-z]|[0-9]+|[+\-*^()\[\]{}=]')}
exec(compile(ast.fix_missing_locations(ast.Module(body=selected, type_ignores=[])), str(PARSER), 'exec'), namespace)
Poly, Parser = namespace['Poly'], namespace['Parser']

def var(index):
    exp = list(zero)
    exp[index] = 1
    return Poly({tuple(exp): 1})

initial = [('J','J'),('F','F'),('alpha','alpha'),('f','f'),('i','i'),('T','T'),
           ('s','s'),('w','w'),('n','n'),('eta','eta'),('zeta','zeta'),
           ('m','m'),('gamma','gamma'),('beta','beta'),('K','K0'),('mu','MC'),('omega','MF')]
expected = [('b','qm'),('q','q'),('C','C'),('X','X'),('Y','Y'),('E','E'),
            ('k','k'),('ell','ell'),('c','c'),('a','a'),('H','H'),('Delta','Delta'),
            ('D','main_root'),('R','R'),('tau','tau'),('L','cTminusR'),('V','V'),('G','B'),('y','y'),
            ('P','N0'),('Q','N1'),('U','Na'),('Z','Z'),('A','corrCoefficient'),('W','correctedU')]

def check(text):
    display = text[:text.index(r'\textbf{The four fixed integers.}')]
    if 'exact degree 92; an 84-operation evaluator.' not in display:
        raise ValueError('unexpected degree or operation caption')
    match = re.search(r'The only unknowns are\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]', display, re.S)
    if not match:
        raise ValueError('missing positive-integer unknowns')
    listed = [x.strip().lstrip('\\') for x in match.group(1).split(',')]
    want = [x[0] for x in initial[:13]]
    if listed != want or len(set(listed)) != 13:
        raise ValueError(('unknowns', listed))
    group = re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}', display, re.S)
    if not group:
        raise ValueError('missing displayed definitions')
    body = group.group(1).strip()
    if not body.endswith('.'):
        raise ValueError('missing definition punctuation')
    defs = [s.strip() for s in body[:-1].replace(r'\quad','').replace('\\\\',',').split(',') if s.strip()]
    if len(defs) != len(expected):
        raise ValueError(('definition count', len(defs)))
    variables = {printed: var(i) for i,(printed,_) in enumerate(initial)}
    inputs = {internal: variables[printed] for printed,internal in initial}
    cuts = {}
    for index, (definition, (label, target)) in enumerate(zip(defs, expected)):
        parser = Parser(definition, variables)
        if parser.take() != label or parser.take() != '=':
            raise ValueError(('unexpected definition', definition))
        actual = parser.expression()
        if parser.peek() is not None:
            raise ValueError(('unparsed tokens', label))
        memo = {}
        def value(name):
            if isinstance(name, int):
                return Poly.lift(name)
            if name in inputs:
                return inputs[name]
            if name in cuts:
                return cuts[name]
            if name not in memo:
                op,left,right = node[name]
                x,y = value(left),value(right)
                memo[name] = {'+':lambda:x+y, '-':lambda:x-y, '*':lambda:x*y}[op]()
            return memo[name]
        wanted = value(target)
        if actual != wanted:
            raise ValueError(('definition differs from graph', label))
        variables[label] = var(len(initial)+index)
        cuts[target] = variables[label]
    boxed = re.search(r'\\boxed\{(.*?)\}', display, re.S)
    if not boxed:
        raise ValueError('missing boxed equation')
    parser = Parser(boxed.group(1).strip().removesuffix('.'), variables)
    left = parser.expression()
    if parser.take() != '=' or parser.take() != '0' or parser.peek() is not None:
        raise ValueError('unexpected boxed equation')
    if left != (variables['P']*variables['Q'])**2+variables['W']**2+variables['Z']**2-3:
        raise ValueError('unexpected boxed factors')
    if rows[-7:] != [['product0','*','N0','N1'], ['sqPQ','*','product0','product0'],
                     ['sqU','*','correctedU','correctedU'], ['sqZ','*','Z','Z'],
                     ['sumPQ_U','+','sqPQ','sqU'], ['sumSquares','+','sumPQ_U','sqZ'],
                     ['polynomial','-','sumSquares',3]]:
        raise ValueError('unexpected graph output wiring')
    return len(defs)

text = TEX.read_text()
count = check(text)
# The 2011 constants and their decimal action encoding are byte-identical to
# the separately audited fourteen-variable display; that older audit retains
# a manual decoder/ranking interpretation boundary.
start = r'\textbf{The four fixed integers.}'
end = r'\normalfont\fontsize{7.7}{8.2}\selectfont'
old = OLD.read_text()
constant_block = text[text.index(start):text.index(end)]
if hashlib.sha256(constant_block.encode()).hexdigest() != '41031aebc8fbac323b9ca29d465865b4d35c92977d8342734f882450f0183267':
    raise ValueError('fixed-constant block does not match independently reviewed 69 display')
if constant_block != old[old.index(start):old.index(end)]:
    raise ValueError('fixed-constant block differs from original display')
for before, after in [('C=q-F-\\alpha', 'C=q+F-\\alpha'),
                      ('b(m-LVG)', 'b(m+LVG)'),
                      ('W=U-A(P-1)', 'W=U+A(P-1)'),
                      ('+Z^2-3=0', '+Z^2+3=0'),
                      ('exact degree 92; an 84-operation evaluator.', 'exact degree 91; an 84-operation evaluator.')]:
    changed = text.replace(before, after, 1)
    if changed == text:
        raise ValueError(('mutation did not apply', before))
    try:
        check(changed)
    except (ValueError, KeyError):
        continue
    raise ValueError(('mutation not detected', before))
print(f'PASS: {count} exact cut-point definitions, 13 distinct positive unknowns, '
      'graph output wiring, identical 2011 constants block, five mutation controls')
print('source SHA256:', sha(TEX))
print('parser SHA256:', sha(PARSER))
