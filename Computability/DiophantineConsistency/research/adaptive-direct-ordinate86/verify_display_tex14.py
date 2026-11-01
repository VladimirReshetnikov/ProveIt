#!/usr/bin/env python3
"""Parse the 14-variable TeX display and compare its factors with the DAG.

The polynomial and small TeX-expression parser come from the companion 86
checker; its normal checks run first. This does not parse fixed constants or
constitute a Lean proof of a TeX interpretation.
"""
import hashlib
import json
from pathlib import Path
import re
import runpy

D = Path(__file__).resolve().parent
BASE = D.parents[1]
data = (BASE / 'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json').read_bytes()
if hashlib.sha256(data).hexdigest() != 'f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e':
    raise ValueError('candidate JSON differs from the pinned circuit')
candidate = json.loads(data)
module = runpy.run_path(str(D / 'verify_display_tex86.py'))
Poly, Parser = module['Poly'], module['Parser']
# Give the shared polynomial implementation the 14-witness/4-port arity.
namespace = Poly.lift.__globals__
names = candidate['witnesses'] + candidate['fixed_numerals']
namespace['zero'] = (0,) * len(names)
namespace['commands'].add('tau')
zero = namespace['zero']
dag = {}
for index, name in enumerate(names):
    monomial = list(zero)
    monomial[index] = 1
    dag[name] = Poly({tuple(monomial): 1})
if candidate['source'][-5:] != [
    ['product0','*','N0','N1'], ['product1','*','product0','Na'],
    ['product3','*','product1','Nt'], ['product4','*','product3','scaled_Ns'],
    ['polynomial','-','product4','Delta']]:
    raise ValueError('unexpected final circuit wiring')
for name, op, left, right in candidate['source'][:-5]:
    x = left if isinstance(left, int) else dag[left]
    y = right if isinstance(right, int) else dag[right]
    if op == '+':
        dag[name] = x + y
    elif op == '-':
        dag[name] = x - y
    elif op == '*':
        dag[name] = x * y
    else:
        raise ValueError(('unexpected candidate operation', op))

symbol_map = {'J':'J', 'F':'F', 'alpha':'alpha', 'z':'z', 'f':'f', 'i':'i',
              'T':'T', 's':'s', 'w':'w', 'n':'n', 'eta':'eta', 'zeta':'zeta',
              'y':'y', 'gamma':'gamma', 'beta':'beta', 'K':'K0', 'mu':'MC', 'omega':'MF'}
expected_definitions = {'b':'qm', 'q':'q', 'C':'C', 'X':'X', 'Y':'Y', 'E':'E',
                        'k':'k', 'ell':'ell', 'c':'c', 'a':'a', 'H':'H',
                        'Delta':'Delta', 'D':'main_root', 'R':'R', 'tau':'tau',
                        'V':'V', 'P':'N0', 'Q':'N1', 'S':'normalized_S',
                        'U':'Na', 'W':'Nt', 'Z':'scaled_Ns'}

def check(text):
    display = text[:text.index(r'\textbf{The four fixed integers.}')]
    unknowns = re.search(r'The only unknowns are\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]', display, re.S)
    if not unknowns:
        raise ValueError('missing positive-integer unknown declaration')
    listed = [x.strip().lstrip('\\') for x in unknowns.group(1).split(',')]
    expected = ['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
    if listed != expected or len(set(listed)) != 14:
        raise ValueError(('unexpected displayed unknowns', listed))
    group = re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}', display, re.S)
    if not group:
        raise ValueError('missing displayed definitions')
    body = group.group(1).strip()
    if not body.endswith('.'):
        raise ValueError('missing definition punctuation')
    body = body[:-1].replace(r'\quad', '').replace('\\\\', ',')
    variables = {printed: dag[internal] for printed, internal in symbol_map.items()}
    seen = []
    for definition in (x.strip() for x in body.split(',') if x.strip()):
        parser = Parser(definition, variables)
        lhs = parser.take()
        if lhs not in expected_definitions or parser.take() != '=' or lhs in seen:
            raise ValueError(('unexpected definition', definition))
        value = parser.expression()
        if parser.peek() is not None or value != dag[expected_definitions[lhs]]:
            raise ValueError(('definition differs from circuit', lhs))
        variables[lhs] = value
        seen.append(lhs)
    if seen != list(expected_definitions):
        raise ValueError(('missing or reordered definitions', seen))
    boxed = re.search(r'\\boxed\{(.*?)\}', display, re.S)
    if not boxed:
        raise ValueError('missing boxed equation')
    expression = boxed.group(1).strip()
    if not expression.endswith('.'):
        raise ValueError('missing equation punctuation')
    tokens = Parser(expression[:-1], variables).tokens
    if tokens != ['P','Q','U','W','Z','-','Delta','=','0']:
        raise ValueError(('unexpected final factor product', tokens))
    return len(seen)

text = (BASE / 'equation.tex').read_text()
count = check(text)
for mutation in (text.replace('C=q-F-\\alpha', 'C=q+F-\\alpha', 1),
                 text.replace('PQUWZ-\\Delta=0', 'PQUWZ+\\Delta=0', 1)):
    if mutation == text:
        raise ValueError('negative control did not mutate the TeX')
    try:
        check(mutation)
    except ValueError:
        continue
    raise ValueError('negative control was not detected')
print('PASS: parsed', count, 'TeX definitions and final factor wiring;',
      '14 positive unknowns; two mutation controls')
