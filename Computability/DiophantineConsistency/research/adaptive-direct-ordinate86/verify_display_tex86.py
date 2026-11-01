#!/usr/bin/env python3
"""Parse the displayed equation86 arithmetic and compare it with its DAG.

This deliberately small parser accepts the exact polynomial TeX subset used in
the display. It is not a general TeX parser or a proof of TeX rendering.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

D = Path(__file__).resolve().parent
BASE = D.parents[1]
TEX = BASE / 'equation86.tex'
JSON = D / 'candidate.json'
data = JSON.read_bytes()
if hashlib.sha256(data).hexdigest() != 'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f':
    raise ValueError('candidate JSON differs from the pinned circuit')
candidate = json.loads(data)
names = candidate['witnesses'] + candidate['fixed_numerals']
zero = (0,) * len(names)

class Poly:
    def __init__(self, terms):
        self.terms = {k: v for k, v in terms.items() if v}
    @staticmethod
    def lift(value):
        return value if isinstance(value, Poly) else Poly({zero: value})
    def __add__(self, other):
        terms = self.terms.copy()
        for monomial, coefficient in self.lift(other).terms.items():
            terms[monomial] = terms.get(monomial, 0) + coefficient
        return Poly(terms)
    __radd__ = __add__
    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})
    def __sub__(self, other):
        return self + -self.lift(other)
    def __rsub__(self, other):
        return self.lift(other) - self
    def __mul__(self, other):
        terms = {}
        for a, x in self.terms.items():
            for b, y in self.lift(other).terms.items():
                c = tuple(i + j for i, j in zip(a, b))
                terms[c] = terms.get(c, 0) + x*y
        return Poly(terms)
    __rmul__ = __mul__
    def __pow__(self, exponent):
        result = self.lift(1)
        for _ in range(exponent):
            result = result * self
        return result
    def __eq__(self, other):
        return self.terms == self.lift(other).terms

dag = {}
for i, name in enumerate(names):
    monomial = list(zero)
    monomial[i] = 1
    dag[name] = Poly({tuple(monomial): 1})
for name, op, left, right in candidate['source']:
    if name in ('g86', 'g87', 'g88', 'P13'):
        continue
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

expected_tail = [['g86','*','F0','F1'], ['g87','*','Fa','g86'],
                 ['g88','*','Fs','g87'], ['P13','-','g88',1]]
if candidate['source'][-4:] != expected_tail:
    raise ValueError('unexpected candidate final product')

symbol_map = {'J':'J', 'F':'F', 'alpha':'alpha', 'f':'f', 'g':'i', 'T':'T',
              'X':'X', 'Y':'Y', 'xi':'r', 'eta':'eta', 'zeta':'zeta',
              'upsilon':'y', 'gamma':'gamma', 'beta':'beta', 'K':'K0',
              'mu':'MC', 'omega':'MF'}
expected_definitions = {'b':'qm','q':'q','C':'C','U':'U','E':'E','k':'k',
                        'ell':'ell','c':'c','a':'a','H':'H','Delta':'Delta',
                        'L':'b0','M':'M','W':'Bt','R':'R','Z':'Z',
                        'D':'Dstar','I':'I','Q':'Q','V':'V'}
commands = {'alpha','beta','gamma','Delta','eta','ell','mu','omega','upsilon','xi','zeta'}
token_re = re.compile(r'\s+|\\[A-Za-z]+|[A-Za-z]|[0-9]+|[+\-*^()\[\]{}=]')

def tokenize(text):
    pos = 0
    result = []
    while pos < len(text):
        match = token_re.match(text, pos)
        if not match:
            raise ValueError(('unknown TeX token', text[pos:pos+40]))
        token = match.group()
        pos = match.end()
        if token.isspace():
            continue
        if token.startswith('\\'):
            token = token[1:]
            if token not in commands:
                raise ValueError(('unexpected command', token))
        result.append(token)
    return result

class Parser:
    def __init__(self, text, variables):
        self.tokens = tokenize(text)
        self.variables = variables
        self.pos = 0
    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None
    def take(self):
        token = self.peek()
        if token is None:
            raise ValueError('unexpected end of expression')
        self.pos += 1
        return token
    def expression(self):
        value = self.product()
        while self.peek() in ('+', '-'):
            op = self.take()
            right = self.product()
            value = value + right if op == '+' else value - right
        return value
    def product(self):
        value = self.power()
        while self.peek() is not None and self.peek() not in ('+', '-', ')', ']', '}', '='):
            if self.peek() == '*':
                self.take()
            value = value * self.power()
        return value
    def power(self):
        value = self.atom()
        if self.peek() == '^':
            self.take()
            wrapped = self.peek() == '{'
            if wrapped:
                self.take()
            exponent = self.take()
            if not exponent.isdigit():
                raise ValueError(('nonliteral exponent', exponent))
            if wrapped and self.take() != '}':
                raise ValueError('unclosed exponent')
            value = Poly.lift(value) ** int(exponent)
        return value
    def atom(self):
        token = self.take()
        if token == '-':
            return -Poly.lift(self.atom())
        if token in ('(', '[', '{'):
            value = self.expression()
            if self.take() != {'(':')', '[':']', '{':'}'}[token]:
                raise ValueError('unbalanced grouping')
            return value
        if token.isdigit():
            return Poly.lift(int(token))
        if token not in self.variables:
            raise ValueError(('unknown or forward-referenced variable', token))
        return self.variables[token]

def parse_and_check(text):
    start = text.index('% BEGIN VERIFIED DISPLAY\n')
    end = text.index('% END VERIFIED DISPLAY\n', start)
    display = text[start:end]
    # Pin the entire raw math environment before translating any residual aliases.
    marker = 'The single Diophantine equation is'
    if display.count(marker) != 1: raise ValueError('equation marker')
    section = display.split(marker, 1)[1]
    raw_equation = re.fullmatch(r'\s*\\\[(.*?)\\\]\s*', section, re.S)
    if not raw_equation or re.sub(r'\s+', '', raw_equation.group(1)) != '\\boxed{\\begin{aligned}&[1+Z^2-M^2(1+\\ell(\\ell+k))]\\\\&\\quad\\cdot[1+D^2-U^2(1+\\Deltac^2)]\\\\&\\quad\\cdot[\\upsilon^2-Q(\\upsilon^2-V^2)][1+I^2-Q]=1.\\end{aligned}}':
        raise ValueError('raw equation environment differs')
    unknowns = re.search(r'The only unknowns are the thirteen separately named positive-integer variables\s*\\\[(.*?)\\in\\mathbb Z_\{>0\}\.\s*\\\]', display, re.S)
    if not unknowns:
        raise ValueError('missing positive-integer unknown declaration')
    listed = [x.strip().lstrip('\\') for x in unknowns.group(1).split(',')]
    expected_unknowns = ['J','F','alpha','f','g','T','X','Y','xi','eta','zeta','upsilon','gamma']
    if listed != expected_unknowns or len(set(listed)) != 13:
        raise ValueError(('unexpected displayed unknowns', listed))
    variables = {printed: dag[internal] for printed, internal in symbol_map.items()}
    group = re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}', display, re.S)
    if not group:
        raise ValueError('missing displayed definitions')
    body = group.group(1).strip()
    if not body.endswith('.'):
        raise ValueError('missing definition punctuation')
    body = body[:-1].replace(r'\quad', '').replace('\\\\', ',')
    definitions = [x.strip() for x in body.split(',') if x.strip()]
    seen = []
    for definition in definitions:
        parser = Parser(definition, variables)
        lhs = parser.take()
        if lhs not in expected_definitions or parser.take() != '=' or lhs in seen:
            raise ValueError(('unexpected definition', definition))
        value = parser.expression()
        if parser.peek() is not None or value != dag[expected_definitions[lhs]]:
            raise ValueError(('definition does not match candidate DAG', lhs))
        variables[lhs] = value
        seen.append(lhs)
    if seen != list(expected_definitions):
        raise ValueError(('missing or reordered definitions', seen))
    match = re.search(r'\\boxed\{\\begin\{aligned\}(.*?)\\end\{aligned\}\}', display, re.S)
    if not match:
        raise ValueError('missing boxed equation')
    equation = match.group(1).strip()
    if not equation.endswith('.'):
        raise ValueError('missing equation punctuation')
    equation = equation[:-1].replace('\\\\', '').replace(r'\quad', '').replace(r'\cdot', '*').replace('&', '')
    parser = Parser(equation, variables)
    factors = []
    while parser.peek() == '[':
        factors.append(parser.atom())
        if parser.peek() == '*':
            parser.take()
    if len(factors) != 4 or parser.take() != '=' or parser.take() != '1' or parser.peek() is not None:
        raise ValueError('unexpected boxed equation shape')
    for index, (actual, name) in enumerate(zip(factors, ('F0','F1','Fa','Fs'))):
        if actual != dag[name]:
            raise ValueError(('boxed factor differs from candidate', index, name))
    return len(seen), len(factors)

text = TEX.read_text()
counts = parse_and_check(text)
# Exact raw-environment controls: a bare alias and an inserted outside term.
raw_marker = 'The single Diophantine equation is'
start_raw = text.index(raw_marker)
raw_open = text.index(r'\[', start_raw) + len(r'\[')
outside_mutation = text[:raw_open] + '1+' + text[raw_open:]
mutations_raw = [outside_mutation]
if r'\mathcal{P}^2' in text[start_raw:]:
    mutations_raw.append(text[:start_raw] + text[start_raw:].replace(r'\mathcal{P}^2', 'resA^2', 1))
for mutation in mutations_raw:
    try: parse_and_check(mutation)
    except ValueError: pass
    else: raise ValueError('raw equation mutation was not detected')

# Check that two concrete source changes are rejected by the parser/comparison.
mutations = [text.replace('C=q-F-\\alpha', 'C=q+F-\\alpha', 1),
             text.replace('[1+I^2-Q]', '[1+I^2+Q]', 1)]
for mutated in mutations:
    if mutated == text:
        raise ValueError('negative control did not mutate TeX')
    try:
        parse_and_check(mutated)
    except ValueError:
        continue
    raise ValueError('negative control was not detected')
print('PASS: parsed', counts[0], 'TeX definitions and', counts[1],
      'boxed factors; 13 positive unknowns; two mutation controls')
