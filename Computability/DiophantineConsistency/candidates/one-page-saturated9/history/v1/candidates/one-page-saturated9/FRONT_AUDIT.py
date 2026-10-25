#!/usr/bin/env python3
"""Audit actual nine-positive TeX, the complete fixed tuple, graph and PDF.

Preparation HOLD: this new module must not be imported or executed until
the complete code closure has two static approvals and a root release.
Only Python standard-library modules are used. No parent program is loaded.
"""
import argparse
from collections import Counter
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PAGE = ROOT/'candidates/one-page-saturated9'
GAP = ROOT/'candidates/gap2082-compact54'
OLD = ROOT/'candidates/one-page-compression/original-base62-collected'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
NATIVE_MARKER = r'\textbf{The complete fixed coefficient tuple.}'
GRAPH_SHA = 'bf0907fb36ab78830922f61e5bfbacbd80786ebd375a11b4d0cf6b1bfb7c12b3'
VARIABLES = ['b', 'g', 'h', 's', 'w', 'C', 'i', 'j', 'n']
PORTS = ['beta', 'K0', 'MC', 'MF']


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def encoded(data):
    return (json.dumps(data, indent=2, sort_keys=True)+'\n').encode()


def pin_inputs():
    """Authenticate whole data/code, without importing any pinned program."""
    pins = load(PAGE/'TOOL_PINS.json')
    for key in ['external_files', 'preparation_files', 'tool_core']:
        for name, pin in pins[key].items():
            path = ROOT/name if key == 'external_files' else PAGE/name
            if name.startswith('../../tools/'):
                path = PAGE/name
            raw = path.read_bytes()
            need(digest(raw) == pin['sha256'] and len(raw) == pin['bytes'], key+' whole bytes '+name)
    prep = load(PAGE/'SOURCE_PINS.json')
    for name, pin in prep['external_files'].items():
        raw = (ROOT/name).read_bytes()
        need(digest(raw) == pin['sha256'] and len(raw) == pin['bytes'], 'preparation dependency '+name)
    for name, pin in prep['own_core'].items():
        raw = (PAGE/name).read_bytes()
        need(digest(raw) == pin['sha256'] and len(raw) == pin['bytes'], 'frozen preparation member '+name)
    return pins


# A polynomial is an integer coefficient dictionary indexed by sorted
# (symbol, natural exponent) tuples. This expands local blocks, never the
# degree-1,628,768 polynomial. No modular or numerical identity is used.
def const(n):
    need(type(n) is int, 'integer ring coefficient')
    return {(): n} if n else {}


def atom(name):
    return {((name, 1),): 1}


def add(a, b, sign=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0)+sign*c
        if out[m] == 0:
            del out[m]
    return out


def mul(a, b):
    out = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            powers = dict(ma)
            for name, exponent in mb:
                powers[name] = powers.get(name, 0)+exponent
            m = tuple(sorted(powers.items()))
            out[m] = out.get(m, 0)+ca*cb
    out = {m: c for m, c in out.items() if c}
    need(len(out) <= 10000, 'reviewed local sparse polynomial size')
    return out


def power(a, exponent):
    need(type(exponent) is int and 0 <= exponent <= 6500000, 'fixed natural polynomial exponent')
    result = const(1)
    while exponent:
        if exponent & 1:
            result = mul(result, a)
        exponent //= 2
        if exponent:
            a = mul(a, a)
    return result


def recipe(terms):
    result = {}
    for term in terms:
        need(len(term['port_powers']) == 4, 'all four coefficient powers')
        value = const(term['integer'])
        for name, exponent in zip(PORTS, term['port_powers']):
            value = mul(value, power(atom(name), exponent))
        result = add(result, value)
    return result


def clean_math(text):
    for command in [r'\qquad', r'\quad', r'\,', r'\\', r'\bigl', r'\bigr']:
        text = text.replace(command, ' ')
    return text.replace('&', '')


ALIASES = {
    r'\mathcal W': ('list', 'weights'), r'\mathcal T': ('list', 'targets'),
    r'D_0': ('function', 'D0'), r'D_1': ('function', 'D1'), r'D_2': ('function', 'D2'),
    'p': ('function', 'p'), r'\ell': 'ell', r'\Omega': 'Omega',
    r'\Theta': 'Theta', r'\delta': 'delta', r'\Lambda': 'Lambda',
    r'\beta': 'beta', 'K_0': 'K0', 'M_C': 'MC', 'M_F': 'MF',
    'N_0': 'N0', 'G_c': 'Gc', 'S_c': 'Sc', 'T_c': 'Tc', 'L_c': 'Lc',
    'c_*': 'cap', 'B_1': 'B1', 'W_1': 'W1', 'J_r': 'Jr', 'Q_r': 'Qr',
    'E_0': 'E0', 'V_0': 'V0', 'V_1': 'V1', 'd_e': 'de', 'F_p': 'Fp',
    'G_p': 'Gp', 'T_m': 'Tm', 'a_0': 'a0', 'a_1': 'a1',
}
for _name in VARIABLES+['B', 'Z', 'u', 'R', 'N', 'U', 'Y', 'M', 'P', 'k', 'A', 'm', 'D', 'e', 'H', 'I']:
    ALIASES[_name] = _name
KEYS = sorted(ALIASES, key=len, reverse=True)


def tokens(text):
    text = clean_math(text)
    out, pos = [], 0
    while pos < len(text):
        c = text[pos]
        if c.isspace():
            pos += 1
        elif c in '+-*^()[]{} ,':
            out.append(c)
            pos += 1
        elif c.isdigit():
            m = re.match(r'\d+', text[pos:])
            out.append(int(m[0]))
            pos += len(m[0])
        else:
            key = next((k for k in KEYS if text.startswith(k, pos)), None)
            need(key is not None, 'complete actual TeX token '+text[pos:])
            value = ALIASES[key]
            out.append(value if isinstance(value, tuple) else ('symbol', value))
            pos += len(key)
    return out


class Parser:
    def __init__(self, text, env, lists, kernels):
        self.ts, self.pos = tokens(text), 0
        self.env, self.lists, self.kernels = env, lists, kernels

    def pop(self, token):
        need(self.pos < len(self.ts) and self.ts[self.pos] == token, 'actual polynomial delimiter '+str(token))
        self.pos += 1

    def parse(self):
        value = self.expression()
        need(self.pos == len(self.ts), 'entire actual polynomial expression')
        return value

    def expression(self):
        value = self.product()
        while self.pos < len(self.ts) and self.ts[self.pos] in ['+', '-']:
            op = self.ts[self.pos]
            self.pos += 1
            value = add(value, self.product(), 1 if op == '+' else -1)
        return value

    def product(self):
        value = self.powered()
        while self.pos < len(self.ts):
            t = self.ts[self.pos]
            if t == '*':
                self.pos += 1
                value = mul(value, self.powered())
            elif type(t) is int or isinstance(t, tuple) or t in ['(', '[', '{']:
                value = mul(value, self.powered())
            else:
                break
        return value

    def powered(self):
        value = self.primary()
        if self.pos < len(self.ts) and self.ts[self.pos] == '^':
            self.pos += 1
            braces = self.ts[self.pos] == '{'
            if braces:
                self.pos += 1
            exponent = self.ts[self.pos]
            self.pos += 1
            need(type(exponent) is int, 'no unknown used as a polynomial exponent')
            if braces:
                self.pop('}')
            # These two particular printed numerals are authenticated as
            # complete integer payloads independently, not left as ports.
            if value == const(2) and exponent in [864026, 6480184]:
                value = atom('base_scale' if exponent == 864026 else 'threshold_6480184')
            else:
                value = power(value, exponent)
        return value

    def primary(self):
        need(self.pos < len(self.ts), 'complete polynomial operand')
        t = self.ts[self.pos]
        self.pos += 1
        if t == '-':
            return mul(const(-1), self.powered())
        if type(t) is int:
            return const(t)
        if isinstance(t, tuple):
            if t[0] == 'symbol':
                need(t[1] in self.env, 'previous actual abbreviation '+t[1])
                return self.env[t[1]]
            need(t[0] == 'function', 'finite list used only inside p')
            self.pop('(')
            if t[1] == 'p':
                exponents = []
                if self.pos < len(self.ts) and isinstance(self.ts[self.pos], tuple) and self.ts[self.pos][0] == 'list':
                    exponents = self.lists[self.ts[self.pos][1]]
                    self.pos += 1
                else:
                    while True:
                        need(self.pos < len(self.ts) and type(self.ts[self.pos]) is int, 'explicit finite-list exponent')
                        exponents.append(self.ts[self.pos])
                        self.pos += 1
                        if self.pos >= len(self.ts) or self.ts[self.pos] != ',':
                            break
                        self.pos += 1
                self.pop(')')
                result = {}
                for exponent in exponents:
                    result = add(result, power(self.env['B'], exponent))
                return result
            need(self.ts[self.pos] == ('symbol', 'B'), 'kernel argument is exactly packing B')
            self.pos += 1
            self.pop(')')
            need(t[1] in self.kernels, 'complete preceding printed kernel')
            return self.kernels[t[1]]
        need(t in ['(', '[', '{'], 'polynomial grouping')
        value = self.expression()
        self.pop({'(': ')', '[': ']', '{': '}'}[t])
        return value


def top_split(text, separator=','):
    parts, start, stack = [], 0, []
    for j, c in enumerate(text):
        if c in '([{':
            stack.append(c)
        elif c in ')]}':
            need(stack and stack.pop() == {')': '(', ']': '[', '}': '{'}[c], 'balanced complete displayed statement')
        elif c == separator and not stack:
            parts.append(text[start:j])
            start = j+1
    need(not stack, 'closed displayed statement groups')
    parts.append(text[start:])
    return parts


def braced(text, marker):
    need(text.count(marker) == 1, 'unique actual math boundary '+marker)
    start = text.index(marker)+len(marker)
    depth = 1
    for j in range(start, len(text)):
        if text[j] == '{':
            depth += 1
        elif text[j] == '}':
            depth -= 1
            if depth == 0:
                return text[start:j]
    raise ValueError('unclosed actual math boundary '+marker)


CUTS = [
    ('B', 13), ('N0', 55), ('ell', 107), ('Z', 163), ('u', 186), ('Gc', 366),
    ('Sc', 370), ('Tc', 167), ('Lc', 51), ('R', 375), ('N', 377), ('cap', 401),
    ('U', 382), ('Y', 380), ('M', 381), ('P', 396), ('k', 399), ('A', 384),
    ('B1', 432), ('W1', 3), ('Jr', 388), ('Qr', 10), ('m', 411), ('Omega', 412),
    ('E0', 393), ('V0', 413), ('delta', 415), ('D', 418), ('e', 421), ('de', 422),
    ('Fp', 425), ('Lambda', 428), ('Gp', 430), ('H', 438), ('Tm', 440), ('V1', 441),
    ('I', 452), ('a0', 448), ('a1', 454), ('Theta', 444),
]


def graph_shape(graph):
    need(graph['variables'] == VARIABLES and graph['domain'] == 'positive', 'complete literal positive signature')
    need(graph['output'] == 463 and len(graph['nodes']) == 464, 'whole literal output and node census')
    counts = Counter()
    fixed, variable, dependencies = {}, {}, {}
    for j, node in enumerate(graph['nodes']):
        kind = node['kind']
        if kind in ['add', 'sub', 'mul']:
            need(set(node) == {'kind', 'left', 'right'} and all(type(node[k]) is int and 0 <= node[k] < j for k in ['left', 'right']), 'whole binary topology')
            counts[kind] += 1
            dependencies[j] = [node['left'], node['right']]
        elif kind == 'fixed':
            need(set(node) == {'kind', 'name'} and node['name'] not in fixed, 'unique fixed leaf')
            fixed[node['name']] = j
        elif kind == 'variable':
            need(set(node) == {'kind', 'name'} and node['name'] not in variable, 'unique input leaf')
            variable[node['name']] = j
        else:
            need(kind == 'literal' and set(node) == {'kind', 'value'} and type(node['value']) is int, 'exact integer literal leaf')
    need(counts == Counter({'add': 157, 'mul': 256, 'sub': 20}) and sum(counts.values()) == graph['total_operations'] == 433, 'all433 actual binary operations')
    need(graph['operation_counts'] == dict(counts) and graph['exact_degree'] == 1628768, 'accepted exact degree and operation metadata')
    need(set(variable) == set(VARIABLES) and len(fixed) == 11, 'exact nine-input eleven-fixed-leaf signature')
    live, todo = set(), [graph['output']]
    while todo:
        j = todo.pop()
        if j not in live:
            live.add(j)
            todo.extend(dependencies.get(j, []))
    need(live == set(range(464)), 'all nodes, operations, variables and fixed leaves live')
    return variable, fixed, counts


def printed_front(tex, graph, kernel_data, layout):
    variable, fixed, counts = graph_shape(graph)
    need(tex.count(NATIVE_MARKER) == 1, 'complete constant boundary')
    front = tex.split(NATIVE_MARKER, 1)[0]
    need(r'b,g,h,s,w,C,i,j,n\in\mathbb Z_{>0}' in front, 'actual nine strictly positive inputs')
    need(r'accepted evaluator: 433 operations, degree $1{,}628{,}768$.' in front, 'actual exact degree/cost claim')
    need(r'p(e_1,\ldots,e_t)=\sum_{\nu=1}^{t}B^{e_\nu}' in front, 'complete finite-list sum definition')
    lists = {}
    for symbol, name in [('W', 'weights'), ('T', 'targets')]:
        m = re.search(r'\\mathcal '+symbol+r'=\{\}&\((.*?)\)', front, re.S)
        need(m is not None, 'complete printed '+name)
        text = re.sub(r'\s|&|\\\\', '', m[1])
        need(re.fullmatch(r'\d+(?:,\d+)*', text), 'all integer list entries '+name)
        lists[name] = [int(x) for x in text.split(',')]
        need(lists[name] == layout[name], 'entire ordered actual '+name)
    need(len(lists['weights']) == 31 and len(lists['targets']) == 22, '31weights and22targets')
    kernel_text = front.split(r'\textbf{All 85 kernel terms.}', 1)[1]
    aligned = kernel_text.split(r'\begin{aligned}', 1)[1].split(r'\end{aligned}', 1)[0]
    sections = re.split(r'D_([012])\(B\)=\{\}&', aligned)
    need(len(sections) == 7 and not sections[0].strip(), 'exactly all three printed kernels')
    env = {n: atom(n) for n in VARIABLES+PORTS+['B']}
    kernels, supports = {}, {}
    for pos in [1, 3, 5]:
        degree = int(sections[pos])
        text = clean_math(sections[pos+1]).strip().removesuffix('.')
        value = Parser(text, env, lists, {}).parse()
        expected = {}
        record = next(k for k in kernel_data['kernels'] if k['degree'] == degree)
        for term in record['terms']:
            expected = add(expected, mul(recipe(term['coefficient']), power(atom('B'), term['exponent'])))
        need(value == expected, 'ALL complete free-four-port kernel coefficients/support D'+str(degree))
        kernels['D'+str(degree)] = value
        supports[str(degree)] = [t['exponent'] for t in record['terms']]
    need([len(supports[str(d)]) for d in [0, 1, 2]] == [6, 36, 43], 'all85 kernel records')
    math = front.split(r'\begin{gathered}', 1)[1].split(r'\end{gathered}', 1)[0]
    statements = [s.strip().removesuffix('.') for s in top_split(clean_math(math)) if s.strip()]
    need(len(statements) == 40, 'all40 actual front definitions')
    context = {j: atom(n) for n, j in variable.items()}
    coeff = {r['name']: recipe(r['terms']) for r in graph['coefficient_recipes']}
    coeff.update({n: atom(n) for n in ['base_scale', 'threshold_6480184']})
    need(set(coeff) == set(fixed), 'all eleven fixed leaves have exact symbolic definitions')
    touched, assignments = set(), []

    def evaluate(j, memo):
        touched.add(j)
        if j in context:
            return context[j]
        if j in memo:
            return memo[j]
        node = graph['nodes'][j]
        kind = node['kind']
        if kind == 'literal':
            value = const(node['value'])
        elif kind == 'fixed':
            value = coeff[node['name']]
        else:
            need(kind in ['add', 'sub', 'mul'], 'all variables already bound')
            a, b = evaluate(node['left'], memo), evaluate(node['right'], memo)
            value = mul(a, b) if kind == 'mul' else add(a, b, -1 if kind == 'sub' else 1)
        memo[j] = value
        return value

    printed = {n: atom(n) for n in VARIABLES+PORTS}
    for statement, (name, node) in zip(statements, CUTS):
        need(statement.count('=') == 1, 'single actual displayed assignment')
        lhs, rhs = statement.split('=')
        need(tokens(lhs) == [('symbol', name)] and name not in printed, 'exact ordered fresh front alias '+name)
        value = Parser(rhs, printed, lists, kernels).parse()
        need(value == evaluate(node, {}), 'complete exact literal-block identity '+name)
        printed[name] = atom(name)
        context[node] = atom(name)
        assignments.append({'symbol': name, 'node': node})
        if name == 'R':
            # Actual k reuses node374 rather than traversing node375. The
            # just-proved node375=row374-1 licenses this affine bridge.
            need(graph['nodes'][375] == {'kind': 'sub', 'left': 374, 'right': 52} and graph['nodes'][52] == {'kind': 'literal', 'value': 1}, 'exact R+1 bridge')
            context[374] = add(atom('R'), const(1))
    box = braced(front, r'\boxed{')
    need(box.count('=') == 1, 'single complete boxed equation')
    lhs, rhs = box.split('=')
    need(rhs.strip() == '0.' or rhs.strip() == '0', 'boxed zero target')
    need(Parser(lhs, printed, lists, kernels).parse() == evaluate(463, {}), 'complete shared final norm block')
    need(touched == set(range(464)), 'union of exact blocks covers EVERY literal node')
    return {'assignments': assignments, 'covered_nodes': len(touched), 'all433_operations_live': True,
            'operation_breakdown': dict(counts), 'kernel_supports': supports,
            'weights': lists['weights'], 'targets': lists['targets'], 'ratio_math': math,
            'kernel_math': aligned, 'boxed_math': lhs}


# Each complete recipe block is a reviewed mathematical schema, not an
# outer document digest. The actual seven printed blocks must match these
# formulas after whitespace/alignment normalization; THEN the actual seed
# is decoded and every resulting integer is independently reconstructed.
NATIVE_BLOCKS = [
r'''\rho=2^{89},\quad\mathcal B=\rho^{4831},\quad\beta=\mathcal B-1,\\
\lambda=2^{29},\quad\theta=2^{42},\quad\mathcal Q=2^{40},\\
G_t(x)=\sum_{r=0}^{t-1}x^r,\quad
\mu=510+2^{17}+2^{26}+2^{28}+\lambda(2^{44}-1).''',
r'''\mathcal S={}&\rng0{456}\cup\rng{495}{504}\cup\{507,508\}\\
&\cup\rng{517}{537}\cup\rng{539}{549}\\
&\cup\rng{567}{583}\cup\{1203,1807\}.''',
r'''M_C={}&\mathcal B-1-\sum_{r\in\mathcal S\setminus\{1\}}\rho^r-2\rho^{507},\\
M_F={}&\mathcal B-1+4+\mu(\rho^{2409}+\rho^{3015})\\
&+\rho^{528}G_{10}(\rho)+\rho^{585}G_{11}(\rho)+\rho^{1203}+\rho^{1807}\\
&+(2^{87}-1)\rho^{4823}G_4(\rho)+(2^{38}-1)\rho^{4827},\\
K_0={}&\rho^{33}+\rho^{68}+\rho^{664}+\rho^{1268}+\rho^{4877}\\
&+(\rho^{2409}+\rho^{3015})\Phi(1/\rho),''',
r'''\Phi(x)={}&O G_{457}(x)+\lambda\sum_{a=0}^{456}\ell_a x^{r_a}\\
&-(255\,2^9+2^{27})x^{374}-(255\,2^{18}+2^{27})x^4\\
&+\lambda\bigl[(x^{539}+2^{21}x^{517})G_{11}(2x)\\
&\qquad +(2^{11}x^{528}+2^{32}x^{495})G_{10}(2x)\\
&\qquad +\theta(x^{539}+x^{1203}+x^{1807})\bigr]\\
&+\bigl[(2^9+\lambda(2+2^{33}))x^{567}\\
&\qquad +(2^{18}+\lambda(2^{22}+2^{33}))x^{575}\bigr]G_8(2x)\\
&+(2^{27}+\lambda(2^{11}+2^{32}))x^{583}.''',
r'''b_r=\fl{\mathcal A/1024^r}\bmod1024,\quad u_r=b_r\bmod256,\\
v_r=\fl{b_r/256}\bmod2,\quad d_r=\fl{b_r/512},\\
t_{2+r}=((1-d_r)(512+u_r),512+r,d_r(256+u_r),v_r).''',
r'''\text{index}&\text{range}&t_r\\\hline
0&& (2,3,3,1)\\1&& (5,0,0,0)\\
432+r&0\le r<2&(0,942+r,0,942+r)\\
434+r&0\le r<2&(0,r,0,r)\\
436+r&0\le r<4&(0,(r\bmod2)+942\fl{r/2},0,6)\\
440&&(2,2,2,0)\\441&&(3,4,4,698)\\442&&(4,4,4,0)\\
443+r&0\le r<3&(1,6,1,2+r)\\
446+3r+t&0\le r,t<3&(r^2,5,t,5)\\
455&&(256,0,0,512)\\456&&(0,0,512,512)''',
r'''\kappa_r&=2^{30}w_r+2^{20}n_r+2^{10}e_r+s_r,\\
\ell_r&=2w_r+2^{11}n_r+2^{22}e_r+2^{32}s_r,\\
r_0&=0,\quad r_1=1,\\
r_t&=2+\sum_{r=2}^{456}\fl{\frac{\mathcal Q+\kappa_t-\kappa_r-1}{\mathcal Q}}
\quad(2\le t\le456),\\
O&=1+255\,2^9+255\,2^{18}+2^{27}+\lambda.''',
]


def native_canon(text):
    text = re.sub(r'\\(?:begin|end)\{(?:gathered|aligned)\}', '', text)
    text = re.sub(r'\\begin\{array\}\{c\|c\|l\}|\\end\{array\}', '', text)
    return re.sub(r'\s', '', clean_math(text))


def native_recipe(tex, reconstruct=True):
    body = tex.split(NATIVE_MARKER, 1)[1]
    blocks = re.findall(r'\\\[(.*?)\\\]', body, re.S)
    need(len(blocks) == len(NATIVE_BLOCKS) == 7, 'all seven COMPLETE native display blocks')
    for j, (actual, expected) in enumerate(zip(blocks, NATIVE_BLOCKS)):
        need(native_canon(actual) == native_canon(expected), 'entire actual native formula block '+str(j))
    need(r'$a\bmod b=a-b\fl{a/b}$' in body, 'complete quotient/remainder convention')
    need(r'$\mathcal A=\sum_{r=0}^{721}\epsilon_r62^{721-r}$' in body, 'actual complete positional numeral definition')
    need('following 457 fixed quadruples' in body and r'$0\le r<430$' in body and 'following 722 characters' in body, 'actual finite native table/action/seed bounds')
    groups = re.findall(r'\\ttfamily\s*(.*?)\\endgroup', body, re.S)
    need(len(groups) == 2, 'entire alphabet and literal seed groups')
    alphabet, seed = [re.sub(r'\\par|\s', '', g) for g in groups]
    need(alphabet == ALPHABET and len(seed) == 722 and set(seed) <= set(alphabet), 'all62 alphabet and722 seed characters')
    need(seed == (OLD/'SEED.txt').read_text().strip(), 'complete actual original seed, not a transferred controller')
    if not reconstruct:
        return {'seed': seed, 'blocks': blocks}
    seed_value = 0
    for c in seed:
        seed_value = 62*seed_value+alphabet.index(c)
    modes = [(2, 3, 3, 1), (5, 0, 0, 0)]
    for r in range(430):
        digit = seed_value//1024**r % 1024
        target, write, right = digit % 256, digit//256 % 2, digit//512
        need(target <= 215 and right in [0, 1], 'actual ten-bit transition digit')
        modes.append(((1-right)*(512+target), 512+r, right*(256+target), write))
    need(seed_value//1024**430 == 0, 'no omitted high transition bits')
    modes += [(0, 942+r, 0, 942+r) for r in range(2)]
    modes += [(0, r, 0, r) for r in range(2)]
    modes += [(0, r % 2+942*(r//2), 0, 6) for r in range(4)]
    modes += [(2, 2, 2, 0), (3, 4, 4, 698), (4, 4, 4, 0)]
    modes += [(1, 6, 1, 2+r) for r in range(3)]
    modes += [(r*r, 5, t, 5) for r in range(3) for t in range(3)]
    modes += [(256, 0, 0, 512), (0, 0, 512, 512)]
    need(len(modes) == len(set(modes)) == 457, 'all457 actual distinct constant quadruples')
    keys = [2**30*w+2**20*n+2**10*e+s for w, n, e, s in modes]
    ranks = [0, 1]+[2+sum((2**40+keys[t]-keys[r]-1)//2**40 for r in range(2, 457)) for t in range(2, 457)]
    need(sorted(ranks) == list(range(457)), 'entire arithmetic rank permutation')
    ordered = modes[:2]+sorted(modes[2:])
    need(all(ordered[ranks[r]] == modes[r] for r in range(457)), 'all ranks equal their actual sorted modes')
    rho, lam, theta = 2**89, 2**29, 2**42
    base = rho**4831
    ordinary = 1+255*2**9+255*2**18+2**27+lam
    phi = {r: ordinary for r in range(457)}
    def put(e, c):
        phi[e] = phi.get(e, 0)+c
    for r, (w, n, e, s) in enumerate(modes):
        put(ranks[r], lam*(2*w+2**11*n+2**22*e+2**32*s))
    put(374, -(255*2**9+2**27))
    put(4, -(255*2**18+2**27))
    for r in range(11):
        put(539+r, lam*2**r)
        put(517+r, lam*2**(21+r))
    for r in range(10):
        put(528+r, lam*2**(11+r))
        put(495+r, lam*2**(32+r))
    for e in [539, 1203, 1807]:
        put(e, lam*theta)
    for r in range(8):
        put(567+r, (2**9+lam*(2+2**33))*2**r)
        put(575+r, (2**18+lam*(2**22+2**33))*2**r)
    put(583, 2**27+lam*(2**11+2**32))
    denominator = rho**1807
    numerator = sum(c*rho**(1807-e) for e, c in phi.items())
    scaled = (rho**2409+rho**3015)*numerator
    need(scaled % denominator == 0, 'printed rational Phi evaluation is an exact integer')
    kval = sum(rho**e for e in [33, 68, 664, 1268, 4877])+scaled//denominator
    support = set(range(457))|set(range(495, 505))|{507, 508}|set(range(517, 538))|set(range(539, 550))|set(range(567, 584))|{1203, 1807}
    need(len(support) == 520, 'all printed support entries')
    mc = base-1-sum(rho**e for e in support if e != 1)-2*rho**507
    mu = 510+2**17+2**26+2**28+lam*(2**44-1)
    mf = base-1+4+mu*(rho**2409+rho**3015)
    mf += sum(rho**(528+r) for r in range(10))+sum(rho**(585+r) for r in range(11))+rho**1203+rho**1807
    mf += (2**87-1)*sum(rho**(4823+r) for r in range(4))+(2**38-1)*rho**4827
    return {'seed': seed, 'blocks': blocks, 'ports': dict(beta=base-1, K0=kval, MC=mc, MF=mf),
            'mode_count': len(modes), 'support_count': len(support), 'rank_permutation': True,
            'seed_bits': seed_value.bit_length(), 'Phi_reciprocal_is_exact_integer': True}


def whole_payloads(ports, graph):
    binding = load(GAP/'coefficients/COEFFICIENT_BINDING.json')
    names = {'beta': 'beta', 'K': 'K0', 'MC': 'MC', 'MF_source': 'MF'}
    records = []
    for pin in binding['ports']:
        value = ports[names[pin['port']]]
        raw = value.to_bytes((value.bit_length()+7)//8, 'little')
        compressed = (GAP/'coefficients'/pin['gzip_file']).read_bytes()
        need(gzip.decompress(compressed) == raw and digest(raw) == pin['sha256'] and digest(compressed) == pin['gzip_sha256'], 'ENTIRE reconstructed actual native port '+pin['port'])
        need(value.bit_length() == pin['bits'] and len(raw) == pin['bytes'], 'canonical whole native integer '+pin['port'])
        records.append({'port': pin['port'], 'raw_bytes': len(raw), 'bits': value.bit_length(), 'raw_sha256': digest(raw)})
    need(sum(r['raw_bytes'] for r in records) == 215492, 'all215492 actual reconstructed tuple bytes')
    values = {'base_scale': 1 << 864026, 'threshold_6480184': 1 << 6480184}
    for r in graph['coefficient_recipes']:
        value = 0
        for term in r['terms']:
            c = term['integer']
            for name, exponent in zip(PORTS, term['port_powers']):
                c *= ports[name]**exponent
            value += c
        values[r['name']] = value
    fixed_binding = load(GAP/'fixed/BINDING.json')
    need(set(values) == {r['name'] for r in fixed_binding['records']}, 'exact all11 fixed integer recipes')
    for r in fixed_binding['records']:
        value = values[r['name']]
        raw = abs(value).to_bytes((abs(value).bit_length()+7)//8, 'little')
        compressed = (GAP/r['path']).read_bytes()
        need(gzip.decompress(compressed) == raw and digest(raw) == r['raw_sha256'] and digest(compressed) == r['gzip_sha256'], 'ENTIRE actual fixed leaf '+r['name'])
        need((1 if value > 0 else -1) == r['sign'] and abs(value).bit_length() == r['bits'] and len(raw) == r['raw_bytes'], 'canonical signed fixed leaf '+r['name'])
    return records


def audit_tex(tex, graph, kernels, layout, reconstruct=True):
    front = printed_front(tex, graph, kernels, layout)
    native = native_recipe(tex, reconstruct)
    return front, native


def corruption_controls(tex, graph, kernels, layout):
    tests = [
        ('packing base exponent', 'B=2^{864026}b^2', 'B=2^{864025}b^2'),
        ('packing variable power', 'B=2^{864026}b^2', 'B=2^{864026}b^3'),
        ('missing weight', '109,110,112,116', '109,112,116'),
        ('changed target', '2028,2050)', '2028,2051)'),
        ('kernel constant sign', '2K_0B^{124}-2p', '-2K_0B^{124}-2p'),
        ('kernel omitted exponent', '325,384,1450,1627', '325,384,1627'),
        ('kernel paired coefficient', '2\\beta(K_0+1)B^{123}', '2\\beta(K_0-1)B^{123}'),
        ('kernel shifted-F coefficient', '-2\\beta M_FB^{844}', '-2\\beta M_FB^{843}'),
        ('kernel coefficient power', '-2\\beta^2B^{1259}', '-2\\beta B^{1259}'),
        ('source word factor', 'Z+2G_c', 'Z+G_c'),
        ('word transport sign', 'R=L_c(S_c+T_c+1)-S_c-1', 'R=L_c(S_c+T_c+1)+S_c-1'),
        ('threshold scale', 'N=2^{6480184}', 'N=2^{6480183}'),
        ('ratio square', 'P=2M^2U', 'P=2MU'),
        ('margin cap', '16c_*(C-kY)^2', '8c_*(C-kY)^2'),
        ('saturated factor', 'F_p=1+(\\delta e)d_e', 'F_p=1+\\delta e'),
        ('missing Pell definition', r'T_m=Ad_e,\quad V_1=T_m(G_pH),', r'T_m=Ad_e,'),
        ('wrong input shift', '(j-1)C', '(j+1)C'),
        ('shared norm sign', '-4\\Omega^2a_0\\Theta^2', '+4\\Omega^2a_0\\Theta^2'),
        ('wrong tail factor', '-4\\Omega^2a_0\\Theta^2', '-4\\Omega^2a_1\\Theta^2'),
        ('nonpositive input domain', r'\mathbb Z_{>0}', r'\mathbb Z_{\ge0}'),
        ('wrong exact degree claim', '1{,}628{,}768', '1{,}628{,}767'),
        ('wrong operation claim', '433 operations', '432 operations'),
        ('native radix changed', r'\rho^{4831}', r'\rho^{4830}'),
        ('native initializer', '(3,4,4,698)', '(3,4,4,514)'),
        ('native alphabet swap', ALPHABET, '1023456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'),
        ('double shifted F mask', r'M_F={}&\mathcal B-1+4', r'M_F={}&2(\mathcal B-1)+4'),
        ('Phi receiver correction', r'x^{374}-(255', r'x^{375}-(255'),
        ('rank controller ceiling', r'\mathcal Q=2^{40}', r'\mathcal Q=2^{41}'),
    ]
    seed = (OLD/'SEED.txt').read_text().strip()
    tests.append(('actual literal seed character', seed[:12], ('0' if seed[0] != '0' else '1')+seed[1:12]))
    rejected = []
    for label, old, new in tests:
        need(tex.count(old) == 1, 'unique ACTUAL printed mutation site '+label)
        try:
            audit_tex(tex.replace(old, new), graph, kernels, layout, False)
        except (ValueError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise ValueError('accepted ACTUAL TeX corruption '+label)
    positives = [
        ('formatting whitespace', tex.replace(r'B=2^{864026}b^2,\quad', r'B=2^{864026}b^2,\qquad', 1)),
        ('distributive A spelling', tex.replace('A=M(U+1)', 'A=M+MU')),
        ('kernel commutative support order', tex.replace('325,384,1450,1627', '1627,1450,384,325')),
    ]
    for label, good in positives:
        need(good != tex, 'real positive printed control '+label)
        audit_tex(good, graph, kernels, layout, False)
    return rejected, [label for label, _ in positives]


def pdf_text(path):
    return subprocess.run(['pdftotext', '-raw', str(path), '-'], check=True, capture_output=True, text=True).stdout


def math_glyphs(text):
    """Full front variable/operator/numeral stream, ignoring delimiters only."""
    text = clean_math(text)
    for command, value in [(r'\Omega', 'Ω'), (r'\Theta', 'Θ'), (r'\delta', 'δ'), (r'\Lambda', 'Λ'), (r'\beta', 'β'), (r'\ell', 'ℓ'), (r'\mathcal W', 'W'), (r'\mathcal T', 'T')]:
        text = text.replace(command, value)
    text = text.replace('−', '-').replace('∗', '*').replace('Ω', 'Ω')
    return ''.join(c for c in text if c.isalnum() or c in '+-=*ΩΘδΛβℓ')


def check_pdf(tex, front, native):
    path = PAGE/'equation.pdf'
    text = pdf_text(path)
    compact = re.sub(r'\s', '', text)
    need(native['seed'] in compact and ALPHABET in compact, 'ALL actual PDF seed/alphabet characters')
    need('b,g,h,s,w,C,i,j,n∈Z>0' in compact, 'actual PDF nine-positive signature')
    need('433operations,degree1,628,768.' in compact, 'actual PDF exact degree/cost claim')
    stream = math_glyphs(text)
    # The actual front has no sums, floors or fractions. All of its
    # variable, coefficient, exponent and operator glyphs are checked in
    # complete consecutive blocks; punctuation delimiters are ignored.
    expected = [front['boxed_math']+'=0', front['ratio_math']]
    expected += [','.join(str(x) for x in front['weights']), ','.join(str(x) for x in front['targets'])]
    expected += [front['kernel_math']]
    cursor = 0
    for block in expected:
        sig = math_glyphs(block)
        pos = stream.find(sig, cursor)
        need(pos >= 0, 'entire actual PDF front glyph block')
        cursor = pos+len(sig)
    # Native mathematics includes large-sum/floor font encodings whose
    # raw PDF glyph names are extractor-dependent. Every actual printed
    # numeral is checked in order for ALL seven whole formula blocks;
    # exact operators/variables are independently proved from actual TeX.
    native_pdf = text.split('The complete fixed coefficient tuple.', 1)
    need(len(native_pdf) == 2, 'actual PDF complete native section')
    digits = re.sub(r'\D', '', native_pdf[1])
    cursor = 0
    for block in native['blocks']:
        # Poppler emits a large sum's upper limit before its lower limit.
        # This reorders only the already-validated literal sum annotations.
        visible_order = re.sub(r'\\sum_\{([^{}]*)\}\^\{([^{}]*)\}',
                               lambda m: m[2]+m[1], block)
        sig = re.sub(r'\D', '', visible_order)
        pos = digits.find(sig, cursor)
        need(pos >= 0, 'every numeral in a whole actual PDF native formula block')
        cursor = pos+len(sig)
    info = subprocess.run(['pdfinfo', str(path)], check=True, capture_output=True, text=True).stdout
    need(re.search(r'Pages:\s+1\b', info) and '612 x 792' in info, 'actual one Letter page')
    need('Overfull' not in (PAGE/'RENDER.txt').read_text() and 'Overfull' not in (PAGE/'TEX_DIAGNOSTICS.txt').read_text(), 'actual retained PDF has no overfull boxes')
    need(r'\fontsize{9}{9.6}\selectfont' in tex and r'\fontsize{8}{8.8}\selectfont\ttfamily' in tex, 'exact reviewed9pt body and8pt literal recipe')
    need((PAGE/'equation.txt').read_text() == text, 'complete retained extracted PDF text')
    return {'pages': 1, 'paper': 'Letter', 'body_font_pt': 9, 'seed_font_pt': 8,
            'whole_front_symbol_operator_numeral_blocks': True,
            'all_native_formula_numerals_in_order': True,
            'native_operator_glyphs_require_visual_review_in_addition_to_exact_TeX_proof': True,
            'all722_seed_characters_exact': True, 'all62_alphabet_characters_exact': True,
            'no_overfull_boxes': True, 'nonwhite_pdf_characters': len(compact)}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    pins = pin_inputs()
    raw = (PAGE/'polynomial.json').read_bytes()
    need(digest(raw) == GRAPH_SHA and raw == (ROOT/'candidates/norm-tail-sharing/saturated_positive.json').read_bytes(), 'ENTIRE unchanged accepted433 graph')
    graph = json.loads(raw)
    kernels, layout = load(GAP/'data/H2082/kernels.json'), load(GAP/'data/H2082/layout.json')
    need(kernels['ports'] == PORTS, 'all four free kernel ports in exact order')
    tex = (PAGE/'equation.tex').read_text()
    front, native = audit_tex(tex, graph, kernels, layout)
    records = whole_payloads(native['ports'], graph)
    rejected, positive = corruption_controls(tex, graph, kernels, layout)
    pdf = check_pdf(tex, front, native)
    report = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
        'scope': 'Actual printed TeX all40front identities/every464node/all85free-port kernel records; complete original compact54 numeral reconstruction and all11fixed leaves; actual PDF front, full seed/alphabet, all native formula numerals and one-Letter/no-overflow checks. Visual review remains separately required. No parent program or Lean run.',
        'audit_self_sha256': digest(Path(__file__).read_bytes()), 'tool_pins_sha256': digest((PAGE/'TOOL_PINS.json').read_bytes()),
        'whole_graph_sha256': digest(raw), 'domain': 'strictly positive integers', 'variables': VARIABLES,
        'operations': 433, 'operation_breakdown': front['operation_breakdown'], 'exact_degree': 1628768,
        'degree_method': 'Identical whole accepted graph plus exact universal displayed-block identities; inherited global exact degree, not the larger unexpanded DAG bound.',
        'parsed_definitions': front['assignments'], 'whole_literal_nodes_covered': front['covered_nodes'],
        'all_operations_variables_and_fixed_leaves_live': True, 'all85_kernel_records_free_port_exact': True,
        'kernel_supports': front['kernel_supports'], 'all31_weights': front['weights'], 'all22_targets': front['targets'],
        'complete_native_formula_blocks': 7, 'literal_seed_characters': 722, 'literal_seed_sha256': digest(native['seed'].encode()),
        'ordered_alphabet': ALPHABET, 'initializer': [3, 4, 4, 698], 'native_modes': native['mode_count'],
        'support_entries': native['support_count'], 'all_ranks_equal_sorted_order': True,
        'MF_source_shifted_exactly_once': True, 'all_four_entire_reconstructed_ports': records,
        'all11_signed_fixed_leaves_entire_bytes_equal': True, 'no_tuple_transfer': True,
        'rejected_actual_TeX_corruptions': rejected, 'positive_actual_TeX_controls': positive, 'render': pdf,
        'sha256': {n: digest((PAGE/n).read_bytes()) for n in ['equation.tex', 'equation.pdf', 'equation.txt', 'polynomial.json', 'SOURCE_PINS.json', 'FORMULA_MAP.json', 'RENDER.txt', 'TEX_DIAGNOSTICS.txt']},
        'external_pinned_inputs': len(pins['external_files']), 'canonical_page_unchanged': True}
    data = encoded(report)
    if args.output.exists():
        need(args.output.read_bytes() == data, 'refuse changed existing audit receipt')
    else:
        args.output.write_bytes(data)
    print(json.dumps({'status': 'PASS', 'operations': 433, 'degree': 1628768,
          'definitions': len(front['assignments']), 'covered_nodes': front['covered_nodes'],
          'kernel_records': 85, 'rejected_actual_TeX_corruptions': len(rejected), 'pages': 1}, sort_keys=True))


if __name__ == '__main__':
    main()
