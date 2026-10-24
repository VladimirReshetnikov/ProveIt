#!/usr/bin/env python3
"""Independent actual-TeX/PDF front and whole indexed-constant audit."""
import argparse
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
PAGE = ROOT/'candidates/one-page-uncentered89'
FRONT = ROOT/'research/ten-positive-uncentered-b-weight'
INDEXED = ROOT/'research/indexed-tile-enumeration'
MARKER = r'\textbf{The four fixed integers.}'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
CORE = {
    'zero89.json': '75a40952ea6efa12788963230884c7d2e804fe76f95385ac80c9025aaae76517',
    'PROOF.md': 'd769bc6b43fe34cc9c0d6d14c0f4a5a9baa12c4bfa95ec8a4bb668854c5716b5',
    'INDEXED_BINDING.json': '6317736cbc06179a87d590623c4b951b0165249ce99e23dd295a946331a92a36',
}

def need(ok, why):
    if not ok:
        raise ValueError(why)

def digest(data):
    return sha256(data).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

def sealed(folder, expected=None):
    data = (folder/'MANIFEST.json').read_bytes()
    if expected is not None:
        need(digest(data) == expected, 'exact inherited seal')
    files = json.loads(data)['files']
    need(set(files) == {str(p.relative_to(folder)) for p in folder.rglob('*')
                       if p.is_file() and p != folder/'MANIFEST.json'}, 'closed inherited inventory')
    for n, h in files.items():
        need(digest((folder/n).read_bytes()) == h, 'whole inherited member '+n)
    return digest(data), files

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    for n, h in CORE.items():
        need(digest((FRONT/n).read_bytes()) == h, 'exact reviewed uncentered core '+n)
    indexed_seal, indexed_files = sealed(INDEXED, 'e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84')
    parent_seal, parent_files = sealed(FRONT, 'e4fe2d2e3d502619cfda003341fd08b49efea408ccdd569d3a551c64dd8f7ac0')
    if (PAGE/'MANIFEST.json').exists():
        sealed(PAGE)
    packet = load(FRONT/'zero89.json')
    unknowns = ['J', 'F', 'alpha', 'i', 'T', 'w', 'Y', 'n', 'eta', 'zeta']
    need(packet['witnesses'] == unknowns and packet['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'], 'ten unknowns and four independent fixed ports')
    need(packet['domain'] == 'strictly positive integers' and packet['output'] == 'N', 'whole quantified signature')
    counts = Counter(r[1] for r in packet['source'])
    need(len(packet['source']) == packet['operations'] == 89 and counts == Counter({'*': 53, '+': 19, '-': 17}), 'actual full89-gate inventory')

    # Shared-term algebra uses only exact integer arithmetic and AC for +,*.
    # Subtractions remain ordered nodes: no sampled or guessed identity.
    nodes, interned = [], {}
    def make(value):
        if value not in interned:
            interned[value] = len(nodes)
            nodes.append(value)
        return interned[value]
    def atom(value):
        return make(('integer', value)) if type(value) is int else make(('symbol', value))
    def operation(op, a, b):
        if op == '-':
            return make(('minus', a, b))
        items, constant = [], 0 if op == '+' else 1
        for index in [a, b]:
            parts = nodes[index][1:] if nodes[index][0] == op else [index]
            for q in parts:
                if nodes[q][0] == 'integer':
                    constant = constant+nodes[q][1] if op == '+' else constant*nodes[q][1]
                else:
                    items.append(q)
        if op == '*' and constant == 0:
            return atom(0)
        if constant != (0 if op == '+' else 1) or not items:
            items.append(atom(constant))
        return items[0] if len(items) == 1 else make((op, *sorted(items)))
    def power(a, n):
        need(type(n) is int and n >= 0, 'fixed natural polynomial exponent')
        value = atom(1)
        for _ in range(n):
            value = operation('*', value, a)
        return value
    actual = {n: atom(n) for n in unknowns+packet['fixed_numerals']}
    deps = {}
    for name, op, a, b in packet['source']:
        need(name not in actual and op in ['+', '-', '*'], 'fresh binary source node')
        need(all(type(x) is int or x in actual for x in [a, b]), 'source topological order')
        actual[name] = operation(op, atom(a) if type(a) is int else actual[a], atom(b) if type(b) is int else actual[b])
        deps[name] = [x for x in [a, b] if type(x) is not int]
    live, todo = set(), [packet['output']]
    while todo:
        n = todo.pop()
        if n not in live:
            live.add(n)
            todo.extend(deps.get(n, []))
    need(live == set(actual), 'all89 gates, ten inputs and four fixed ports live')

    alias = {r'q_-': 'bJ', r'\alpha': 'alpha', r'\eta': 'eta', r'\zeta': 'zeta', r'\beta': 'beta',
             r'\mu': 'mu', r'\Delta': 'Delta', r'\delta': 'delta', r'V_0': 'V0', r'\ell': 'V0k',
             r'B_t': 'Bt', r'D_f': 'Df', r'D_y': 'Dnum', r'K_2': 'Kpos', r'P_1': 'P1',
             r'A_g': 'fg', r'A_y': 'fy', r'M_C': 'MC', r'M_F': 'MF',
             "T'": 'Tp', r'T\prime': 'Tp', "b'": 'cTR', 'A': 'Am1', 'H': 'Hp',
             'E': 'Dtau', 'K': 'K0', 'M': 'Mtot', 'Z': 'Znum', 'S': 'fs'}
    for n in unknowns+['q', 'C', 'X', 'k', 'c', 'U', 'R', 'e', 'Q', 'V']:
        alias.setdefault(n, n)
    ordered = sorted(alias, key=len, reverse=True)
    def tokens(text):
        result, pos = [], 0
        while pos < len(text):
            c = text[pos]
            if c.isspace():
                pos += 1
            elif c in '+-*^()[]{}':
                result.append(c)
                pos += 1
            elif c.isdigit():
                match = re.match(r'\d+', text[pos:])
                result.append(int(match[0]))
                pos += len(match[0])
            else:
                key = next((k for k in ordered if text.startswith(k, pos)), None)
                need(key is not None, 'entire TeX token '+text[pos:])
                result.append(('variable', alias[key]))
                pos += len(key)
        return result
    def tex_audit(tex, constant_body, seed):
        need(tex.count(MARKER) == 1 and tex.split(MARKER, 1)[1] == constant_body, 'complete verbatim indexed constant body')
        need('%%SEED%%' not in tex and len(seed) == 436 and set(seed) <= set(ALPHABET), 'literal full436-character seed, no template slot')
        need(r'J,F,\alpha,i,T,w,Y,n,\eta,\zeta\in\mathbb Z_{>0}' in tex, 'printed strictly positive ordered signature')
        need('exact degree 288; an 89-operation evaluator.' in tex, 'actual printed degree and cost')
        printed = {n: atom(n) for n in unknowns+packet['fixed_numerals']}
        def parse(text):
            ts, pos = tokens(text), 0
            def expression():
                nonlocal pos
                a = product()
                while pos < len(ts) and ts[pos] in ['+', '-']:
                    op = ts[pos]
                    pos += 1
                    a = operation(op, a, product())
                return a
            def product():
                nonlocal pos
                a = powered()
                while pos < len(ts):
                    t = ts[pos]
                    if t == '*':
                        pos += 1
                        a = operation('*', a, powered())
                    elif type(t) is int or isinstance(t, tuple) or t in ['(', '[', '{']:
                        a = operation('*', a, powered())
                    else:
                        break
                return a
            def powered():
                nonlocal pos
                a = primary()
                if pos < len(ts) and ts[pos] == '^':
                    pos += 1
                    n = ts[pos]
                    pos += 1
                    if n == '{':
                        n = ts[pos]
                        pos += 1
                        need(ts[pos] == '}', 'fixed exponent closing brace')
                        pos += 1
                    a = power(a, n)
                return a
            def primary():
                nonlocal pos
                need(pos < len(ts), 'complete polynomial operand')
                t = ts[pos]
                pos += 1
                if type(t) is int:
                    return atom(t)
                if isinstance(t, tuple):
                    need(t[1] in printed, 'prior printed abbreviation '+t[1])
                    return printed[t[1]]
                need(t in ['(', '[', '{'], 'group opening')
                a = expression()
                need(ts[pos] == {'(': ')', '[': ']', '{': '}'}[t], 'matching group')
                pos += 1
                return a
            value = expression()
            need(pos == len(ts), 'entire actual expression parsed')
            return value
        front = tex.split('All other symbols in the equation are polynomial abbreviations:', 1)[1].split(MARKER, 1)[0]
        math = front.split(r'\begin{gathered}', 1)[1].split(r'\end{gathered}', 1)[0]
        clean = math
        for command in [r'\qquad', r'\quad', r'\\']:
            clean = clean.replace(command, ' ')
        assignments = []
        for statement in clean.split(','):
            if not statement.strip():
                continue
            need(statement.count('=') == 1, 'single displayed assignment')
            lhs, rhs = statement.split('=')
            left = tokens(lhs.strip())
            need(len(left) == 1 and isinstance(left[0], tuple), 'single lhs alias')
            name = left[0][1]
            need(name in actual and name not in printed, 'unique complete alias '+name)
            value = parse(rhs.strip().removesuffix('.'))
            need(value == actual[name], 'actual displayed definition equals literal register '+name)
            printed[name] = value
            assignments.append(dict(tex_lhs=lhs.strip(), literal_register=name))
        box = front.split(r'\boxed{', 1)[1].split('}', 1)[0]
        lhs, rhs = box.split('=')
        need(rhs == '0.' and parse(lhs) == actual['N'], 'entire boxed polynomial equals complete89-gate output')
        return assignments, math, box

    tex = (PAGE/'equation.tex').read_text()
    template = (PAGE/'equation-template.tex').read_text()
    need(tex == template, 'complete actual TeX equals full literal template')
    indexed_tex = (INDEXED/'equation.tex').read_text()
    need(indexed_tex.count(MARKER) == 1, 'sealed indexed body marker')
    body = indexed_tex.split(MARKER, 1)[1]
    seed = (INDEXED/'SEED.txt').read_text().strip()
    need((PAGE/'SEED.txt').read_bytes() == (INDEXED/'SEED.txt').read_bytes(), 'whole copied seed file')
    block = re.search(r'\\begingroup[^\n]*\\ttfamily\s*(.*?)\\endgroup', body, flags=re.S)
    need(block is not None, 'actual literal seed block')
    literal_seed = re.sub(r'\\par|\s', '', block[1])
    need(literal_seed == seed and body.count(ALPHABET) == 1, 'all printed seed and alphabet characters')
    assignments, math, box = tex_audit(tex, body, seed)
    need(len(assignments) == 31, 'all31 actual displayed definitions')

    # Actual TeX mutations are fed through the SAME complete parser/body check.
    mutations = [
        ('missing saturation factor', r'D_f=1+\Delta U^2E', r'D_f=1+\Delta U^2'),
        ('restored unlicensed center', "n+V-b'B_t", "n+V+E-b'B_t"),
        ('old transport weight', "n+V-b'B_t", r'n+V-kB_t'),
        ('zero-offset A changed', r'A=\mu Y(X+1)', r'A=\mu Y(X+1)+1'),
        ('wrong discriminant', r'\Delta=A(A+2)', r'\Delta=A(A+1)'),
        ('wrong strong auxiliary modulus', r'Q=\Delta^2U^2E', r'Q=\Delta U^2E'),
        ('transport sign', "n+V-b'B_t", "n+V+b'B_t"),
        ('wrong norm sign', r'[S-(A_g+A_y)]^2-4A_gA_y', r'[S-(A_g+A_y)]^2+4A_gA_y'),
        ('wrong native initializer', '(3,436,4,4)', '(3,436,4,0)'),
        ('changed actual seed', seed[:10], ('0' if seed[0] != '0' else '1')+seed[1:10]),
        ('printed operation count', 'an 89-operation evaluator.', 'a 91-operation evaluator.'),
        ('printed exact degree', 'exact degree 288;', 'exact degree 287;'),
        ('printed input domain', r'\mathbb Z_{>0}', r'\mathbb Z_{\ge0}'),
    ]
    rejected = []
    for label, old, new in mutations:
        need(tex.count(old) == 1, 'unique real TeX corruption site '+label)
        bad = tex.replace(old, new)
        try:
            tex_audit(bad, body, seed)
        except (ValueError, IndexError):
            rejected.append(label)
        else:
            raise ValueError('accepted actual printed corruption '+label)

    binding = load(FRONT/'INDEXED_BINDING.json')
    expected_binding = deepcopy(load(INDEXED/'coefficients/BINDING.json'))
    expected_binding['path'] = 'coefficients/indexed_bfs/'
    need(binding == expected_binding, 'whole separately calibrated indexed binding')
    values = {}
    for name, pin in binding['ports'].items():
        blob = (PAGE/'coefficients'/pin['file']).read_bytes()
        need(blob == (FRONT/'coefficients/indexed_bfs'/pin['file']).read_bytes() == (INDEXED/'coefficients'/pin['file']).read_bytes(), 'entire jointly transferred payload '+name)
        raw = gzip.decompress(blob)
        values[name] = int.from_bytes(raw, 'little')
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'] and values[name].bit_length() == pin['bits'] and len(raw) == (values[name].bit_length()+7)//8, 'all canonical compressed/raw bytes and bits '+name)
    beta = values['beta']
    need(beta >= 31 and beta % 2 == 1 and values['K0'] > 0 and 0 < values['MC'] < beta < values['MF'] < 2*beta, 'uniform four-port theorem box')
    need((PAGE/'parent-polynomial.json').read_bytes() == (FRONT/'zero89.json').read_bytes(), 'complete frozen primary parent graph')
    expected = deepcopy(packet)
    expected.update(name='one_page_uncentered_b_indexed_bfs_degree288', proof='../../research/ten-positive-uncentered-b-weight/PROOF.md', parent_sha256=digest((FRONT/'zero89.json').read_bytes()), parent_manifest_sha256=parent_seal, proof_status='Complete ordinary coefficient-uniform uncentered theorem at the whole indexed tuple; no canonical promotion.')
    expected['coefficient_binding'] = deepcopy(binding)
    expected['coefficient_binding']['path'] = 'coefficients/'
    need(load(PAGE/'polynomial.json') == expected, 'ENTIRE page graph and whole coherent tuple specialization')

    # Independent extraction checks all actual front glyphs in order and the
    # WHOLE constant/table/decoder/seed/footer text against its sealed PDF.
    def extracted(path):
        return subprocess.run(['pdftotext', '-raw', str(path), '-'], check=True, capture_output=True, text=True).stdout
    pdf = extracted(PAGE/'equation.pdf')
    old_pdf = extracted(INDEXED/'equation.pdf')
    def pdf_norm(s):
        return re.sub(r'\s', '', s).replace('-', '').replace('‐', '')
    text_marker = 'The four fixed integers.'
    need(pdf.count(text_marker) == old_pdf.count(text_marker) == 1, 'complete PDF constant boundary')
    need(pdf_norm(pdf.split(text_marker, 1)[1]) == pdf_norm(old_pdf.split(text_marker, 1)[1]), 'ALL actual PDF constants, tile table, decoder, full seed and footer')
    def math_glyphs(s):
        for old, new in [(r'\qquad', ''), (r'\quad', ''), (r'\\', ''), (r'\alpha', 'α'), (r'\eta', 'η'), (r'\zeta', 'ζ'), (r'\beta', 'β'), (r'\mu', 'µ'), (r'\Delta', '∆'), (r'\delta', 'δ'), (r'\ell', 'ℓ')]:
            s = s.replace(old, new)
        return re.sub(r'\s', '', s).replace('_', '').replace('^', '').replace('{', '').replace('}', '').replace("'", '′').replace('-', '−')
    pdf_front = pdf.split('polynomial abbreviations:', 1)[1].split(text_marker, 1)[0].replace('The single equation is', '')
    need(re.sub(r'\s', '', pdf_front) == math_glyphs(math+box), 'EVERY actual rendered front formula glyph in exact order')
    signature = pdf.split('The only unknowns are', 1)[1].split('All other symbols', 1)[0]
    need(re.sub(r'\s', '', signature) == 'J,F,α,i,T,w,Y,n,η,ζ∈Z>0.', 'actual PDF positive input signature')
    need('exact degree 288; an 89-operation evaluator.' in pdf, 'actual PDF metric heading')
    need(len(re.sub(r'\s', '', pdf)) == 3111, 'actual full-page3111-character census')
    need(seed in re.sub(r'\s', '', pdf) and ALPHABET in pdf, 'whole actual PDF literal seed and alphabet')
    info = subprocess.run(['pdfinfo', str(PAGE/'equation.pdf')], check=True, capture_output=True, text=True).stdout
    need(re.search(r'Pages:\s+1\b', info) and '612 x 792' in info, 'actual one Letter page')
    need('Overfull' not in (PAGE/'RENDER.txt').read_text(), 'retained render has no overfull boxes')

    pins = load(PAGE/'SOURCE_PINS.json')
    need(pins['parent_manifest_sha256'] == parent_seal and pins['complete_parent_files'] == parent_files, 'whole rendered parent seal')
    need(pins['indexed_manifest_sha256'] == indexed_seal and pins['complete_indexed_files'] == indexed_files, 'whole rendered indexed seal')
    need(pins['renderer_sha256'] == digest((ROOT/'tools/render_uncentered89_page.py').read_bytes()) and pins['ordinary_proof_sha256'] == CORE['PROOF.md'] and pins['indexed_proof_sha256'] == digest((INDEXED/'PROOF.md').read_bytes()), 'whole renderer and ordinary/native proof pins')
    need(pins['constant_body_sha256'] == digest(body.encode()), 'whole constant-body pin')
    for name, h in pins['copied_files'].items():
        need(digest((PAGE/name).read_bytes()) == h, 'entire copied page member '+name)
    report = dict(status='PASS', optimized_python=bool(sys.flags.optimize), audit_self_sha256=digest(Path(__file__).read_bytes()),
        scope='Independent ACTUAL TeX parser, all89 free-port gates, whole printed PDF front and constants, complete indexed tuple and page graph; no renderer/source-producer imports, no new ordinary or Lean theorem.',
        parsed_definitions=assignments, complete_output_matches=True, all89_gates_live=True, operations=89,
        operation_breakdown=dict(counts), exact_degree=288, actual_pdf_front_glyphs_exact=True,
        entire_indexed_constant_body_verbatim=True, entire_pdf_constant_body_exact=True,
        complete_literal_seed_characters=436, literal_seed_sha256=digest(seed.encode()), ordered_alphabet=ALPHABET,
        whole_payload_ports=binding['ports'], parent_manifest_sha256=parent_seal, indexed_manifest_sha256=indexed_seal,
        new_specialized_polynomial_is_not_identified_with_old_K_instance=True,
        rejected_actual_printed_corruptions=rejected, actual_pages=1, paper='Letter',
        nonwhite_pdf_characters=len(re.sub(r'\s', '', pdf)),
        sha256={str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in [PAGE/'equation-template.tex', PAGE/'equation.tex', PAGE/'equation.pdf', PAGE/'README.md', PAGE/'polynomial.json', PAGE/'parent-polynomial.json', PAGE/'SOURCE_PINS.json', PAGE/'SEED.txt', ROOT/'tools/render_uncentered89_page.py', FRONT/'PROOF.md', FRONT/'zero89.json', FRONT/'INDEXED_BINDING.json', INDEXED/'equation.tex', INDEXED/'equation.pdf']})
    data = (json.dumps(report, indent=2, sort_keys=True)+'\n').encode()
    if args.output.exists():
        need(args.output.read_bytes() == data, 'refuse changed existing peer receipt')
    else:
        args.output.write_bytes(data)
    print(json.dumps(dict(status='PASS', operations=89, exact_degree=288, parsed_definitions=len(assignments), actual_pdf_front_and_constants_exact=True, rejected_actual_printed_corruptions=len(rejected)), sort_keys=True))

if __name__ == '__main__':
    main()
