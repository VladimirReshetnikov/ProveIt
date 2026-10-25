#!/usr/bin/env python3
"""Held standalone actual-TeX/PDF audit; no project imports or producers.

CODE ONLY/HOLD until two complete static reviews and explicit release.
Local source pins bind the frozen finite source; no project code is imported.
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
PAGE = ROOT/'candidates/one-page-doubled85'
CANON = ROOT/'candidates/one-page-saturated10'
INDEXED = ROOT/'research/indexed-tile-enumeration'
SOURCE = ROOT/'research/ten-positive-doubled-product-square'
MARKER = r'\textbf{The four fixed integers.}'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
INPUTS = ['J', 'F', 'alpha', 'i', 'T', 'w', 'Y', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']
REGISTERS = ['bJ', 'q', 'C', 'X', 'k', 'c', 'mu', 'Am1', 'Hp', 'Delta', 'U',
             'V0', 'V0k', 'Dtau', 'R', 'e', 'Bt', 'DpI2', 'Df', 'Dg',
             'Fsqr', 'Q', 'cTR', 'V', 'Kpos', 'P1', 'Mtot', 'RG', 'Znum', 'N']
ALIASES = {r'q_-': 'bJ', r'\alpha': 'alpha', r'\eta': 'eta', r'\zeta': 'zeta',
           r'\beta': 'beta', r'\mu': 'mu', r'\Delta': 'Delta', r'V_0': 'V0',
           r'\ell': 'V0k', r'B_t': 'Bt', r'K_2': 'Kpos', r'P_1': 'P1',
           r'R_G': 'RG', r'M_C': 'MC', r'M_F': 'MF', 'A': 'Am1', 'H': 'Hp',
           'E': 'Dtau', 'a': 'DpI2', 'D': 'Df', 'G': 'Dg', 'S': 'Fsqr',
           'b': 'cTR', 'K': 'K0', 'M': 'Mtot', 'Z': 'Znum'}
for _name in INPUTS+['q', 'C', 'X', 'k', 'c', 'U', 'R', 'e', 'Q', 'V']:
    ALIASES.setdefault(_name, _name)


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(raw):
    return sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True)+'\n').encode()


def authenticate():
    pins = json.loads((PAGE/'SOURCE_PINS.json').read_bytes())
    for group in ['external_files', 'own_core']:
        for name, pin in pins[group].items():
            data = (ROOT/name).read_bytes()
            need(digest(data) == pin['sha256'] and len(data) == pin['bytes'],
                 'whole reviewed '+group+' '+name)
    required = {str(p.relative_to(ROOT)) for p in [CANON, INDEXED, SOURCE]}
    need({d['folder'] for d in pins['closed_dependencies']} == required,
         'all three complete calibrated parent closures')
    for dep in pins['closed_dependencies']:
        base = ROOT/dep['folder']
        raw = (base/'MANIFEST.json').read_bytes()
        need(digest(raw) == dep['manifest_sha256'], 'exact parent manifest')
        declared = json.loads(raw)['files']
        actual = {str(p.relative_to(base)) for p in base.rglob('*')
                  if p.is_file() and p != base/'MANIFEST.json'}
        need(actual == set(declared), 'complete parent inventory '+dep['folder'])
        for name, entry in declared.items():
            data = (base/name).read_bytes()
            expected = {'sha256': digest(data), 'bytes': len(data)} if isinstance(entry, dict) else digest(data)
            need(entry == expected, 'complete parent member '+name)
    need(pins['ordinary_completeness_premise'] == 'canonical R>3q>=96',
         'explicit shifted-positive-T qualification')
    return pins


def constant(value):
    return {(): value} if value else {}


def variable(name):
    return {(name,): 1}


def add(a, b, sign=1):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, 0)+sign*coefficient
    return {m: c for m, c in out.items() if c}


def multiply(a, b):
    out = {}
    for left, c in a.items():
        for right, d in b.items():
            monomial = tuple(sorted(left+right))
            out[monomial] = out.get(monomial, 0)+c*d
    return {m: c for m, c in out.items() if c}


def power(value, exponent):
    need(type(exponent) is int and exponent >= 0, 'fixed natural exponent')
    out = constant(1)
    for _ in range(exponent):
        out = multiply(out, value)
    return out


def tokens(text):
    result, position = [], 0
    ordered = sorted(ALIASES, key=len, reverse=True)
    while position < len(text):
        char = text[position]
        if char.isspace():
            position += 1
        elif char in '+-*^()[]{}':
            result.append(char)
            position += 1
        elif char.isdigit():
            match = re.match(r'\d+', text[position:])
            result.append(int(match[0]))
            position += len(match[0])
        else:
            name = next((k for k in ordered if text.startswith(k, position)), None)
            need(name is not None, 'entire polynomial TeX token '+text[position:])
            result.append(('variable', ALIASES[name]))
            position += len(name)
    return result


def parse(text, available):
    stream, position = tokens(text), 0

    def expression():
        nonlocal position
        value = product()
        while position < len(stream) and stream[position] in ['+', '-']:
            operator = stream[position]
            position += 1
            value = add(value, product(), 1 if operator == '+' else -1)
        return value

    def product():
        nonlocal position
        value = powered()
        while position < len(stream):
            token = stream[position]
            if token == '*':
                position += 1
                value = multiply(value, powered())
            elif type(token) is int or isinstance(token, tuple) or token in ['(', '[', '{']:
                value = multiply(value, powered())
            else:
                break
        return value

    def powered():
        nonlocal position
        value = primary()
        if position < len(stream) and stream[position] == '^':
            position += 1
            need(position < len(stream), 'complete exponent')
            exponent = stream[position]
            position += 1
            if exponent == '{':
                need(position+1 < len(stream), 'complete braced exponent')
                exponent = stream[position]
                need(stream[position+1] == '}', 'fixed exponent closing brace')
                position += 2
            value = power(value, exponent)
        return value

    def primary():
        nonlocal position
        need(position < len(stream), 'complete polynomial operand')
        token = stream[position]
        position += 1
        if type(token) is int:
            return constant(token)
        if isinstance(token, tuple):
            need(token[1] in available, 'previously proved abbreviation '+token[1])
            return variable(token[1])
        need(token in ['(', '[', '{'], 'group opening')
        value = expression()
        need(position < len(stream) and stream[position] == {'(': ')', '[': ']', '{': '}'}[token],
             'matching polynomial group')
        position += 1
        return value

    value = expression()
    need(position == len(stream), 'entire actual expression consumed')
    return value


def circuit(packet):
    need(packet['witnesses'] == INPUTS and packet['fixed_numerals'] == PORTS,
         'exact positive ten-input four-port signature')
    need(packet['domain'] == 'strictly positive integers' and packet['output'] == 'N', 'domain/output')
    need(packet['transport_weight'] == 'bV', 'lower-degree bV point only')
    rows = packet['source']
    counts = dict(Counter(row[1] for row in rows))
    need(len(rows) == packet['operations'] == 85 and counts == packet['operation_breakdown'] == {'*': 51, '+': 19, '-': 15},
         'complete85-operation inventory')
    definitions, known = {}, set(INPUTS+PORTS)
    degrees = {n: 1 for n in INPUTS} | {n: 0 for n in PORTS}
    for name, op, a, b in rows:
        need(type(name) is str and name not in known and op in ['+', '-', '*'], 'fresh binary gate')
        need(all(type(x) is int or x in known for x in [a, b]), 'strict source topology')
        definitions[name] = (op, a, b)
        da, db = [0 if type(x) is int else degrees[x] for x in [a, b]]
        degrees[name] = da+db if op == '*' else max(da, db)
        known.add(name)
    live, todo = set(), ['N']
    while todo:
        name = todo.pop()
        if type(name) is int or name in live:
            continue
        live.add(name)
        todo.extend(definitions.get(name, ('',))[1:])
    need(live == known, 'every gate/input/port live')
    need(degrees['N'] == packet['exact_degree'] == 328, 'global degree upper bound')
    return definitions, counts


def tex_audit(tex, packet, constant_body, seed):
    need(tex.count(MARKER) == 1 and tex.split(MARKER, 1)[1] == constant_body,
         'complete verbatim constant recipe/table/decoder/seed/footer')
    need(r'J,F,\alpha,i,T,w,Y,n,\eta,\zeta\in\mathbb Z_{>0}.' in tex,
         'actual printed ordered strictly-positive signature')
    need('exact degree 328; an 85-operation evaluator.' in tex, 'printed cost and degree')
    need(r'\fontsize{9}{9.5}\selectfont' in tex and '%%SEED%%' not in tex, 'fixed standalone font/layout')
    block = re.search(r'\\begingroup[^\n]*\\ttfamily\s*(.*?)\\endgroup', constant_body, re.S)
    need(block is not None and re.sub(r'\\par|\s', '', block[1]) == seed,
         'every actual seed character')
    need(len(seed) == 436 and set(seed) <= set(ALPHABET) and constant_body.count(ALPHABET) == 1,
         'complete literal seed and alphabet')
    definitions, counts = circuit(packet)
    front = tex.split('All other symbols in the equation are polynomial abbreviations:', 1)[1].split(MARKER, 1)[0]
    need(front.count(r'\begin{gathered}') == front.count(r'\end{gathered}') == front.count(r'\boxed{') == 1,
         'one complete displayed schedule and equation')
    before, rest = front.split(r'\begin{gathered}', 1)
    math, after = rest.split(r'\end{gathered}', 1)
    need(before.strip() == r'\[', 'no hidden preceding front formula')
    expected_prefix = '\\]\nThe single equation is\n\\[\n\\boxed{'
    need(after.strip().startswith(expected_prefix), 'exact equation display skeleton')
    boxed = after.strip()[len(expected_prefix):]
    depth, stop = 1, None
    for position, char in enumerate(boxed):
        depth += (char == '{')-(char == '}')
        if depth == 0:
            stop = position
            break
    need(stop is not None and boxed[stop+1:].strip() == r'\]', 'complete boxed body, no extra formula')
    box = boxed[:stop]
    clean = math
    for command in [r'\qquad', r'\quad', r'\\']:
        clean = clean.replace(command, ' ')
    available, covered, assignments = set(INPUTS+PORTS), set(), []

    def compare(target, wanted):
        memo = {name: variable(name) for name in available}

        def expand(name):
            if type(name) is int:
                return constant(name)
            if name in memo:
                return memo[name]
            need(name in definitions, 'complete literal source dependency '+name)
            op, a, b = definitions[name]
            covered.add(name)
            left, right = expand(a), expand(b)
            value = multiply(left, right) if op == '*' else add(left, right, 1 if op == '+' else -1)
            memo[name] = value
            return value

        need(expand(target) == wanted, 'exact free-port polynomial cut '+target)

    for statement in clean.split(','):
        statement = statement.strip()
        if not statement:
            continue
        need(statement.count('=') == 1, 'single actual displayed assignment')
        lhs, rhs = statement.split('=')
        left = tokens(lhs.strip())
        need(len(left) == 1 and isinstance(left[0], tuple), 'single literal alias lhs')
        target = left[0][1]
        need(target not in available and target == REGISTERS[len(assignments)], 'exact unique display order')
        text = rhs.strip()
        if text.endswith('.'):
            text = text[:-1]
        compare(target, parse(text, available))
        available.add(target)
        assignments.append({'tex_lhs': lhs.strip(), 'literal_register': target})
    need(len(assignments) == 29 and box.count('=') == 1, 'all29 definitions plus one whole equation')
    lhs, rhs = box.split('=')
    need(rhs == '0.', 'entire output equals zero')
    compare('N', parse(lhs, available))
    need(covered == set(definitions), 'all85 actual source gates covered by proved polynomial cuts')
    return assignments, math, box, counts


def controls(tex, packet, body, seed):
    mutants = [
        ('doubling factor', 'S=1+4aD', 'S=1+2aD'),
        ('undoubled auxiliary base', 'V=Sb-c', 'V=Db-c'),
        ('missing G factor', 'G=ED', 'G=D'),
        ('wrong auxiliary Q', r'Q=4\Delta aD', r'Q=4\Delta a'),
        ('wrong transport weight', 'n-bVB_t', 'n-bB_t'),
        ('transport sign', 'n-bVB_t', 'n+bVB_t'),
        ('wrong final sign', '+(R_G-Z^2)', '-(R_G-Z^2)'),
        ('zero-offset base', r'A=\mu Y(X+1)', r'A=\mu Y(X+1)+1'),
        ('wrong discriminant', r'\Delta=A(A+2)', r'\Delta=A(A+1)'),
        ('changed native initializer', '(3,436,4,4)', '(3,436,4,0)'),
        ('changed printed seed', seed[:10], ('0' if seed[0] != '0' else '1')+seed[1:10]),
        ('wrong printed cost', 'an 85-operation evaluator.', 'an 84-operation evaluator.'),
        ('wrong input domain', r'\mathbb Z_{>0}', r'\mathbb Z_{\ge0}'),
        ('unparsed expression suffix', 'V=Sb-c', 'V=Sb-c!'),
    ]
    rejected = []
    for label, old, new in mutants:
        need(tex.count(old) == 1, 'unique actual TeX mutation '+label)
        try:
            tex_audit(tex.replace(old, new), packet, body, seed)
        except (ValueError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise ValueError('accepted actual TeX mutation '+label)
    positives = [tex.replace('V=Sb-c', 'V=bS-c'), tex.replace('D=1+a', 'D=a+1')]
    for good in positives:
        tex_audit(good, packet, body, seed)
    return rejected, len(positives)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    pins = authenticate()
    packet = json.loads((PAGE/'polynomial.json').read_bytes())
    need((PAGE/'polynomial.json').read_bytes() == (SOURCE/'equation_85.json').read_bytes(), 'whole copied fixed85 polynomial')
    seed = (PAGE/'SEED.txt').read_text().strip()
    need((PAGE/'SEED.txt').read_bytes() == (CANON/'SEED.txt').read_bytes() == (INDEXED/'SEED.txt').read_bytes(),
         'whole jointly calibrated seed file')
    body = (CANON/'equation.tex').read_text().split(MARKER, 1)[1]
    need(body == (INDEXED/'equation.tex').read_text().split(MARKER, 1)[1], 'same whole indexed printed recipe')
    tex = (PAGE/'equation.tex').read_text()
    assignments, math, box, counts = tex_audit(tex, packet, body, seed)
    mapping = json.loads((PAGE/'FORMULA_MAP.json').read_bytes())
    need([(a['tex_lhs'], a['literal_register']) for a in mapping['assignments'][:-1]] ==
         [(a['tex_lhs'], a['literal_register']) for a in assignments], 'entire actual display map')
    need(mapping['assignments'][-1]['literal_register'] == 'N' and mapping['full_polynomial_sha256'] == digest((PAGE/'polynomial.json').read_bytes()),
         'complete mapped final output')
    values = {}
    need(set(packet['coefficient_binding']['ports']) == set(PORTS), 'exact four fixed ports')
    for name, pin in packet['coefficient_binding']['ports'].items():
        blob = (PAGE/'coefficients'/pin['file']).read_bytes()
        need(blob == (CANON/'coefficients'/pin['file']).read_bytes() ==
             (INDEXED/'coefficients'/pin['file']).read_bytes() == (SOURCE/'coefficients'/pin['file']).read_bytes(),
             'whole four-way calibrated compressed payload '+name)
        raw = gzip.decompress(blob)
        values[name] = int.from_bytes(raw, 'little')
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'] and
             values[name].bit_length() == pin['bits'] and len(raw) == (pin['bits']+7)//8,
             'all actual compressed/raw/canonical bytes '+name)
    rejected, positives = controls(tex, packet, body, seed)

    def extract(path):
        return subprocess.run(['pdftotext', '-raw', str(path), '-'], capture_output=True,
                              check=True, text=True, timeout=30).stdout

    pdf, old_pdf = extract(PAGE/'equation.pdf'), extract(CANON/'equation.pdf')
    compact = lambda text: re.sub(r'\s', '', text)
    boundary = 'The four fixed integers.'
    need(pdf.count(boundary) == old_pdf.count(boundary) == 1, 'complete actual PDF constant boundary')
    need(compact(pdf.split(boundary, 1)[1]) == compact(old_pdf.split(boundary, 1)[1]),
         'every actual PDF constant/table/decoder/seed/footer glyph')

    def glyphs(text):
        for old, new in [(r'\qquad', ''), (r'\quad', ''), (r'\\', ''), (r'\alpha', 'α'),
                         (r'\eta', 'η'), (r'\zeta', 'ζ'), (r'\beta', 'β'), (r'\mu', 'µ'),
                         (r'\Delta', '∆'), (r'\ell', 'ℓ')]:
            text = text.replace(old, new)
        return compact(text).replace('_', '').replace('^', '').replace('{', '').replace('}', '').replace('-', '−')

    actual_front = pdf.split('polynomial abbreviations:', 1)[1].split(boundary, 1)[0].replace('The single equation is', '')
    need(compact(actual_front) == glyphs(math+box), 'every rendered front formula glyph in order')
    signature = pdf.split('The only unknowns are', 1)[1].split('All other symbols', 1)[0]
    need(compact(signature) == 'J,F,α,i,T,w,Y,n,η,ζ∈Z>0.', 'every rendered input/domain glyph')
    need('exact degree 328; an 85-operation evaluator.' in pdf, 'actual PDF heading')
    need(seed in compact(pdf) and ALPHABET in compact(pdf), 'every actual seed/alphabet character')
    info = subprocess.run(['pdfinfo', str(PAGE/'equation.pdf')], capture_output=True,
                          check=True, text=True, timeout=30).stdout
    need(re.search(r'Pages:\s+1\b', info) and '612 x 792' in info, 'one actual Letter page')
    need('Overfull' not in (PAGE/'RENDER.txt').read_text() and 'Overfull' not in (PAGE/'TEX_DIAGNOSTICS.txt').read_text(),
         'retained render contains no overfull boxes')
    report = {'status': 'PASS', 'optimized_python': bool(sys.flags.optimize),
              'scope': 'Actual TeX polynomial cuts/all85 gates/four free ports; complete calibrated indexed recipe and actual PDF. Source exact degree and ordinary calibration are inherited from the pinned accepted source, not reproved by a page render.',
              'operations': 85, 'operation_breakdown': counts, 'exact_degree': 328,
              'parsed_definitions': assignments, 'all30_polynomial_cuts_exact': True,
              'all85_literal_gates_covered_and_live': True, 'whole_coherent_ports': packet['coefficient_binding']['ports'],
              'entire_constant_TeX_and_PDF_exact': True, 'all436_seed_characters_exact': True,
              'actual_TeX_mutations_rejected': rejected, 'positive_algebra_controls': positives,
              'actual_pages': 1, 'paper': 'Letter', 'source_pins_sha256': digest((PAGE/'SOURCE_PINS.json').read_bytes()),
              'sha256': {name: digest((PAGE/name).read_bytes()) for name in ['equation.tex', 'equation.pdf', 'polynomial.json', 'FORMULA_MAP.json', 'SEED.txt']},
              'closed_dependencies': pins['closed_dependencies'], 'audit_self_sha256': digest(Path(__file__).read_bytes())}
    raw = encoded(report)
    if args.output.exists():
        need(args.output.read_bytes() == raw, 'refuse changed existing audit receipt')
    else:
        args.output.write_bytes(raw)
    print(raw.decode(), end='')


if __name__ == '__main__':
    main()
