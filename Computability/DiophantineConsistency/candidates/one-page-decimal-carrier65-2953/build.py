#!/usr/bin/env python3
"""Build the complete decimal, distinctly named14-variable Carrier65 page."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'candidates/one-page-scaled-clause2953'
CARRIER = ROOT / 'research/carrier65-independent'
PARENT_BUILD_SHA = '31e015b06b249309086dde71c6b74fbd206b413f2a01cd2b29e14ab5cfbc9bb9'
PARENT_TEX_SHA = '7d4976c633dfde72ca368fa5bf0f3e6f0dc8e5c1c32c582acc3ac6b3c7a8ac29'
PARENT_GRAPH_SHA = '26c3c6c836850a8ae8c035604bca02bef904af2e4eda50adeb9439d870a39175'
CARRIER_AUDIT_SHA = '39678e9d35dc1995608a92396e1cfae6e47ac6cfb17a853edbf76e8aa01628a8'
CARRIER_CERT_SHA = '12002fda7018df2b878f7b7f50b864f91fec709df85a7a5225e4b364fa663c48'
CARRIER_PROOF_SHA = '53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749'
CARRIER_GRAPH_SHA = 'bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7'
ALPHABET = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'
SCALAR_NAMES = {'qm': 'b', 'MC': r'\mu', 'MF': r'\omega', 'N0': 'P', 'N1': 'Q',
                'Na': 'U', 'Nt': 'W', 'scaled_Ns': 'Z', 'main_root': 'D', 'normalized_S': 'S'}
FRONT = r'''The only unknowns are
\[
J,F,\alpha,z,f,i,T,s,w,n,\eta,\zeta,y,\gamma\in\mathbb Z_{>0}.
\]
All other symbols in the equation are polynomial abbreviations:
\[
\begin{gathered}
b=\beta J,\quad q=b+1,\quad C=q-F-\alpha,\\
X=wq,\quad Y=sq^3,\quad E=XY,\quad k=\eta+\zeta,\\
\ell=EkY,\quad c=kY+\eta,\quad a=E+Y,\\
H=4a+3,\quad\Delta=a^2+H,\quad D=X+ac+\gamma H,\\
R=[b(q-F)+\alpha](q^2-1)+(\mu+q\omega)J,\\
\tau=En+k-R,\quad V=f^2(cT-R)-c,\\
P=\tau^2-\ell(\ell+k),\quad Q=D^2-\Delta c^2,\\
S=i\Delta c^2,\quad U=S^2(V^2-y^2)+y^2,\\
W=(K+w)C+(q-F)-zb,\quad Z=\Delta f^2-S^2.
\end{gathered}
\]
The single equation is
\[
\boxed{PQUWZ-\Delta=0.}
\]

'''


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def pinned(path, expected):
    raw = path.read_bytes()
    require(sha(raw) == expected, 'Pinned complete input changed: ' + str(path))
    return raw


def record(raw):
    return {'bytes': len(raw), 'sha256': sha(raw)}


def load_module(path, expected, name):
    pinned(path, expected)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Reviewed module specification')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def legacy_integer(text):
    begin = text.index(r'\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily')
    end = text.index(r'\endgroup', begin)
    body = text[begin:end].split('\n', 1)[1]
    seed = ''.join(line.removesuffix(r'\par') for line in body.splitlines())
    require(len(seed) == 436 and all(c in ALPHABET for c in seed), 'Entire inherited encoded integer')
    value = 0
    for digit in seed:
        value = 62 * value + ALPHABET.index(digit)
    return value, seed


def decimal_block(value):
    digits = str(value)
    lines = [digits[j:j + 62] for j in range(0, len(digits), 62)]
    return (r'\textbf{The integer $\mathcal A$ in base 10.}' + '\n'
            + 'Its complete decimal expansion is the concatenation of these lines:\\par\n'
            + r'\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily' + '\n'
            + '\n'.join(line + r'\par' for line in lines) + '\n' + r'\endgroup' + '\n')


def read_decimal(text):
    begin = text.index(r'\textbf{The integer $\mathcal A$ in base 10.}')
    begin = text.index(r'\begingroup\fontsize{7.7}{8.2}\selectfont\ttfamily', begin)
    end = text.index(r'\endgroup', begin)
    body = text[begin:end].split('\n', 1)[1]
    lines = body.splitlines()
    require(lines and all(re.fullmatch(r'[0-9]+\\par', line) for line in lines), 'Every actual printed numeral line is decimal')
    digits = ''.join(line[:-4] for line in lines)
    require(digits[0] != '0', 'Canonical decimal numeral has no leading zero')
    return int(digits, 10), digits


def decode(value):
    def digit(a, base, index):
        return a // base ** index % base
    novelty = value % (1 << 636)
    targets = value // (1 << 636) % (1 << 1675)
    exceptions = value // (1 << 2311)
    actions = []
    sigma = 0
    tau = 0
    for q in range(215):
        mask = digit(novelty, 2, 430 + q)
        field = 14 + mask * (digit(exceptions, 16, tau) - 14)
        for bit in (0, 1):
            j = 2 * q + bit
            fresh = digit(novelty, 2, j)
            target = fresh * (1 + sigma) + (1 - fresh) * digit(targets, 216, j - sigma)
            actions.append((target, digit(field, 2, 2 * bit), digit(field, 2, 2 * bit + 1)))
            sigma += fresh
        tau += mask
    return actions


def page_text(parent_text, value):
    text = parent_text.replace('fifteen-variable', 'fourteen-variable').replace('degree 157; a 66-operation', 'degree 150; a 65-operation')
    begin = text.index('The only unknowns are')
    end = text.index(r'\textbf{The four fixed integers.}', begin)
    text = text[:begin] + FRONT + text[end:]
    text = text.replace('M_C', r'\mu').replace('M_F', r'\omega')
    # Distinct scalar decoder registers; indexed finite families remain indices.
    text = text.replace('T_0', r'\mathcal T').replace('E_0', r'\mathcal E')
    text = text.replace(r'N=\mathcal A', r'\mathcal N=\mathcal A').replace('D_2(N,', r'D_2(\mathcal N,')
    begin = text.index(r'\textbf{The integer $\mathcal A$.}')
    end = text.index(r'\endgroup', begin) + len(r'\endgroup') + 1
    text = text[:begin] + decimal_block(value) + text[end:]
    return text


def check_front(text):
    begin = text.index('The only unknowns are')
    end = text.index(r'\textbf{The four fixed integers.}', begin)
    require(text[begin:end] == FRONT, 'Entire actual distinctly named Carrier65 front')
    require(all(token not in text for token in ('q_-', 'M_C', 'M_F', 'N_0', 'N_1', 'N_a', 'N_k', 'N_t', 'N_s', 'T_0', 'E_0')),
            'No ambiguous subscripted scalar names remain')
    require('alphabet' not in text and '62^' not in text and '436 characters' not in text,
            'Printed encoded integer uses only its decimal expansion')


def materialize():
    parent = load_module(PARENT / 'build.py', PARENT_BUILD_SHA, 'reviewed_scaled2953_page')
    parent_files = parent.materialize()
    require(sha(parent_files['equation.tex']) == PARENT_TEX_SHA and sha(parent_files['polynomial.json']) == PARENT_GRAPH_SHA,
            'Complete parent source and graph reproduced')
    carrier = load_module(CARRIER / 'audit.py', CARRIER_AUDIT_SHA, 'reviewed_carrier65_audit')
    pinned(CARRIER / 'PROOF.md', CARRIER_PROOF_SHA)
    pinned(CARRIER / 'CERTIFICATE.json', CARRIER_CERT_SHA)
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O' if sys.flags.optimize == 1 else '-OO')
    command.append(str(CARRIER / 'audit.py'))
    ran = subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    report = json.loads(ran.stdout)
    require(not ran.stderr and report['status'] == 'PASS' and report['certificate_sha256'] == CARRIER_CERT_SHA,
            'Complete reviewed arithmetic audit reproduced')
    graph = json.loads(pinned(CARRIER / 'INCOMING_CARRIER65.json', CARRIER_GRAPH_SHA))
    old_graph = json.loads(parent_files['polynomial.json'])
    graph_audit = carrier.check_graph(graph, old_graph)
    graph.pop('parent_sha256', None)
    graph['parent_polynomial_sha256'] = PARENT_GRAPH_SHA
    graph['name'] = 'decimal_carrier65_scaled2953_degree150'
    graph['proof'] = 'README.md'
    graph['proof_boundary'] = 'Reviewed Carrier65 positive-zero maps applied to complete scaled2953 native/P66 proof and discharged Pcsc; retained syntactic calibration, no new formal-kernel replay.'
    graph['coefficient_binding'] = old_graph['coefficient_binding']
    graph['arithmetic_proof'] = '../../research/carrier65-independent/PROOF.md'
    graph['arithmetic_proof_sha256'] = CARRIER_PROOF_SHA
    graph['display_scalar_names'] = SCALAR_NAMES

    old_text = parent_files['equation.tex'].decode()
    value, seed = legacy_integer(old_text)
    text = page_text(old_text, value)
    check_front(text)
    actual_value, digits = read_decimal(text)
    require(actual_value == value and str(value) == digits, 'Entire decimal integer equals the inherited integer')
    certificate = json.loads((parent.CERT / 'certificate.json').read_bytes())
    actions = decode(actual_value)
    require(len(actions) == 430 and sha(encoded(actions)) == certificate['recipe_bindings']['actions_sha256'],
            'Every430 action decoded directly from the actual decimal integer')
    # Normalize only the two fixed mask names to the reviewed native source grammar.
    native_text = text.replace(r'\mu', 'M_C').replace(r'\omega', 'M_F')
    tiles = parent.printed_tiles(native_text, actions)
    require(sha(encoded(tiles)) == certificate['recipe_bindings']['tiles_sha256'], 'Every942 actual printed tile from decimal actions')
    scaled = json.loads((parent.CERT / 'coefficients.json').read_bytes())
    support = set(range(951)) | set(range(960, 986)) | {1005}
    parent.validate_printed(native_text, tiles, scaled, support)

    controls = {}
    for name, mutated in [('carrier_sign', text.replace(r'\tau=En+k-R', r'\tau=En+k+R', 1)),
                          ('norm_name', text.replace(r'\boxed{PQUWZ-', r'\boxed{PQUWQ-', 1))]:
        try:
            check_front(mutated)
        except ValueError as error:
            controls[name] = str(error) == 'Entire actual distinctly named Carrier65 front'
        else:
            controls[name] = False
    first = digits[:62]
    changed = ('1' if first[0] != '1' else '2') + first[1:]
    bad = text.replace(first + r'\par', changed + r'\par', 1)
    bad_value, _ = read_decimal(bad)
    require(bad_value != value, 'Actual decimal digit mutation changes the whole integer')
    controls['decimal_digit'] = bad_value != value
    controls['decoder_actions'] = sha(encoded(decode(value + 1))) != certificate['recipe_bindings']['actions_sha256']
    require(all(controls.values()), 'All actual decimal/front corruption controls pass')

    files = {name: raw for name, raw in parent_files.items() if name.startswith('coefficients/')}
    files['equation.tex'] = text.encode()
    files['polynomial.json'] = encoded(graph)
    files['DECIMAL_INTEGER.txt'] = (digits + '\n').encode()
    files['PARENT_BUILD_AUDIT.json'] = parent_files['BUILD_AUDIT.json']
    files['BUILD_AUDIT.json'] = encoded({'schema': 'decimal_carrier65_scaled2953_audit_v1',
        'parent_page_sha256': PARENT_TEX_SHA, 'parent_builder_sha256': PARENT_BUILD_SHA,
        'parent_graph_sha256': PARENT_GRAPH_SHA, 'arithmetic_audit_sha256': CARRIER_AUDIT_SHA,
        'arithmetic_certificate_sha256': CARRIER_CERT_SHA, 'arithmetic_proof_sha256': CARRIER_PROOF_SHA,
        'graph': graph_audit, 'display_scalar_names': SCALAR_NAMES,
        'decimal_digits': len(digits), 'decimal_integer_sha256': sha((digits + '\n').encode()),
        'whole_integer_identical': True, 'all430_decimal_decoded_actions_identical': True,
        'all942_printed_tiles_identical': True, 'all3297_scaled_coefficients_identical': True,
        'all978_physical_positions_identical': True, 'all_four_ports_identical_to_scaled2953': True,
        'raw_constant_bytes': 69449, 'legacy_seed_sha256': sha(seed.encode()),
        'negative_controls': controls,
        'scope': 'Complete decimal numeral and renamed front reconstruction, full literal65 graph and retained four2953 ports; actual rendering is separately reviewed.'})
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    files = materialize()
    closure = dict(files)
    closure['README.md'] = (HERE / 'README.md').read_bytes()
    closure['build.py'] = Path(__file__).read_bytes()
    files['SOURCE_MANIFEST.json'] = encoded({'schema': 'decimal_carrier65_scaled2953_sources_v1',
        'files': {name: record(raw) for name, raw in sorted(closure.items())},
        'native_certificate': 'research/scaled-clause-independent/certificate.json',
        'native_certificate_sha256': '957faf013a17c2e8e04c03be166d903263d2aadaccac604d31f0791e005776ed',
        'arithmetic_certificate': 'research/carrier65-independent/CERTIFICATE.json',
        'arithmetic_certificate_sha256': CARRIER_CERT_SHA,
        'scope': 'Complete deterministic source and integer closure; rendering and ordinary reviews are bound separately.'})
    for name, raw in files.items():
        path = HERE / name
        if args.build:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        else:
            require(path.read_bytes() == raw, 'Deterministic artifact differs: ' + name)
    print(json.dumps({'status': 'PASS', 'variables': 14, 'operations': 65, 'degree': 150,
                      'raw_constant_bytes': 69449, 'tex_bytes': len(files['equation.tex']),
                      'files': {name: sha(raw) for name, raw in files.items()}}, sort_keys=True))


if __name__ == '__main__':
    main()
