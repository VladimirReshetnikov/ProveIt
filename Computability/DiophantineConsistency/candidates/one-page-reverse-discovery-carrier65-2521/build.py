#!/usr/bin/env python3
"""Build and audit the complete decimal reverse-discovery Carrier65 page at2521."""
import argparse
import gzip
import hashlib
import importlib.util
import json
from math import prod
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'candidates/one-page-reversed-carrier65-2521'
SEED = ROOT / 'research/reverse-discovery-decimal-seed'
PARENT_BUILD_SHA = 'be6022b1657bb883045f2bb9f42f6fbe57c2889be4694078fade07e3a912fbf7'
PARENT_TEX_SHA = 'a8a09cbff448e4da1788aba2d0fc37850df27c0f3bf4eb692cabeb336f6c48c6'
PARENT_GRAPH_SHA = '408dde55352b837db3c606db446f3bf41dc7fd6d9242808ba4a123930bf0b5ff'
PARENT_PDF_SHA = '8a125b25a4ea2fafdd206b216d3e575153fffe556f5ac769a8816dfb23ed9d2d'
PARENT_TEXT_SHA = '44649d2e4f23863a2d0ea1163aa4236a88496933c03f1f1c58019578718d7a22'
SEED_AUDIT_SHA = '5e1ccfd248d1d521f8a847a37d74468252dd896e8025164e9fd4b699c9948bb9'
SEED_PROOF_SHA = '7ae325c52d69c718266aee8ec116a29ca50353cf3edf20bd15c3abf73f0286c0'
SEED_CERT_SHA = '87c1cc8d349b0472e4917ab9517cb7b907db0d34ce877d321331976cace161af'
NEW_DECIMAL_SHA = '313907d4b38e5d620d85b66f849368960d796ca6e442a8ee6b396c7d67d5a8a7'
DECODER_START = r'\textbf{A closed decoder for the 430 actions.}'
DECIMAL_START = r'\textbf{The integer $\mathcal A$ in base 10.}'
PARAMETERS = {'nu_end': 430, 'prefix_end': 430, 'states': 215,
              'mask_bits': 636, 'payload_bits': 636, 'radix_add': 2,
              'sigma_lower': 0, 'sigma_shift': 1, 'prefix_lower': 0, 'prefix_shift': 1,
              'mark_offset': 430, 'flag_endpoint': 430, 'outer': r'\bmod216'}
DECODER_TEMPLATE = r'''\textbf{A closed decoder for the 430 actions.}
Put $D_b(A,k)=\fl{A/b^k}\bmod b$, where
$a\bmod b=a-b\fl{a/b}$. For $0\le q<@states@$, $b=0,1$, $j=2q+b$:
\[
\begin{gathered}
\mathcal N=\mathcal A\bmod2^{@mask_bits@},\quad
\mathcal T=\fl{\mathcal A/2^{@payload_bits@}},\\
\nu_j=D_2(\mathcal N,j),\quad \kappa_j=(\sigma_j+@radix_add@)^{1-\nu_j}\quad(0\le j<@nu_end@),\\
\sigma_j=\sum_{k=@sigma_lower@}^{j-@sigma_shift@}\nu_k,\quad
\Pi_j=\prod_{k=@prefix_lower@}^{j-@prefix_shift@}\kappa_k\quad(0\le j\le@prefix_end@),\\
m_q=D_2(\mathcal N,@mark_offset@+q),\quad \tau_q=\sum_{k=0}^{q-1}m_k,\\
F_q=14+m_q(D_{16}(\fl{\mathcal T/\Pi_{@flag_endpoint@}},\tau_q)-14),\\
u_j=(\sigma_{j+1}-(\fl{\mathcal T/\Pi_j}\bmod\kappa_j))@outer@,\\
v_j=D_2(F_q,2b),\quad d_j=D_2(F_q,2b+1).
\end{gathered}
\]
Empty sums/products are $0/1$. Here $(v_0,d_0,u_0)=(1,1,1)$; the constructor tile
uses this actual first target, including its state renaming.

'''


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def record(raw):
    return {'bytes': len(raw), 'sha256': sha(raw)}


def pinned(path, digest):
    raw = path.read_bytes()
    require(sha(raw) == digest, 'Exact frozen input: ' + str(path))
    return raw


def load(path, digest, name):
    pinned(path, digest)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Reviewed module specification')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def decoder_block():
    block = DECODER_TEMPLATE
    for name, value in PARAMETERS.items():
        require(block.count('@' + name + '@') == 1, 'Unique decoder parameter token')
        block = block.replace('@' + name + '@', str(value))
    require('@' not in block, 'No unresolved printed decoder parameter')
    return block


def replace_decimal(text, value, decimal_language):
    begin = text.index(DECIMAL_START)
    end = text.index(r'\endgroup', begin) + len(r'\endgroup') + 1
    return text[:begin] + decimal_language.decimal_block(value) + text[end:]


def page_text(parent_text, value, decimal_language):
    begin = parent_text.index(DECODER_START)
    end = parent_text.index(DECIMAL_START, begin)
    text = parent_text[:begin] + decoder_block() + parent_text[end:]
    return replace_decimal(text, value, decimal_language)


def printed_decode(text, decimal_language):
    """Interpret the actual complete narrow printed grammar and its parameters."""
    begin = text.index(DECODER_START)
    end = text.index(DECIMAL_START, begin)
    pattern = re.escape(DECODER_TEMPLATE)
    for name in PARAMETERS:
        token = re.escape('@' + name + '@')
        replacement = r'(?P<outer>\\bmod[0-9]+)?' if name == 'outer' else '(?P<' + name + '>[0-9]+)'
        pattern = pattern.replace(token, replacement)
    match = re.fullmatch(pattern, text[begin:end])
    require(match is not None, 'Entire actual reverse-discovery decoder grammar')
    p = {name: int(match[name]) for name in PARAMETERS if name != 'outer'}
    p['outer'] = match['outer'] or ''
    require(p['nu_end'] == 430 and p['prefix_end'] == 430 and p['states'] == 215,
            'Explicit full domains for nu/kappa and sigma/Pi, including endpoint430')
    require(0 < p['mask_bits'] < 700 and 0 < p['payload_bits'] < 700
            and 0 < p['radix_add'] < 10 and 0 <= p['sigma_lower'] < 430
            and 0 <= p['prefix_lower'] < 430 and 1 <= p['sigma_shift'] <= 430
            and 1 <= p['prefix_shift'] <= 430 and 0 <= p['flag_endpoint'] <= p['prefix_end'],
            'Finite printed decoder parameter domains')
    value, digits = decimal_language.read_decimal(text)
    n, payload = value % (1 << p['mask_bits']), value // (1 << p['payload_bits'])
    nu = [(n >> j) & 1 for j in range(p['nu_end'])]
    sigma = [sum(nu[p['sigma_lower']:max(p['sigma_lower'], j-p['sigma_shift']+1)])
             for j in range(p['prefix_end']+1)]
    kappa = [(sigma[j]+p['radix_add']) ** (1-nu[j]) for j in range(p['nu_end'])]
    prefixes = [prod(kappa[p['prefix_lower']:max(p['prefix_lower'], j-p['prefix_shift']+1)])
                for j in range(p['prefix_end']+1)]
    exceptions = payload // prefixes[p['flag_endpoint']]
    actions, flags, tau = [], [], 0
    for q in range(p['states']):
        mark = (n >> (p['mark_offset']+q)) & 1
        flag = 14 + mark * (((exceptions // 16 ** tau) % 16)-14)
        flags.append(flag)
        tau += mark
        for b in (0, 1):
            j = 2*q+b
            target = sigma[j+1] - ((payload // prefixes[j]) % kappa[j])
            if p['outer']:
                modulus = int(p['outer'][len(r'\bmod'):])
                require(modulus > 0, 'Positive actual outer target modulus')
                target %= modulus
            actions.append((target, (flag >> (2*b)) & 1, (flag >> (2*b+1)) & 1))
    return actions, {'parameters': p, 'decimal_digits': digits, 'decimal_value': value,
                     'all_sigma': sigma, 'all_radices': kappa, 'all_prefixes': prefixes, 'flags': flags}


def materialize():
    parent = load(PARENT / 'build.py', PARENT_BUILD_SHA, 'reviewed_complete_reversed2521_page')
    parent_files = parent.materialize()
    require(sha(parent_files['equation.tex']) == PARENT_TEX_SHA
            and sha(parent_files['polynomial.json']) == PARENT_GRAPH_SHA, 'Whole frozen complete parent reproduced')
    decimal_language = parent.load_module(parent.PARENT / 'build.py', parent.PARENT_BUILD_SHA, 'reviewed_decimal_grammar')
    language = decimal_language.load_module(decimal_language.PARENT / 'build.py', decimal_language.PARENT_BUILD_SHA,
                                            'reviewed_whole_tile_grammar')
    seed = load(SEED / 'audit.py', SEED_AUDIT_SHA, 'reviewed_reverse_discovery_identity')
    pinned(SEED / 'PROOF.md', SEED_PROOF_SHA)
    receipt = json.loads(pinned(SEED / 'CERTIFICATE.json', SEED_CERT_SHA))
    decimal = pinned(SEED / 'DECIMAL_INTEGER.txt', NEW_DECIMAL_SHA)
    command = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else []) + [str(SEED / 'audit.py')]
    ran = subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(not ran.stderr and json.loads(ran.stdout)['certificate_sha256'] == SEED_CERT_SHA,
            'Entire independent seed identity receipt reproduced')
    verifier = parent.load_module(parent.NATIVE / 'certify.py', parent.VERIFIER_SHA, 'reviewed_complete2521_native')
    _, _, expected_actions, tiles, c, support = verifier.model()
    canonical, _ = verifier.constants(c, support)
    parent_text = parent_files['equation.tex'].decode()
    text = page_text(parent_text, seed.decimal(decimal), decimal_language)
    decimal_language.check_front(text)
    decoded, actual = printed_decode(text, decimal_language)
    require(decoded == expected_actions and sha(encoded(decoded)) == receipt['packing']['actions_sha256'],
            'All430 actions directly from the actual printed decoder and715 decimal digits')
    require((actual['decimal_digits']+'\n').encode() == decimal and len(actual['decimal_digits']) == 715,
            'Every actual715 printed decimal digit equals the independently derived integer')
    require(actual['parameters'] == PARAMETERS and actual['all_sigma'][-1] == 214
            and actual['all_prefixes'][-1] == int(receipt['packing']['P430']), 'All actual printed prefix parameters and endpoints')
    require(actual['flags'] == seed.new_decode(actual['decimal_value'])['flags'], 'All actual printed flag nibbles')
    printed, physical, base_c, permutation = parent.printed_recipe(text, decoded, language, c, support, tiles)
    require(printed == canonical and len(tiles) == 942 and len(base_c) == 3297 and sum(physical) == 978,
            'Complete actual printed table, permutation, arrays and all four whole integers')
    # Restore only the changed decoder and numeral; every other source byte must match.
    a, b = text.index(DECODER_START), text.index(DECIMAL_START)
    old_a, old_b = parent_text.index(DECODER_START), parent_text.index(DECIMAL_START)
    restored = text[:a] + parent_text[old_a:old_b] + text[b:]
    old_value, _ = decimal_language.read_decimal(parent_text)
    require(replace_decimal(restored, old_value, decimal_language) == parent_text,
            'Fonts, entire front, abstract table, permutation and every fixed-integer recipe unchanged')

    mutations = {
        'radix_addend': text.replace(r'(\sigma_j+2)^{1-\nu_j}', r'(\sigma_j+3)^{1-\nu_j}', 1),
        'prefix_upper_bound': text.replace(r'\prod_{k=0}^{j-1}\kappa_k', r'\prod_{k=0}^{j-2}\kappa_k', 1),
        'prefix_endpoint_domain': text.replace(r'\quad(0\le j\le430)', r'\quad(0\le j\le429)', 1),
        'sigma_endpoint_domain': text.replace(r'\quad(0\le j\le430)', r'\quad(0\le j<430)', 1),
        'outer_modulus': text.replace(r'))\bmod216,', r'))\bmod215,', 1),
        'outer_modulo_omission': text.replace(r'))\bmod216,', r')),', 1),
        'target_parentheses': text.replace(r'-(\fl{\mathcal T/\Pi_j}\bmod\kappa_j)', r'-\fl{\mathcal T/\Pi_j}\bmod\kappa_j', 1),
        'exception_prefix_endpoint': text.replace(r'\Pi_{430}', r'\Pi_{429}', 1),
    }
    digits = actual['decimal_digits']
    for name, position in (('decimal_first', 0), ('decimal_middle', len(digits)//2), ('decimal_last', len(digits)-1)):
        replacement = '1' if digits[position] != '1' else '2'
        bad_digits = digits[:position] + replacement + digits[position+1:]
        mutations[name] = replace_decimal(text, int(bad_digits), decimal_language)
    controls = {}
    for name, corrupted in mutations.items():
        require(corrupted != text, 'Actual complete source corruption occurred: ' + name)
        try:
            bad, _ = printed_decode(corrupted, decimal_language)
        except ValueError as error:
            controls[name] = {'rejection': 'printed grammar/domain', 'detail': str(error)}
        else:
            differences = [j for j in range(430) if bad[j] != decoded[j]]
            require(differences, 'Actual mutated printed decoder changed an action: ' + name)
            j = differences[0]
            controls[name] = {'rejection': 'actual decoded actions', 'changed_actions': len(differences),
                              'first_action': j, 'expected': decoded[j], 'actual': bad[j]}
    require(controls['outer_modulo_omission']['first_action'] == 125
            and controls['outer_modulo_omission']['changed_actions'] == 1
            and controls['outer_modulo_omission']['actual'][0] == -1, 'Actual printed halt125 outer-modulo control')

    files = {name: raw for name, raw in parent_files.items() if name.startswith('coefficients/')}
    graph_raw = parent_files['polynomial.json']
    graph = json.loads(graph_raw)
    require(graph['operations'] == 65 and graph['exact_degree'] == 150 and len(graph['witnesses']) == 14,
            'Complete unchanged Carrier65 graph')
    for graph_name, name in (('beta', 'beta'), ('K0', 'K'), ('MC', 'MC'), ('MF', 'MF_source')):
        binding = graph['coefficient_binding']['ports'][graph_name]
        raw = gzip.decompress(files['coefficients/' + binding['file']])
        require(int.from_bytes(raw, 'big') == printed[name] and sha(raw) == binding['raw_sha256'],
                'Entire materialized integer equals actual printed recipe: ' + name)
    beta, K, MC, MF = (printed[key] for key in ('beta', 'K', 'MC', 'MF_source'))
    require(beta >= 31 and K > 0 and 0 < MC < beta < MF < 2*beta, 'Unchanged complete Carrier65 scalar interface')
    files['equation.tex'] = text.encode()
    files['polynomial.json'] = graph_raw
    files['DECIMAL_INTEGER.txt'] = decimal
    files['BUILD_AUDIT.json'] = encoded({
        'schema': 'reverse_discovery_decimal2521_complete_source_audit_v1',
        'parent_builder_sha256': PARENT_BUILD_SHA, 'parent_page_sha256': PARENT_TEX_SHA,
        'parent_graph_sha256': PARENT_GRAPH_SHA, 'seed_audit_sha256': SEED_AUDIT_SHA,
        'seed_proof_sha256': SEED_PROOF_SHA, 'seed_certificate_sha256': SEED_CERT_SHA,
        'actual_printed_decoder_parameters': actual['parameters'],
        'all715_decimal_digits_sha256': sha(decimal), 'all430_actions_sha256': sha(encoded(decoded)),
        'all942_physical_tiles_sha256': sha(encoded(tiles)), 'all3297_base_coefficients_sha256': sha(encoded(base_c)),
        'all978_physical_positions_sha256': sha(encoded(physical)), 'actual_permutation_sha256': sha(encoded(permutation)),
        'all_four_whole_ports_unchanged': True, 'whole_polynomial_json_byte_identical': True,
        'all_source_outside_decoder_and_numeral_byte_identical': True,
        'raw_integer_bytes': 59297, 'gzip_integer_bytes': sum(len(raw) for name, raw in files.items() if name.startswith('coefficients/')),
        'variables': 14, 'operations': 65, 'degree': 150, 'carrier_scalar_hypotheses': True,
        'actual_complete_source_corruption_controls': controls,
        'scope': 'A narrow complete TeX grammar is interpreted, including parsed radix/prefix/modulus parameters; no arbitrary-TeX parser claim.'})
    return files


def render():
    with tempfile.TemporaryDirectory(prefix='reverse-discovery2521-render-') as temporary:
        directory = Path(temporary)
        shutil.copyfile(HERE / 'equation.tex', directory / 'equation.tex')
        ran = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'equation.tex'],
                             cwd=directory, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require(not ran.stderr, 'No TeX stderr')
        (HERE / 'pdflatex.stdout').write_bytes(ran.stdout)
        for source, target in (('equation.pdf', 'equation.pdf'), ('equation.log', 'build.log')):
            shutil.copyfile(directory / source, HERE / target)
    subprocess.run(['pdftotext', '-layout', str(HERE / 'equation.pdf'), str(HERE / 'equation.txt')], check=True)
    subprocess.run(['pdftoppm', '-singlefile', '-png', '-scale-to', '1800', str(HERE / 'equation.pdf'),
                    str(HERE / 'equation')], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def inspect_render(tex):
    pdf = (HERE / 'equation.pdf').read_bytes()
    info = subprocess.run(['pdfinfo', str(HERE / 'equation.pdf')], check=True, stdout=subprocess.PIPE).stdout.decode()
    require(re.search(r'^Pages:\s+1$', info, re.M) is not None
            and re.search(r'^Page size:\s+612 x 792 pts', info, re.M) is not None, 'Actual one-page Letter PDF')
    extracted = subprocess.run(['pdftotext', '-layout', str(HERE / 'equation.pdf'), '-'],
                               check=True, stdout=subprocess.PIPE).stdout
    require(extracted == (HERE / 'equation.txt').read_bytes(), 'Stored text is freshly extracted from actual PDF')
    introduction = re.search(r'Its complete decimal expansion is the.*?concatenation of these lines:',
                             extracted.decode(), re.S)
    require(introduction is not None, 'Actual PDF decimal introduction')
    numeral_lines = []
    for line in extracted.decode()[introduction.end():].splitlines():
        # Layout extraction can place unrelated left-column text before a
        # right-column numeral row; each full numeral row is its long suffix.
        suffix = re.search(r'(?<![0-9])([0-9]{30,62})\s*$', line)
        if suffix:
            numeral_lines.append(suffix[1])
    digits = ''.join(numeral_lines)
    require([len(row) for row in numeral_lines] == [62]*11+[33]
            and len(digits) == 715 and (digits+'\n').encode() == (HERE / 'DECIMAL_INTEGER.txt').read_bytes(),
            'All715 actual PDF digits recovered in order, without clipping or omission')
    log = (HERE / 'build.log').read_text()
    require('Overfull' not in log and 'Underfull' not in log and '! ' not in log, 'No TeX box or fatal diagnostics')
    png = (HERE / 'equation.png').read_bytes()
    require(png[:8] == b'\x89PNG\r\n\x1a\n', 'Actual rendered PNG')
    width, height = struct.unpack('>II', png[16:24])
    require((width, height) == (1391, 1800), 'Full-page1800-high PNG at unchanged aspect ratio')
    parent_tex = pinned(PARENT / 'equation.tex', PARENT_TEX_SHA)
    parent_text = pinned(PARENT / 'equation.txt', PARENT_TEXT_SHA)
    parent_pdf = pinned(PARENT / 'equation.pdf', PARENT_PDF_SHA)
    metrics = lambda source, text, document: {'tex_bytes': len(source), 'tex_nonwhite_characters': len(''.join(source.decode().split())),
                                            'pdf_nonwhite_characters': len(''.join(text.decode().split())), 'pdf_bytes': len(document)}
    before, after = metrics(parent_tex, parent_text, parent_pdf), metrics(tex, extracted, pdf)
    return {'schema': 'reverse_discovery2521_actual_render_v1', 'tex_sha256': sha(tex),
            'pages': 1, 'page_points': [612, 792], 'png_dimensions': [width, height],
            'actual715_pdf_digits_sha256': sha((digits+'\n').encode()), 'pdf_numeral_lines': len(numeral_lines),
            'no_overfull_or_underfull_boxes': True, 'same_fonts_and_margins': True,
            'parent': before, 'candidate': after, 'delta': {key: after[key]-before[key] for key in before},
            'artifacts': {name: record((HERE / name).read_bytes()) for name in
                          ('equation.pdf', 'equation.png', 'equation.txt', 'build.log', 'pdflatex.stdout')},
            'scope': 'Actual rendering and text extraction. Human visual review is recorded separately in README/review receipts.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--render', action='store_true')
    args = parser.parse_args()
    require(not args.render or args.build, '--render requires --build')
    files = materialize()
    closure = {**files, 'README.md': (HERE / 'README.md').read_bytes(), 'build.py': Path(__file__).read_bytes()}
    files['SOURCE_MANIFEST.json'] = encoded({'schema': 'reverse_discovery2521_complete_source_bundle_v1',
        'files': {name: record(raw) for name, raw in sorted(closure.items())},
        'seed_identity_proof': '../../research/reverse-discovery-decimal-seed/PROOF.md',
        'seed_identity_proof_sha256': SEED_PROOF_SHA, 'seed_identity_certificate_sha256': SEED_CERT_SHA,
        'scope': 'Complete unchanged polynomial and integer ports with an exact replacement finite seed recipe.'})
    for name, raw in files.items():
        path = HERE / name
        if args.build:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        else:
            require(path.read_bytes() == raw, 'Deterministic source artifact differs: ' + name)
    if args.render:
        render()
    if (HERE / 'equation.pdf').exists():
        rendered = inspect_render(files['equation.tex'])
        render_raw = encoded(rendered)
        if args.build:
            (HERE / 'RENDER_AUDIT.json').write_bytes(render_raw)
        else:
            require((HERE / 'RENDER_AUDIT.json').read_bytes() == render_raw, 'Actual render receipt reproduced')
        all_files = {**closure, 'SOURCE_MANIFEST.json': files['SOURCE_MANIFEST.json'], 'RENDER_AUDIT.json': render_raw}
        all_files.update({name: (HERE / name).read_bytes() for name in rendered['artifacts']})
        manifest = encoded({'schema': 'reverse_discovery_carrier65_2521_complete_page_v1',
                            'files': {name: record(raw) for name, raw in sorted(all_files.items())},
                            'parent_graph_sha256': PARENT_GRAPH_SHA, 'seed_certificate_sha256': SEED_CERT_SHA,
                            'scope': 'Complete candidate source, exact ports, unchanged full graph and actual PDF/PNG/text/log closure.'})
        if args.build:
            (HERE / 'MANIFEST.json').write_bytes(manifest)
        else:
            require((HERE / 'MANIFEST.json').read_bytes() == manifest, 'Complete candidate manifest reproduced')
    else:
        require(args.build, 'Complete candidate requires its actual render')
        rendered = None
    print(json.dumps({'status': 'PASS', 'variables': 14, 'operations': 65, 'degree': 150,
                      'decimal_digits': 715, 'raw_bytes': 59297, 'tex_bytes': len(files['equation.tex']),
                      'tex_sha256': sha(files['equation.tex']), 'builder_sha256': sha(Path(__file__).read_bytes()),
                      'render': rendered}, sort_keys=True))


if __name__ == '__main__':
    main()
