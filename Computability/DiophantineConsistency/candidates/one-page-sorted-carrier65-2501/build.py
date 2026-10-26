#!/usr/bin/env python3
"""Reproduce the complete715-digit sorted-selector2501 Carrier65 page."""
import argparse
import gzip
import hashlib
import importlib.util
import json
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
PARENT = ROOT / 'candidates/one-page-reverse-discovery-carrier65-2521'
NATIVE = ROOT / 'research/sorted-selector-independent'
PARENT_BUILD_SHA = 'ffa85c3ad98c412d1d112df97cb70b6cf4ced1273a3d4f889376bb17bee3d989'
PARENT_TEX_SHA = '563b2b5a2c6ebefdd705350aef0398eebbb7311512ebf31056a7dcb4f7f09282'
PARENT_GRAPH_SHA = '408dde55352b837db3c606db446f3bf41dc7fd6d9242808ba4a123930bf0b5ff'
PARENT_PDF_SHA = '02713180cf7a3537b690e62df454d956ec50767bcc2855f114b3687256de8b08'
PARENT_TEXT_SHA = '413c31ffaf2885b74793d9d15d013740cab9eae7b23f6d449303c4c031abcd86'
PARENT_SOURCE_SHA = 'adea7412b75397a1a243baf3a222724c8f4ff13fb44f4013b5ce57e09d5f818c'
DECIMAL_SHA = '313907d4b38e5d620d85b66f849368960d796ca6e442a8ee6b396c7d67d5a8a7'
VERIFIER_SHA = '55c1f4a34355b484de06cbe6ee3d30941808c5826d15218386cec74001be48b9'
CERTIFICATE_SHA = '372cee7b5e353ee174a9335e117c843b0e847892b038847bcb5df4c6dda8feae'
PROOF_SHA = 'd38b5f83ae1b6d342d849e134e1fa341306cb506d68f58fbe74abf9e013cb65d'
CARRIER_PROOF_SHA = '53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749'
WEIGHTS = r'''\chi_i=1+2^{10}(1+w_i+2^8n_i\\
\qquad+2^{17}p_i+2^{25}s_i)\quad(0\le i\le941),\\
'''
RANK_TEMPLATE = r'''\pi(0)=@zero@,\quad\pi(i)=@offset@+\sum_{j=@lower@}^{@upper@}
\fl{\frac{2^{@bits@}-@adjust@+\chi_j-\chi_i}{2^{@divisor_bits@}}}\quad(1\le i\le@last@).
'''
RANK_PARAMETERS = {'zero': 0, 'offset': 1, 'lower': 1, 'upper': 941,
                   'bits': 44, 'adjust': 1, 'divisor_bits': 44, 'last': 941}
SORTED_PHI = r'''\Phi(x)={}&\sum_{i=0}^{941}\chi_i x^{\pi(i)}\\
&+2^{10}x^{969}(x^9+2^{17})G_8(2x)\\
&+2^{18}x^{942}(x^{18}+2^{17})G_9(2x).
'''
FIXED_RECIPES = r'''\mu={}&\beta-G_{951}(\rho)\\
&-\rho^{960}G_{26}(\rho)-\rho^{1004},\\
\omega={}&\beta+8G_{917}(\rho)-4+(2^{45}-4)\Lambda\\
&+\rho^{960}G_9(\rho)+\rho^{987}G_8(\rho)
  +\rho^{1004},\\
K={}&\rho^{18}+\rho^{1004}+\rho^{2510}\\
&+2\Lambda\Phi(1/\rho),
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


def pinned(path, expected):
    raw = path.read_bytes()
    require(sha(raw) == expected, 'Pinned complete input changed: ' + str(path))
    return raw


def load_module(path, expected, name):
    pinned(path, expected)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Reviewed module specification')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rank_block():
    text = RANK_TEMPLATE
    for name, value in RANK_PARAMETERS.items():
        require(text.count('@' + name + '@') == 1, 'Unique complete rank parameter')
        text = text.replace('@' + name + '@', str(value))
    return text


def page_text(text, reversal, language):
    old = r'\Lambda=\rho^{1515},\\' + '\n' + reversal.PERMUTATION
    replacements = ((r'B=\rho^{2521}', r'B=\rho^{2501}', 1),
                    (old, r'\Lambda=\rho^{1493}.', 1),
                    (r'\rho^{2530}', r'\rho^{2510}', 1))
    for old, new, count in replacements:
        require(text.count(old) == count, 'Exact complete parent recipe multiplicity: ' + old)
        text = text.replace(old, new)
    start = text.index(r'\Phi(x)')
    end = text.index(r'\end{split}', start)
    require(text[start:end] == language.INLINE_PHI.replace(r')]x^i\\', r')]x^{\pi(i)}\\'),
            'Complete old printed selector weights before factoring')
    text = text[:start] + SORTED_PHI + text[end:]
    marker = 'where\n\\[\n\\begin{split}'
    require(text.count(marker) == 1, 'Unique complete fixed-recipe introduction')
    definitions = 'where\n\\[\n\\begin{gathered}\n' + WEIGHTS + rank_block() + '\\end{gathered}\n\\]\n\\[\n\\begin{split}'
    return text.replace(marker, definitions)


def printed_permutation(text, abstract_c):
    start = text.index(r'\chi_i=')
    end = text.index(r'\end{gathered}', start)
    require(text[start:start+len(WEIGHTS)] == WEIGHTS, 'Entire actual printed fixed weight definition and domain')
    pattern = re.escape(RANK_TEMPLATE)
    for name in RANK_PARAMETERS:
        pattern = pattern.replace(re.escape('@' + name + '@'), '(?P<' + name + '>[0-9]+)')
    match = re.fullmatch(pattern, text[start+len(WEIGHTS):end])
    require(match is not None, 'Entire actual printed floor-rank grammar')
    p = {name: int(match[name]) for name in RANK_PARAMETERS}
    require(0 <= p['zero'] <= 941 and 0 <= p['offset'] <= 2
            and 0 <= p['lower'] <= p['upper'] <= 941 and p['last'] == 941
            and 1 <= p['bits'] <= 47 and 1 <= p['divisor_bits'] <= 47
            and p['adjust'] in (0, 1), 'Finite actual rank parameter domains')
    weights = abstract_c[:942]
    comparisons = [[((1 << p['bits']) - p['adjust'] + weights[j] - weights[i]) // (1 << p['divisor_bits'])
                    for j in range(p['lower'], p['upper']+1)] for i in range(1, p['last']+1)]
    permutation = [p['zero']] + [p['offset'] + sum(row) for row in comparisons]
    require(sorted(permutation) == list(range(942)), 'Complete printed942-position bijection')
    require(p == RANK_PARAMETERS and all(row == [int(weights[j] > weights[i]) for j in range(1, 942)]
                                        for i, row in enumerate(comparisons, 1)),
            'Every actual printed floor equals the exact strict weight comparison')
    return permutation, p


def printed_recipe(text, actions, language, expected_c, expected_support, expected_tiles):
    abstract_tiles = language.printed_tiles(text, actions)
    start = text.index(r'\Phi(x)')
    end = text.index(r'\end{split}', start)
    phi = text[start:end]
    require(phi == SORTED_PHI, 'Entire printed factored sorted Phi recipe')
    # Only after reading and checking the actual exponent grammar, expand the
    # same complete abstract table and apply its actual printed permutation.
    normalized = text[:start] + language.INLINE_PHI + text[end:]
    abstract_c = language.printed_coefficients(normalized, abstract_tiles)
    permutation, parameters = printed_permutation(text, abstract_c)
    base_c = abstract_c.copy()
    physical_tiles = [None] * 942
    for i, position in enumerate(permutation):
        base_c[position] = abstract_c[i]
        physical_tiles[position] = abstract_tiles[i]
    require(physical_tiles == expected_tiles, 'Every942 physical tile from actual printed pi')
    require([2 * value for value in base_c] == expected_c, 'All3297 actual permuted doubled coefficients')
    physical = language.printed_physical(text.replace(r'\mu', 'M_C').replace(r'\omega', 'M_F'))
    require({e for e, value in enumerate(physical) if value} == expected_support,
            'Entire physical support including zero-weight marker and dummy')
    start = text.index(r'\mu={}')
    end = text.index(r'\end{align*}', start)
    require(text[start:end] == FIXED_RECIPES, 'Entire actual three fixed-integer recipes')
    radix = re.findall(r'\\rho=2\^\{([0-9]+)\}', text)
    lengths = re.findall(r'B=\\rho\^\{([0-9]+)\}', text)
    centers = re.findall(r'\\Lambda=\\rho\^\{([0-9]+)\}', text)
    require(radix == ['47'] and lengths == ['2501'] and centers == ['1493'], 'Exact printed radix, cell length and clause')
    power = lambda e: 1 << (int(radix[0]) * e)
    G = lambda n: sum(power(j) for j in range(n))
    length, center = int(lengths[0]), int(centers[0])
    beta = power(length) - 1
    MC = beta - sum(value * power(e) for e, value in enumerate(physical) if value)
    K = power(18) + power(1004) + power(2510)
    K += 2 * sum(value * power(center - e) for e, value in enumerate(base_c) if value)
    MF = beta + 8 * G(917) - 4 + ((1 << 45) - 4) * power(center)
    MF += power(960) * G(9) + power(987) * G(8) + power(1004)
    return {'beta': beta, 'K': K, 'MC': MC, 'MF_source': MF}, physical, base_c, permutation, parameters


def materialize():
    parent = load_module(PARENT / 'build.py', PARENT_BUILD_SHA, 'reviewed_complete715_decimal2521')
    pinned(PARENT / 'SOURCE_MANIFEST.json', PARENT_SOURCE_SHA)
    parent_files = parent.materialize()
    require(sha(parent_files['equation.tex']) == PARENT_TEX_SHA
            and sha(parent_files['polynomial.json']) == PARENT_GRAPH_SHA
            and sha(parent_files['DECIMAL_INTEGER.txt']) == DECIMAL_SHA, 'Whole reviewed decimal parent reproduced')
    reversal = parent.load(parent.PARENT / 'build.py', parent.PARENT_BUILD_SHA, 'reviewed_reversal_page_grammar')
    decimal_language = reversal.load_module(reversal.PARENT / 'build.py', reversal.PARENT_BUILD_SHA, 'reviewed_decimal_front')
    language = decimal_language.load_module(decimal_language.PARENT / 'build.py', decimal_language.PARENT_BUILD_SHA,
                                           'reviewed_full942_source')
    verifier = load_module(NATIVE / 'certify.py', VERIFIER_SHA, 'reviewed_sorted2501_verifier')
    certificate = json.loads(pinned(NATIVE / 'certificate.json', CERTIFICATE_SHA))
    pinned(NATIVE / 'PROOF.md', PROOF_SHA)
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O' if sys.flags.optimize == 1 else '-OO')
    ran = subprocess.run(command + [str(NATIVE / 'certify.py')], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    report = json.loads(ran.stdout)
    require(not ran.stderr and report['status'] == 'PASS' and report['certificate_sha256'] == CERTIFICATE_SHA,
            'Complete2501 finite certificate reproduced')
    _, _, actions, tiles, c, support = verifier.model()
    canonical, _ = verifier.constants(c, support)
    parent_text = parent_files['equation.tex'].decode()
    text = page_text(parent_text, reversal, language)
    decimal_language.check_front(text)
    value, digits = decimal_language.read_decimal(text)
    require((digits + '\n').encode() == parent_files['DECIMAL_INTEGER.txt'] and len(digits) == 715,
            'Every715 printed decimal digit preserved')
    decoded, decoder_data = parent.printed_decode(text, decimal_language)
    require(decoded == actions and sha(encoded(decoded)) == certificate['recipe_bindings']['actions_sha256'],
            'Every430 action decoded from actual decimal source')
    printed, physical, base_c, permutation, parameters = printed_recipe(text, decoded, language, c, support, tiles)
    require(printed == canonical and sum(physical) == 978 and physical[977] == physical[1004] == 1,
            'All four whole printed integers and978 physical positions')
    require(base_c[977] == base_c[1004] == 0 and permutation[928] == 504
            and tiles[504] == (3, 436, 4, 4), 'Actual initializer504 and distinct zero-weight controls')
    require(permutation == certificate['rank_defined_permutation']['all942_ranks'],
            'Every actual printed floor rank equals the complete certified permutation')
    require(text[text.index(parent.DECODER_START):] == parent_text[parent_text.index(parent.DECODER_START):],
            'Every715 decimal digit, full decoder and scope footer byte-identical')
    beta, K, MC, MF = (printed[k] for k in ('beta', 'K', 'MC', 'MF_source'))
    require(beta >= 31 and K > 0 and 0 < MC < beta < MF < 2 * beta, 'Carrier65 scalar hypotheses at exact2501 ports')

    controls = {}
    mutations = {
        'rank_start': text.replace(r'\pi(0)=0', r'\pi(0)=1', 1),
        'rank_numerator': text.replace(r'2^{44}-1+\chi_j-\chi_i', r'2^{44}-0+\chi_j-\chi_i', 1),
        'rank_start_in_sum': text.replace(r'\sum_{j=1}^{941}', r'\sum_{j=0}^{941}', 1),
        'rank_bound': text.replace(r'\sum_{j=1}^{941}', r'\sum_{j=1}^{940}', 1),
        'rank_sign': text.replace(r'+\chi_j-\chi_i', r'+\chi_i-\chi_j', 1),
        'weight_definition': text.replace(r'\chi_i=1+2^{10}', r'\chi_i=1+2^{11}', 1),
        'selector_exponent': text.replace(r'\chi_i x^{\pi(i)}', r'\chi_i x^i', 1),
        'initializer': text.replace('928&(3,436,4,4)', '929&(3,436,4,4)', 1),
        'marker': text.replace(r'-\rho^{1004},\\', r',\\', 1),
        'dummy': text.replace(r'\rho^{960}G_{26}(\rho)', r'\rho^{960}G_{17}(\rho)-\rho^{978}G_8(\rho)', 1),
        'padding_bit': text.replace(r'+8G_{917}(\rho)-4', r'+4G_{917}(\rho)', 1),
        'origin': text.replace(r'+8G_{917}(\rho)-4', r'+8G_{917}(\rho)', 1),
        'scale': text.replace(r'+2\Lambda\Phi(1/\rho)', r'+\Lambda\Phi(1/\rho)', 1),
    }
    for name, corrupted in mutations.items():
        require(corrupted != text, 'Actual page mutation took effect: ' + name)
        try:
            printed_recipe(corrupted, decoded, language, c, support, tiles)
        except ValueError as error:
            controls[name] = str(error)
        else:
            raise ValueError('Actual page corruption unexpectedly accepted: ' + name)
    for name, position in (('marker', 1004), ('dummy', 977)):
        corrupted = language.printed_physical(mutations[name].replace(r'\mu', 'M_C').replace(r'\omega', 'M_F'))
        expected = physical.copy()
        expected[position] = 0
        require(corrupted == expected, 'Actual mask mutation omits exactly one physical position')
        bad_MC = beta - sum(value * (1 << (47 * e)) for e, value in enumerate(corrupted) if value)
        require(bad_MC == MC + (1 << (47 * position)) and bad_MC.bit_count() == MC.bit_count() + 1,
                'Whole corrupted printed mask changes exactly its intended bit')

    files, ports = {}, {}
    for graph_name, name in (('beta', 'beta'), ('K0', 'K'), ('MC', 'MC'), ('MF', 'MF_source')):
        value = printed[name]
        raw = value.to_bytes((value.bit_length() + 7) // 8, 'big')
        expected = certificate['constant_ports'][name]
        require(record(raw) == {'bytes': expected['bytes'], 'sha256': expected['sha256']}
                and value.bit_length() == expected['bits'], 'Whole printed port matches certificate: ' + name)
        packed = gzip.compress(raw, mtime=0)
        filename = name + '.bin.gz'
        files['coefficients/' + filename] = packed
        ports[graph_name] = {'file': filename, 'bits': value.bit_length(), 'raw_bytes': len(raw),
                             'raw_sha256': sha(raw), 'gzip_sha256': sha(packed)}
    require(sum(row['raw_bytes'] for row in ports.values()) == 58829, 'Complete raw byte cost')
    graph = json.loads(parent_files['polynomial.json'])
    require(graph['arithmetic_proof_sha256'] == CARRIER_PROOF_SHA and graph['operations'] == 65
            and graph['exact_degree'] == 150 and len(graph['witnesses']) == 14, 'Whole reviewed uniform Carrier65 graph')
    graph['name'] = 'decimal_sorted_carrier65_2501_degree150'
    graph['parent_polynomial_sha256'] = PARENT_GRAPH_SHA
    graph['proof_boundary'] = 'Complete sorted-selector2501 native/P66 proof and discharged Pcso, followed by uniform Carrier65 positive-zero maps; retained syntactic calibration, no new formal-kernel replay.'
    graph['coefficient_binding'] = {'schema': 'sorted2501_materialized_v1', 'path': 'coefficients/',
        'ports': ports, 'raw_bytes': 58829, 'certificate': '../../research/sorted-selector-independent/certificate.json',
        'certificate_sha256': CERTIFICATE_SHA, 'ordinary_proof': '../../research/sorted-selector-independent/PROOF.md',
        'ordinary_proof_sha256': PROOF_SHA}
    parent_graph = json.loads(parent_files['polynomial.json'])
    for key in set(graph) - {'name', 'parent_polynomial_sha256', 'proof_boundary', 'coefficient_binding'}:
        require(graph[key] == parent_graph[key], 'Every full graph/front field preserved: ' + key)
    files['equation.tex'] = text.encode()
    files['polynomial.json'] = encoded(graph)
    files['DECIMAL_INTEGER.txt'] = parent_files['DECIMAL_INTEGER.txt']
    files['BUILD_AUDIT.json'] = encoded({'schema': 'decimal_sorted2501_source_audit_v1',
        'parent_builder_sha256': PARENT_BUILD_SHA, 'parent_page_sha256': PARENT_TEX_SHA,
        'parent_graph_sha256': PARENT_GRAPH_SHA, 'verifier_sha256': VERIFIER_SHA,
        'certificate_sha256': CERTIFICATE_SHA, 'ordinary_proof_sha256': PROOF_SHA,
        'carrier_proof_sha256': CARRIER_PROOF_SHA, 'display_scalar_names': graph['display_scalar_names'],
        'all715_decimal_digits_identical': True, 'decimal_integer_sha256': DECIMAL_SHA,
        'actual_decoder_parameters': decoder_data['parameters'], 'actual_rank_parameters': parameters,
        'all885481_floor_comparisons_checked': True, 'fixed_weight_family': 'chi_i',
        'all430_actions_identical': True, 'all942_physical_tiles_reconstructed': True,
        'physical_tiles_sha256': sha(encoded(tiles)), 'abstract_initializer': 928, 'physical_initializer': 504,
        'actual_printed_permutation_sha256': sha(encoded(permutation)),
        'all3297_coefficients_reconstructed': True, 'base_Phi_sha256': sha(encoded(base_c)),
        'physical_positions': 978, 'zero_weight_physical_positions': [977, 1004],
        'all_four_printed_integers_equal_canonical': True, 'raw_bytes': 58829,
        'gzip_bytes': sum(len(raw) for name, raw in files.items() if name.startswith('coefficients/')),
        'entire65_operation_graph_unchanged': True, 'variables': 14, 'operations': 65, 'degree': 150,
        'carrier_scalar_hypotheses': True, 'negative_actual_source_controls': controls,
        'scope': 'Complete actual source/decimal/permutation/whole-port reconstruction. Ordinary proof, rendering and peer review remain separately bound.'})
    return files


def render():
    with tempfile.TemporaryDirectory(prefix='sorted2501-render-') as temporary:
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
    return {'schema': 'sorted2501_actual_render_v1', 'tex_sha256': sha(tex),
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
    files['SOURCE_MANIFEST.json'] = encoded({'schema': 'decimal_sorted2501_source_bundle_v1',
        'files': {name: record(raw) for name, raw in sorted(closure.items())},
        'native_certificate': 'research/sorted-selector-independent/certificate.json',
        'native_certificate_sha256': CERTIFICATE_SHA, 'ordinary_proof': 'research/sorted-selector-independent/PROOF.md',
        'ordinary_proof_sha256': PROOF_SHA, 'carrier_proof': 'research/carrier65-independent/PROOF.md',
        'carrier_proof_sha256': CARRIER_PROOF_SHA,
        'scope': 'Complete deterministic source and integer closure; render/acceptance artifacts are separate.'})
    for name, raw in files.items():
        path = HERE / name
        if args.build:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
        else:
            require(path.read_bytes() == raw, 'Deterministic artifact differs: ' + name)
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
        manifest = encoded({'schema': 'sorted_carrier65_2501_complete_page_v1',
                            'files': {name: record(raw) for name, raw in sorted(all_files.items())},
                            'parent_graph_sha256': PARENT_GRAPH_SHA, 'native_certificate_sha256': CERTIFICATE_SHA,
                            'scope': 'Complete candidate source, new ports, same full uniform graph and actual PDF/PNG/text/log closure.'})
        if args.build:
            (HERE / 'MANIFEST.json').write_bytes(manifest)
        else:
            require((HERE / 'MANIFEST.json').read_bytes() == manifest, 'Complete candidate manifest reproduced')
    else:
        require(args.build, 'Complete candidate requires its actual render')
        rendered = None
    print(json.dumps({'status': 'PASS', 'variables': 14, 'operations': 65, 'degree': 150,
                      'raw_bytes': 58829, 'tex_bytes': len(files['equation.tex']),
                      'tex_sha256': sha(files['equation.tex']), 'builder_sha256': sha(Path(__file__).read_bytes()),
                      'render': rendered}, sort_keys=True))


if __name__ == '__main__':
    main()
