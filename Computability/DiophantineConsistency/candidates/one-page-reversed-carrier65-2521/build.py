#!/usr/bin/env python3
"""Reproduce the complete decimal reversed-selector2521 Carrier65 page."""
import argparse
import gzip
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
PARENT = ROOT / 'candidates/one-page-decimal-carrier65-2953'
NATIVE = ROOT / 'research/reversed-selector-independent'
PARENT_BUILD_SHA = 'bdc359762c1c1bb1014eb400d7cf6b23fa604030c17998afd5431bab5f3c0aca'
PARENT_TEX_SHA = '473d6bb1015fb4d381d12606946759ffc5e8512be48774aaa25de6e4b3cea051'
PARENT_GRAPH_SHA = '0691be13bf9b678de0ce067be4accd637a49200518846a79982346c709570248'
DECIMAL_SHA = 'bb8a7c133fe5baafbb41a8b7c1cbadce613e4dc8e79b6866313254dd07bea514'
VERIFIER_SHA = 'c01832bbf7a3e356e46241959ac10ecb474208fff749ba6ac539841bcd50fb4f'
CERTIFICATE_SHA = 'e778823a2ff489789db769189e6e217c8e8d1db955b15232eddd8d473b3e36ed'
PROOF_SHA = '81e9dc739834d385a0134b23cdb6744ad7df2228af05a3ad66956fb17cdb28e8'
CARRIER_PROOF_SHA = '53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749'
PERMUTATION = r'\pi(0)=0,\quad\pi(i)=942-i\quad(1\le i\le941).'
FIXED_RECIPES = r'''\mu={}&\beta-G_{951}(\rho)\\
&-\rho^{960}G_{26}(\rho)-\rho^{1004},\\
\omega={}&\beta+8G_{917}(\rho)-4+(2^{45}-4)\Lambda\\
&+\rho^{960}G_9(\rho)+\rho^{987}G_8(\rho)
  +\rho^{1004},\\
K={}&\rho^{18}+\rho^{1004}+\rho^{2530}\\
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


def page_text(text):
    replacements = ((r'B=\rho^{2953}', r'B=\rho^{2521}', 1),
                    (r'\Lambda=\rho^{1945}.', r'\Lambda=\rho^{1515},\\' + '\n' + PERMUTATION, 1),
                    (r'\rho^{1005}', r'\rho^{1004}', 3),
                    (r'\rho^{2962}', r'\rho^{2530}', 1),
                    (r'\beta+4G_{917}(\rho)', r'\beta+8G_{917}(\rho)-4', 1),
                    (r')]x^i\\', r')]x^{\pi(i)}\\', 1))
    for old, new, count in replacements:
        require(text.count(old) == count, 'Exact complete parent recipe multiplicity: ' + old)
        text = text.replace(old, new)
    return text


def printed_permutation(text):
    pattern = r'\\pi\(0\)=([0-9]+),\\quad\\pi\(i\)=([0-9]+)-i\\quad\(1\\le i\\le([0-9]+)\)\.'
    matches = list(re.finditer(pattern, text))
    require(len(matches) == 1, 'Entire printed selector permutation grammar')
    zero, total, last = map(int, matches[0].groups())
    require((zero, total, last) == (0, 942, 941), 'Exact printed Start-preserving reversal')
    permutation = [zero] + [total - i for i in range(1, last + 1)]
    require(sorted(permutation) == list(range(942)), 'Complete printed942-position bijection')
    return permutation


def printed_recipe(text, actions, language, expected_c, expected_support, expected_tiles):
    permutation = printed_permutation(text)
    abstract_tiles = language.printed_tiles(text, actions)
    start = text.index(r'\Phi(x)')
    end = text.index(r'\end{split}', start)
    phi = text[start:end]
    expected_phi = language.INLINE_PHI.replace(r')]x^i\\', r')]x^{\pi(i)}\\')
    require(phi == expected_phi, 'Entire printed permuted inline Phi recipe')
    # Only after reading and checking the actual exponent grammar, expand the
    # same complete abstract table and apply its actual printed permutation.
    normalized = text[:start] + language.INLINE_PHI + text[end:]
    abstract_c = language.printed_coefficients(normalized, abstract_tiles)
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
    require(radix == ['47'] and lengths == ['2521'] and centers == ['1515'], 'Exact printed radix, cell length and clause')
    power = lambda e: 1 << (int(radix[0]) * e)
    G = lambda n: sum(power(j) for j in range(n))
    length, center = int(lengths[0]), int(centers[0])
    beta = power(length) - 1
    MC = beta - sum(value * power(e) for e, value in enumerate(physical) if value)
    K = power(18) + power(1004) + power(2530)
    K += 2 * sum(value * power(center - e) for e, value in enumerate(base_c) if value)
    MF = beta + 8 * G(917) - 4 + ((1 << 45) - 4) * power(center)
    MF += power(960) * G(9) + power(987) * G(8) + power(1004)
    return {'beta': beta, 'K': K, 'MC': MC, 'MF_source': MF}, physical, base_c, permutation


def materialize():
    parent = load_module(PARENT / 'build.py', PARENT_BUILD_SHA, 'reviewed_decimal_carrier2953')
    parent_files = parent.materialize()
    require(sha(parent_files['equation.tex']) == PARENT_TEX_SHA
            and sha(parent_files['polynomial.json']) == PARENT_GRAPH_SHA
            and sha(parent_files['DECIMAL_INTEGER.txt']) == DECIMAL_SHA, 'Whole reviewed decimal parent reproduced')
    language = parent.load_module(parent.PARENT / 'build.py', parent.PARENT_BUILD_SHA, 'reviewed_full942_source')
    verifier = load_module(NATIVE / 'certify.py', VERIFIER_SHA, 'reviewed_reversed2521_verifier')
    certificate = json.loads(pinned(NATIVE / 'certificate.json', CERTIFICATE_SHA))
    pinned(NATIVE / 'PROOF.md', PROOF_SHA)
    command = [sys.executable, '-B']
    if sys.flags.optimize:
        command.append('-O' if sys.flags.optimize == 1 else '-OO')
    ran = subprocess.run(command + [str(NATIVE / 'certify.py')], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    report = json.loads(ran.stdout)
    require(not ran.stderr and report['status'] == 'PASS' and report['certificate_sha256'] == CERTIFICATE_SHA,
            'Complete2521 finite certificate reproduced')
    _, _, actions, tiles, c, support = verifier.model()
    canonical, _ = verifier.constants(c, support)
    text = page_text(parent_files['equation.tex'].decode())
    parent.check_front(text)
    value, digits = parent.read_decimal(text)
    require((digits + '\n').encode() == parent_files['DECIMAL_INTEGER.txt'] and len(digits) == 781,
            'Every781 printed decimal digit preserved')
    decoded = parent.decode(value)
    require(decoded == actions and sha(encoded(decoded)) == certificate['recipe_bindings']['actions_sha256'],
            'Every430 action decoded from actual decimal source')
    printed, physical, base_c, permutation = printed_recipe(text, decoded, language, c, support, tiles)
    require(printed == canonical and sum(physical) == 978 and physical[977] == physical[1004] == 1,
            'All four whole printed integers and978 physical positions')
    require(base_c[977] == base_c[1004] == 0 and permutation[928] == 14
            and tiles[14] == (3, 436, 4, 4), 'Actual initializer14 and distinct zero-weight controls')
    beta, K, MC, MF = (printed[k] for k in ('beta', 'K', 'MC', 'MF_source'))
    require(beta >= 31 and K > 0 and 0 < MC < beta < MF < 2 * beta, 'Carrier65 scalar hypotheses at exact2521 ports')

    controls = {}
    mutations = {
        'permutation': text.replace(r'\pi(i)=942-i', r'\pi(i)=941-i', 1),
        'selector_exponent': text.replace(r')]x^{\pi(i)}', r')]x^i', 1),
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
    require(sum(row['raw_bytes'] for row in ports.values()) == 59297, 'Complete raw byte cost')
    graph = json.loads(parent_files['polynomial.json'])
    require(graph['arithmetic_proof_sha256'] == CARRIER_PROOF_SHA and graph['operations'] == 65
            and graph['exact_degree'] == 150 and len(graph['witnesses']) == 14, 'Whole reviewed uniform Carrier65 graph')
    graph['name'] = 'decimal_reversed_carrier65_2521_degree150'
    graph['parent_polynomial_sha256'] = PARENT_GRAPH_SHA
    graph['proof_boundary'] = 'Complete reversed-selector2521 native/P66 proof and discharged Pcrv, followed by uniform Carrier65 positive-zero maps; retained syntactic calibration, no new formal-kernel replay.'
    graph['coefficient_binding'] = {'schema': 'reversed2521_materialized_v1', 'path': 'coefficients/',
        'ports': ports, 'raw_bytes': 59297, 'certificate': '../../research/reversed-selector-independent/certificate.json',
        'certificate_sha256': CERTIFICATE_SHA, 'ordinary_proof': '../../research/reversed-selector-independent/PROOF.md',
        'ordinary_proof_sha256': PROOF_SHA}
    files['equation.tex'] = text.encode()
    files['polynomial.json'] = encoded(graph)
    files['DECIMAL_INTEGER.txt'] = parent_files['DECIMAL_INTEGER.txt']
    files['BUILD_AUDIT.json'] = encoded({'schema': 'decimal_reversed2521_source_audit_v1',
        'parent_builder_sha256': PARENT_BUILD_SHA, 'parent_page_sha256': PARENT_TEX_SHA,
        'parent_graph_sha256': PARENT_GRAPH_SHA, 'verifier_sha256': VERIFIER_SHA,
        'certificate_sha256': CERTIFICATE_SHA, 'ordinary_proof_sha256': PROOF_SHA,
        'carrier_proof_sha256': CARRIER_PROOF_SHA, 'display_scalar_names': graph['display_scalar_names'],
        'all781_decimal_digits_identical': True, 'decimal_integer_sha256': DECIMAL_SHA,
        'all430_actions_identical': True, 'all942_physical_tiles_reconstructed': True,
        'physical_tiles_sha256': sha(encoded(tiles)), 'abstract_initializer': 928, 'physical_initializer': 14,
        'actual_printed_permutation_sha256': sha(encoded(permutation)),
        'all3297_coefficients_reconstructed': True, 'base_Phi_sha256': sha(encoded(base_c)),
        'physical_positions': 978, 'zero_weight_physical_positions': [977, 1004],
        'all_four_printed_integers_equal_canonical': True, 'raw_bytes': 59297,
        'entire65_operation_graph_unchanged': True, 'variables': 14, 'operations': 65, 'degree': 150,
        'carrier_scalar_hypotheses': True, 'negative_actual_source_controls': controls,
        'scope': 'Complete actual source/decimal/permutation/whole-port reconstruction. Ordinary proof, rendering and peer review remain separately bound.'})
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    files = materialize()
    closure = {**files, 'README.md': (HERE / 'README.md').read_bytes(), 'build.py': Path(__file__).read_bytes()}
    files['SOURCE_MANIFEST.json'] = encoded({'schema': 'decimal_reversed2521_source_bundle_v1',
        'files': {name: record(raw) for name, raw in sorted(closure.items())},
        'native_certificate': 'research/reversed-selector-independent/certificate.json',
        'native_certificate_sha256': CERTIFICATE_SHA, 'ordinary_proof': 'research/reversed-selector-independent/PROOF.md',
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
    print(json.dumps({'status': 'PASS', 'variables': 14, 'operations': 65, 'degree': 150,
                      'raw_bytes': 59297, 'tex_bytes': len(files['equation.tex']),
                      'files': {name: sha(raw) for name, raw in files.items()}}, sort_keys=True))


if __name__ == '__main__':
    main()
