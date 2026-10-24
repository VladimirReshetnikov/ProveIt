#!/usr/bin/env python3
"""Independently verify the delivered literal equations and new arithmetic bindings.

Requires Python 3.10+, standard library only. No network or source repository.
--rebuild also runs both complete deterministic producers in temporary directories.
--skip-manifest is for authoring before the final manifest is generated.
"""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import hashlib
import json
import re
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run(script, *args):
    flags = ['-B'] + (['-O'] if sys.flags.optimize else [])
    process = subprocess.run([sys.executable, *flags, str(ROOT / script), *map(str, args)],
                             cwd=ROOT, text=True, capture_output=True)
    if process.returncode:
        raise RuntimeError(f'{script} failed\n{process.stdout}\n{process.stderr}')
    return json.loads(process.stdout)


def verify_manifest():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for relative, expected in manifest['sha256'].items():
        path = (ROOT / relative).resolve()
        require(path.is_relative_to(ROOT), 'Manifest path leaves release')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected, 'Hash mismatch: ' + relative)
    return len(manifest['sha256'])


def literal_checks(variant):
    base = ROOT / 'portable/equations' / variant / 'natural'
    equation = json.loads((base / 'equation.json').read_text())
    expanded = json.loads((base / 'expanded_polynomial.json').read_text())
    n, rows = len(equation['variables']), equation['residuals']
    used = {i for row in rows for c, monomial in row['terms'] for i in monomial if c}
    require(used == set(range(n)), 'Missing or undeclared variable in ' + variant)
    require(all(type(c) is int and len(m) <= 2 for r in rows for c, m in r['terms']), 'Nonquadratic residual')
    terms = expanded['terms']
    require(len({tuple(m) for c, m in terms}) == len(terms), 'Uncollected coefficient list')
    require(all(type(c) is int and c != 0 and m == sorted(m) for c, m in terms), 'Noncanonical coefficient')
    require(max(map(lambda term: len(term[1]), terms)) == 4, 'Wrong degree')
    constant = sum(c for c, m in terms if not m)
    residual_constant = sum(sum(c for c, m in r['terms'] if not m) ** 2 for r in rows)
    require(constant == residual_constant, 'Constant coefficient mismatch')
    return {'variables': n, 'quadratic_residuals': len(rows), 'exact_degree': 4,
            'expanded_monomials': len(terms), 'coefficient_height': max(abs(c) for c, m in terms),
            'all_variables_used': True, 'integer_coefficients': True}


def check_integer_companion():
    path = ROOT / 'equations/integer/recipe.json'
    data = json.loads(path.read_text())
    base = (path.parent / data['base_equation']).resolve()
    require(hashlib.sha256(base.read_bytes()).hexdigest() == data['base_equation_sha256'], 'Integer base hash')
    n = len(json.loads(base.read_text())['variables'])
    require(data['source_variables'] == n and data['variables'] == 3*n and data['exact_degree'] == 8, 'Integer dimensions')
    expected = [[[1, [3*i, 3*i]], [1, [3*i+1, 3*i+1]],
                 [1, [3*i+2, 3*i+2]], [1, [3*i+2]]] for i in range(n)]
    require(data['substitutions'] == expected, 'Integer substitution differs from H')
    return {'variables': 3*n, 'exact_degree': 8, 'literal_substitution_verified': True,
            'surjectivity_basis': "Report proof using Legendre's three-square theorem"}


def check_printed_equation():
    """Parse the emitted TeX independently; do not import its generator."""
    equation = json.loads((ROOT / 'portable/equations/primary/natural/equation.json').read_text())
    source = (ROOT / 'report/residuals.tex').read_text()
    blocks = re.findall(r'\\begin\{align\*\}(.*?)\\end\{align\*\}', source, re.S)
    require(len(blocks) == len(equation['residuals']), 'Printed residual count')
    term_count = 0
    for index, block in enumerate(blocks):
        heading = re.match(r'\s*r_\{(\d+)\}\s*&=\s*', block)
        require(heading is not None and int(heading.group(1)) == index, 'Printed residual order')
        expression = block[heading.end():].replace('\\\\', '').replace('&\\quad', '')
        expression = re.sub(r'\s+', '', expression)
        terms = []
        for token in re.findall(r'[+-]?[^+-]+', expression):
            sign = -1 if token.startswith('-') else 1
            token = token.lstrip('+-')
            coefficient = re.match(r'\d+', token)
            if coefficient:
                c = sign * int(coefficient.group())
                token = token[coefficient.end():]
            else:
                c = sign
            monomial = []
            while token:
                factor = re.match(r'z_\{(\d+)\}(?:\^\{(\d+)\})?', token)
                require(factor is not None, 'Unrecognized printed term')
                monomial += [int(factor.group(1))] * int(factor.group(2) or 1)
                token = token[factor.end():]
            terms.append([c, monomial])
        require(terms == equation['residuals'][index]['terms'], 'Printed polynomial differs at residual ' + str(index))
        term_count += len(terms)
    metrics = (ROOT / 'report/metrics.tex').read_text()
    for macro, filename in [('EquationHash', 'equation.json'), ('PolynomialHash', 'expanded_polynomial.json')]:
        digest = hashlib.sha256((ROOT / 'portable/equations/primary/natural' / filename).read_bytes()).hexdigest()
        require('\\newcommand{\\' + macro + '}{' + digest + '}' in metrics, 'Printed hash mismatch')
    return {'literal_residuals': len(blocks), 'literal_terms': term_count,
            'every_coefficient_and_index_matched': True, 'printed_hashes_matched': True}


def check_baseline():
    snapshot = json.loads((ROOT / 'provenance/SNAPSHOT.json').read_text())
    archive = ROOT / 'provenance' / snapshot['baseline_archive']
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == snapshot['baseline_archive_sha256'], 'Baseline archive hash')
    with zipfile.ZipFile(archive) as source:
        suffix = '/architecture/derived16_cantor/natural/'
        paths = [name for name in source.namelist() if name.endswith(suffix + 'equation.json')]
        require(len(paths) == 1, 'Ambiguous baseline endpoint')
        equation = json.loads(source.read(paths[0]))
        expanded = json.loads(source.read(paths[0].removesuffix('equation.json') + 'expanded_polynomial.json'))
    collected = {}
    for row in equation['residuals']:
        for c, m in row['terms']:
            for d, n in row['terms']:
                key = tuple(sorted(m + n))
                collected[key] = collected.get(key, 0) + c*d
    collected = {m: c for m, c in collected.items() if c}
    require(collected == {tuple(m): c for c, m in expanded['terms']}, 'Baseline collected coefficients')
    metrics = {'variables': len(equation['variables']), 'quadratic_rows': len(equation['residuals']),
               'degree': max(map(len, collected)), 'monomials': len(collected),
               'coefficient_height': max(map(abs, collected.values()))}
    require(metrics == snapshot['baseline_metrics'], 'Baseline metric table differs')
    return {'exact_expansion_matched': True, **metrics}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rebuild', action='store_true')
    p.add_argument('--skip-manifest', action='store_true')
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    metadata = ROOT / 'portable/equations/primary/raw/raw_audit_input.json'
    raw = metadata.with_name('equation.json')
    result = {'python_optimization': sys.flags.optimize,
              'manifest_files_verified': None if args.skip_manifest else verify_manifest()}
    result['contractions_and_coefficients'] = run('portable/verify.py')
    result['cap_semantics'] = run('code/check_cap_independent.py', metadata, '--adversarial')
    result['radix_semantics'] = run('code/check_self_radix.py', metadata)
    with TemporaryDirectory(prefix='con_zfc_release_') as directory:
        scratch = Path(directory)
        generated = scratch / 'affine_certificate.json'
        result['affine_export'] = run('code/check_affine_export.py', metadata, raw, '--certificate', generated)
        retained = ROOT / 'verification/affine_export_certificate.json'
        require(json.loads(generated.read_text()) == json.loads(retained.read_text()), 'Affine certificate mismatch')
        if args.rebuild:
            result['full_rebuilds'] = [run('portable/build.py', '--variant', variant,
                                          '--output', scratch / variant)
                                       for variant in ['primary', 'sparse']]
            for rebuild in result['full_rebuilds']:
                rebuild['output'] = '<temporary directory removed after verification>'
    result['literal_equations'] = {v: literal_checks(v) for v in ['primary', 'sparse']}
    result['printed_equation'] = check_printed_equation()
    result['baseline_comparison'] = check_baseline()
    result['integer_companion'] = check_integer_companion()
    result['verified'] = True
    result['scope'] = ('Exact finite checks and reconstruction; universal equivalence uses the '
                       'ordinary mathematical proof and its named inherited dependencies.')
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
