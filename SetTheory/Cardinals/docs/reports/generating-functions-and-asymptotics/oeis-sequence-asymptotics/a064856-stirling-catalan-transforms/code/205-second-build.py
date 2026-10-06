#!/usr/bin/env python3
"""Regenerate, check, typeset, and package Report205 deterministically."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
sys.dont_write_bytecode = True
import tempfile
import zipfile

import mpmath as mp
import sympy as sp
from verify_exact import REFERENCE_Q, require, run as independent_exact_checks

ROOT = Path(__file__).resolve().parent
EPOCH = 1791072000  # 2026-10-04 00:00:00 UTC
ARCHIVE = 'Report205.zip'
CHECKPOINTS = (10, 20, 50, 100, 200, 500, 1000, 2000)
SOURCE_FILES = ('Report205.tex', 'build.py', 'verify_exact.py', 'README.md',
                'SOURCES.md', 'manuscript_guards.json')
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def write_text(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding='utf-8', newline='\n')


def write_json(path, value):
    write_text(path, json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True)+'\n')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def derive():
    r, b, v = sp.symbols('r b v')
    order = 3
    p = [sp.Integer(0), sp.Integer(1)]
    for k in range(1, 2*order+2):
        p.append(sp.expand(r*sp.diff(p[-1], r)+(1+r)*p[-1]))
    beta = [sp.rf(sp.Rational(1, 2), k)*sp.rf(sp.Rational(3, 2), k)
            /(4**k*sp.factorial(k)) for k in range(order+1)]
    c = [sum(beta[k]*sp.rf(sp.Rational(3, 2)+k, m-k)/sp.factorial(m-k)
             for k in range(m+1)) for m in range(order+1)]
    exponent = {s: p[s+2]*v**(s+2)/sp.factorial(s+2)-b*r*v**s/sp.factorial(s)
                for s in range(1, 2*order+1)}
    h = [sp.Integer(1)]
    for k in range(1, 2*order+1):
        h.append(sp.expand(sum(s*exponent[s]*h[k-s] for s in range(1, k+1))/k))
    def gaussian(poly):
        return sp.factor(sum(coefficient*(-1)**(degree[0]//2)
            *sp.factorial2(degree[0]-1)/(1+r)**(degree[0]//2)
            for degree, coefficient in sp.Poly(poly, v).terms() if degree[0] % 2 == 0))
    saddle = [gaussian(h[2*j]) for j in range(order+1)]
    q = [sp.factor(sum(c[m]*(4*r)**m*saddle[j-m].subs(b, sp.Rational(3, 2)+m)
                      for m in range(j+1))) for j in range(order+1)]
    exported = []
    for j, item in enumerate(q):
        denominator, coefficients = REFERENCE_Q[j]
        expected = sum(sp.Integer(x)*r**k for k, x in enumerate(coefficients))/(
            denominator*(1+r)**(3*j))
        require(sp.cancel(item-expected) == 0, f'Symbolic Q{j} literal differs')
        numerator = sp.Poly(sp.cancel(item*denominator*(1+r)**(3*j)), r)
        require(numerator.degree() <= 4*j, f'Q{j} degree exceeds bound')
        exported.append({'degree_bound': 4*j, 'denominator_constant': denominator,
                         'numerator_ascending': [int(numerator.nth(k)) for k in range(4*j+1)]})
    bell = sp.factor(q[1]-saddle[1].subs(b, 0))
    require(sp.cancel(bell-3*r*(13*r**2+29*r+18)/(8*(1+r)**2)) == 0,
            'Bell comparison first correction differs')
    require(c == [1, sp.Rational(27, 16), sp.Rational(1245, 512), sp.Rational(27685, 8192)],
            'Endpoint coefficients differ')
    require([sp.limit(q[j]/r**j, r, sp.oo) for j in range(4)] ==
            [1, sp.Rational(115, 24), sp.Rational(13801, 1152), -sp.Rational(660793, 414720)],
            'Leading Q coefficient limits differ')
    # Direct checks of the inverse matching equations and their limiting shifts.
    u = r+sp.log(4)
    hlog = -sp.Rational(3, 2)*r-sp.log(1+r)/2-4-sp.Rational(3, 2)*sp.log(4)-sp.log(sp.pi)/2
    d0 = -hlog/u
    r1 = q[1]+sp.Rational(1, 12)
    d1 = -(r*d0**2/(2*(1+r))+sp.diff(hlog, r)*r*d0/(1+r)+r1)/u
    require(sp.simplify(u*d0+hlog) == 0, 'Inverse d0 matching equation fails')
    require(sp.simplify(u*d1+r*d0**2/(2*(1+r))+sp.diff(hlog, r)*r*d0/(1+r)+r1) == 0,
            'Inverse d1 matching equation fails')
    require(sp.limit(d0, r, sp.oo) == sp.Rational(3, 2), 'd0 limit differs')
    require(sp.limit(d1, r, sp.oo) == -sp.Rational(115, 24), 'd1 limit differs')
    n_of_r = 4*r*sp.exp(r)
    carrier = 4*sp.exp(r)*(r*r+(sp.log(4)-1)*r+1)
    require(sp.simplify(sp.diff(carrier, r)/sp.diff(n_of_r, r)-u) == 0,
            'Carrier first derivative differs')
    require(sp.simplify(sp.diff(u, r)/sp.diff(n_of_r, r)-r/(n_of_r*(1+r))) == 0,
            'Carrier second derivative differs')
    rseries = [r1, sp.factor(q[2]-q[1]**2/2),
               sp.factor(q[3]-q[1]*q[2]+q[1]**3/3-sp.Rational(1, 360))]
    write_json(ROOT/'data/polynomial_coefficients.json', exported)
    write_json(ROOT/'data/coefficients.json', {
        'P': [str(x) for x in p], 'beta': [str(x) for x in beta],
        'c': [str(x) for x in c], 'A': [str(x) for x in saddle],
        'Q': [str(x) for x in q], 'R': [str(x) for x in rseries],
        'bell_first_correction': str(bell),
        'd0': str(d0), 'd1': str(d1),
    })
    names = ('zero', 'one', 'two', 'three')
    macros = ['% Generated by build.py; do not edit.']
    for j, name in enumerate(names):
        macros.extend([r'\newcommand{\C'+name+'}{'+sp.latex(c[j])+'}',
                       r'\newcommand{\Q'+name+'}{'+sp.latex(q[j])+'}'])
        denominator, coefficients = REFERENCE_Q[j]
        numerator = sum(sp.Integer(x)*r**k for k, x in enumerate(coefficients))
        macros.extend([r'\newcommand{\Q'+name+'Numerator}{'+sp.latex(numerator)+'}',
                       r'\newcommand{\Q'+name+'Denominator}{'+sp.latex(denominator*(1+r)**(3*j))+'}'])
    q2_top = sum(sp.Integer(x)*r**k for k, x in enumerate(REFERENCE_Q[2][1]) if k >= 5)
    q2_bottom = sum(sp.Integer(x)*r**k for k, x in enumerate(REFERENCE_Q[2][1]) if k < 5)
    macros.append(r'\newcommand{\QtwoDisplay}{\frac{\begin{gathered}'+sp.latex(q2_top)
                  +r'\\{}+'+sp.latex(q2_bottom)+r'\end{gathered}}{1152(1+r)^6}}')
    macros.extend([r'\newcommand{\BellCorrection}{'+sp.latex(bell)+'}',
                   r'\newcommand{\FirstInverseShiftLimit}{\frac{3}{2}}',
                   r'\newcommand{\InverseShiftLimit}{-\frac{115}{24}}',
                   r'\newcommand{\QthreeLeadingLimit}{-\frac{660793}{414720}}'])
    write_text(ROOT/'tex/constants.tex', '\n'.join(macros)+'\n')
    write_text(ROOT/'tex/pdf_settings.tex',
        '% Generated deterministic pdfTeX settings.\n'
        '\\pdfinfoomitdate=1\n\\pdfsuppressptexinfo=15\n\\pdftrailerid{}\n')
    return r, q


def exact_checkpoints():
    row, catalan = [1], [1]
    records = []
    previous = 1
    for n in range(1, max(CHECKPOINTS)+1):
        row = [0]+[row[k-1]+(k*row[k] if k < len(row) else 0) for k in range(1, n+1)]
        cat_numerator = catalan[-1]*2*(2*n-1)
        require(cat_numerator % (n+1) == 0, f'Catalan integrality fails at n={n}')
        catalan.append(cat_numerator//(n+1))
        if n in CHECKPOINTS:
            a = sum(s*c for s, c in zip(row, catalan))
            bell = sum(row)
            require(a > previous and a > bell, f'Exact checkpoint order fails at n={n}')
            previous = a
            records.append({'n': n, 'a_n': str(a), 'bell_n': str(bell)})
    write_json(ROOT/'data/exact_values.json', records)
    return records


def numeric_at_precision(records, r_symbol, q, precision):
    with mp.workdps(precision):
        qfunc = [sp.lambdify(r_symbol, value, modules='mpmath') for value in q]
        asymptotic, inverse = [], []
        for rec in records:
            n, a, bell = rec['n'], int(rec['a_n']), int(rec['bell_n'])
            r = mp.lambertw(mp.mpf(n)/4)
            log_l = (mp.loggamma(n+1)-4+n/r+(mp.mpf('1.5')-n)*mp.log(r)
                     -2*mp.log(n)-mp.log(mp.pi*mp.sqrt(2))-mp.log1p(r)/2)
            ratio = mp.exp(mp.log(a)-log_l)
            partial, residuals, scaled = mp.mpf(0), [], []
            for j, qj in enumerate(qfunc):
                partial += qj(r)/n**j
                residuals.append(ratio-partial)
                scaled.append((ratio-partial)*(mp.mpf(n)/r)**(j+1))
            require(all(mp.isfinite(x) for x in [r, ratio]+scaled), 'Nonfinite asymptotic diagnostic')
            require(all(abs(residuals[j+1]) < abs(residuals[j]) for j in range(3)),
                    f'Finite-grid correction improvement fails at n={n}')
            require(0 < scaled[0] < 9 and 0 < scaled[1] < 27 and 0 < scaled[2] < 50
                    and -110 < scaled[3] < 0, f'Finite-grid residual regression fails at n={n}')
            ell, c = mp.log(a), mp.log(4)-1
            rho = mp.findroot(lambda t: 4*mp.exp(t)*(t*t+c*t+1)-ell, r)
            require(rho > 0 and abs(4*mp.exp(rho)*(rho*rho+c*rho+1)-ell) < mp.mpf(10)**(-precision+12)*ell,
                    f'Inverse carrier residual fails at n={n}')
            n0, u = 4*rho*mp.exp(rho), rho+mp.log(4)
            d0 = (mp.mpf('1.5')*rho+mp.log1p(rho)/2+4+mp.mpf('1.5')*mp.log(4)+mp.log(mp.pi)/2)/u
            d1 = -(rho*d0*d0/(2*(1+rho))-rho/(1+rho)*(mp.mpf('1.5')+1/(2*(1+rho)))*d0
                   +qfunc[1](rho)+mp.mpf(1)/12)/u
            err0, err1 = n0+d0-n, n0+d0+d1/n0-n
            require(0 < err0 < 1 and abs(err1) < abs(err0), f'Inverse finite-grid regression fails at n={n}')
            require(mp.ceil(n0+d0) == n+1, f'Observed I0 ceiling obstruction fails at n={n}')
            def decimal(value):
                return mp.nstr(value, 72)
            asymptotic.append({'n': n, 'r': decimal(r), 'ratio_to_L': decimal(ratio),
                'scaled_remainders': [decimal(x) for x in scaled],
                'relative_residuals': [decimal(x/ratio) for x in residuals],
                'nth_root_ratio_Bell': decimal(mp.exp((mp.log(a)-mp.log(bell))/n))})
            inverse.append({'n': n, 'rho': decimal(rho), 'n0': decimal(n0),
                'd0': decimal(d0), 'd1': decimal(d1), 'I0_minus_n': decimal(err0),
                'I1_minus_n': decimal(err1), 'scaled_I1_error': decimal(err1*n0*n0/rho)})
        return asymptotic, inverse


def compare_numeric(a, b, path='root'):
    if isinstance(a, dict):
        require(a.keys() == b.keys(), f'Precision replay keys differ at {path}')
        for key in a:
            compare_numeric(a[key], b[key], path+'.'+key)
    elif isinstance(a, list):
        require(len(a) == len(b), f'Precision replay lengths differ at {path}')
        for i, (x, y) in enumerate(zip(a, b)):
            compare_numeric(x, y, path+f'[{i}]')
    elif isinstance(a, str):
        with mp.workdps(110):
            x, y = mp.mpf(a), mp.mpf(b)
            require(abs(x-y) < mp.mpf('1e-62')*max(abs(y), mp.mpf('1e-30')),
                    f'80/110-digit precision replay differs at {path}')
    else:
        require(a == b, f'Precision replay values differ at {path}')


def tex_number(value, digits=8):
    if re.fullmatch(r'[+-]?\d+', str(value)):
        return str(value)
    with mp.workdps(90):
        text = mp.nstr(mp.mpf(value), digits, min_fixed=-3, max_fixed=5, strip_zeros=False)
    if 'e' in text:
        mantissa, exponent = text.split('e')
        return mantissa+r'\times10^{'+str(int(exponent))+'}'
    return text


def write_tables(asymptotic, inverse):
    first = [r'% Generated by build.py; finite diagnostics, not certified remainder bounds.',
             r'\begin{tabular}{rrrrrr}', r'\toprule',
             r'$n$ & $a_n/L_n$ & $E_0$ & $E_1$ & $E_2$ & $E_3$ \\', r'\midrule']
    for row in asymptotic:
        cells = [str(row['n']), row['ratio_to_L']]+row['scaled_remainders']
        first.append(' & '.join('$'+tex_number(x)+'$' for x in cells)+r' \\')
    first.extend([r'\bottomrule', r'\end{tabular}'])
    second = [r'% Generated by build.py; y=a_n at every row.',
              r'\begin{tabular}{rrrrr}', r'\toprule',
              r'$n$ & $d_0$ & $d_1$ & $I_0(a_n)-n$ & $I_1(a_n)-n$ \\', r'\midrule']
    for row in inverse:
        cells = [str(row['n'])]+[row[k] for k in ('d0', 'd1', 'I0_minus_n', 'I1_minus_n')]
        second.append(' & '.join('$'+tex_number(x)+'$' for x in cells)+r' \\')
    second.extend([r'\bottomrule', r'\end{tabular}'])
    write_text(ROOT/'tex/asymptotic_table.tex', '\n'.join(first)+'\n')
    write_text(ROOT/'tex/inverse_table.tex', '\n'.join(second)+'\n')


def check_manuscript():
    source = (ROOT/'Report205.tex').read_text(encoding='utf-8')
    guards = json.loads((ROOT/'manuscript_guards.json').read_text())
    require(guards['schema'] == 1, 'Unsupported manuscript guard schema')
    require(digest(ROOT/'Report205.tex') == guards['source_sha256'],
            'Manuscript changed: independently review constants and refresh the committed guards')
    pattern = re.compile(r'^% BEGIN VERIFIED ([A-Za-z0-9_-]+)\n(.*?)^% END VERIFIED \1\s*$', re.M | re.S)
    actual = {m.group(1): m.group(2) for m in pattern.finditer(source)}
    require(len(actual) == len(list(pattern.finditer(source))), 'Duplicate manuscript guard names')
    require(actual == guards['literal_blocks'], 'A reviewed literal manuscript block changed')
    require({'inverse_limit_explanation', 'rounding_coefficient', 'spectral_comparison'} <= set(actual),
            'Required literal guards for the inverse coefficient are missing')
    required_inputs = ('tex/pdf_settings', 'tex/constants', 'tex/asymptotic_table', 'tex/inverse_table')
    for name in required_inputs:
        require(r'\input{'+name+'}' in source, f'Manuscript missing generated input {name}')
    for phrase in guards.get('required_literals', []):
        require(phrase in source, f'Missing checked manuscript literal: {phrase}')
    return {'source_sha256': guards['source_sha256'], 'literal_block_names': sorted(actual),
            'generated_inputs': list(required_inputs), 'whole_source_guard': 'PASS'}


def prepare_tex(work):
    """Build a local format from installed TeX sources; isolate writable caches."""
    require(all(shutil.which(name) for name in ('pdflatex', 'pdftex', 'kpsewhich')),
            'pdflatex, pdftex and kpsewhich are required')
    environment = {'PATH': os.environ.get('PATH', os.defpath),
        'SOURCE_DATE_EPOCH': str(EPOCH), 'FORCE_SOURCE_DATE': '1',
        'TZ': 'UTC', 'LC_ALL': 'C', 'LANG': 'C', 'max_print_line': '1000',
        'openout_any': 'p', 'shell_escape': 'f'}
    for variable in ('HOME', 'TMPDIR', 'TEXMFVAR', 'TEXMFCONFIG',
                     'TEXMFCACHE', 'TEXMFHOME', 'VARTEXFONTS'):
        directory = work/variable.lower()
        directory.mkdir()
        environment[variable] = str(directory)
    def run(command):
        result = subprocess.run(command, cwd=work, env=environment, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        require(result.returncode == 0, 'TeX setup failed: '+str(command)+'\n'+result.stdout[-12000:])
        return result.stdout.strip()
    distribution = Path(run(['kpsewhich', '-var-value=TEXMFDIST']))
    require(distribution.is_dir(), 'Installed TeX distribution was not found')
    trees = [distribution]
    sibling = distribution.parent.parent/'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    environment['TEXMF'] = '{'+','.join(str(path) for path in trees)+'}'
    environment['TEXFORMATS'] = str(work)+os.pathsep
    environment['TEXFONTMAPS'] = str(work)+os.pathsep
    run(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
         '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'])
    require((work/'pdflatex.fmt').is_file(), 'TeX format was not created')
    maps = []
    for name in ('cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'lm.map'):
        path = Path(run(['kpsewhich', name]))
        require(path.is_file(), 'Installed font map was not found: '+name)
        maps.append(path.read_bytes())
    (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    return environment


def typeset():
    # No format, font-map cache or TeX intermediate is distributed.
    with tempfile.TemporaryDirectory(prefix='report205-tex-') as temporary:
        work = Path(temporary)
        environment = prepare_tex(work)
        previous_state = None
        for run in range(1, 7):
            process = subprocess.run(['pdflatex', '-no-shell-escape', '-halt-on-error',
                                      '-interaction=nonstopmode', '-output-directory='+temporary,
                                      'Report205.tex'], cwd=ROOT, env=environment,
                                     text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                     timeout=300)
            if process.returncode:
                raise RuntimeError(f'pdflatex pass {run} failed:\n'+process.stdout)
            state = tuple((work/('Report205.'+suffix)).read_bytes()
                          if (work/('Report205.'+suffix)).exists() else b''
                          for suffix in ('aux', 'toc', 'out'))
            if run >= 2 and state == previous_state:
                break
            previous_state = state
        else:
            raise RuntimeError('TeX references did not stabilize in six passes')
        log = (work/'Report205.log').read_text(errors='replace')
        shutil.copyfile(work/'Report205.pdf', ROOT/'Report205.pdf')
        defects = re.findall(r'(?:Overfull[^\n]*|Missing character:[^\n]*|'
                            r'[^\n]*undefined references[^\n]*|[^\n]*undefined citations[^\n]*|'
                            r'[^\n]*multiply-defined labels[^\n]*)', log)
        require(not defects, 'TeX unresolved references or layout defects: '+'; '.join(defects))
        require('Rerun to get cross-references right' not in log,
                'TeX references are still unstable after the repeated passes')
    return subprocess.run(['pdflatex', '--version'], text=True, stdout=subprocess.PIPE,
                          check=True).stdout.splitlines()[0]


def package():
    paths = list(SOURCE_FILES)+['Report205.pdf']
    paths += [p.relative_to(ROOT).as_posix() for folder in ('data', 'tex')
              for p in (ROOT/folder).iterdir() if p.is_file()]
    paths = sorted(paths)
    require(len(paths) == len(set(paths)), 'Duplicate public member names')
    for name in paths:
        require((ROOT/name).is_file() and not (ROOT/name).is_symlink(), f'Missing or linked public member: {name}')
    manifest = {'schema': 1, 'source_date_epoch': EPOCH, 'hash_algorithm': 'SHA-256',
        'members': [{'path': name, 'bytes': (ROOT/name).stat().st_size, 'sha256': digest(ROOT/name)} for name in paths],
        'self_exclusion': 'MANIFEST.json is not self-hashed. Its hash is in archive_manifest.json.',
        'archive_identity': 'archive_manifest.json records the ZIP and every ZIP member, including MANIFEST.json; it is outside the ZIP to avoid self-reference.'}
    write_json(ROOT/'MANIFEST.json', manifest)
    paths = sorted(paths+['MANIFEST.json'])
    zip_date = datetime.fromtimestamp(EPOCH, timezone.utc).timetuple()[:6]
    with zipfile.ZipFile(ROOT/ARCHIVE, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in paths:
            member = zipfile.ZipInfo(name, date_time=zip_date)
            member.create_system = 3
            member.external_attr = 0o100644 << 16
            member.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(member, (ROOT/name).read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    # Read the archive back and check all identities, not merely the source files.
    members = []
    with zipfile.ZipFile(ROOT/ARCHIVE) as archive:
        require(archive.namelist() == paths, 'ZIP member list differs')
        require(archive.testzip() is None, 'ZIP CRC test failed')
        for name in paths:
            payload = archive.read(name)
            require(payload == (ROOT/name).read_bytes(), f'ZIP member differs: {name}')
            members.append({'path': name, 'bytes': len(payload), 'sha256': sha256(payload).hexdigest()})
    write_json(ROOT/'archive_manifest.json', {'schema': 1, 'archive': ARCHIVE,
        'archive_bytes': (ROOT/ARCHIVE).stat().st_size, 'archive_sha256': digest(ROOT/ARCHIVE),
        'all_zip_members': members, 'all_zip_members_verified': True,
        'exclusions': [ARCHIVE, 'archive_manifest.json', 'TeX logs and intermediate files',
                       '__pycache__ and temporary directories']})
    return len(paths)


def verify_replay():
    identity = json.loads((ROOT/'archive_manifest.json').read_text())
    names = [record['path'] for record in identity['all_zip_members']]
    names += [ARCHIVE, 'archive_manifest.json']
    reference = {name: (ROOT/name).read_bytes() for name in names}
    with tempfile.TemporaryDirectory(prefix='report205-replay-') as temporary:
        for label, options in (('normal', []), ('optimized', ['-O'])):
            destination = Path(temporary)/label
            destination.mkdir()
            with zipfile.ZipFile(ROOT/ARCHIVE) as archive:
                archive.extractall(destination)
            print(f'Running complete extracted {label} rebuild...', flush=True)
            process = subprocess.run([sys.executable]+options+['build.py'], cwd=destination,
                                     text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if process.returncode:
                raise RuntimeError(f'Extracted {label} build failed:\n'+process.stdout)
            for name, expected in reference.items():
                require((destination/name).is_file(), f'{label} rebuild missing {name}')
                require((destination/name).read_bytes() == expected,
                        f'Byte identity failure in {label} rebuild: {name}')
            replay_identity = json.loads((destination/'archive_manifest.json').read_text())
            require(replay_identity == identity, f'{label} all-member identity manifest differs')
            print(f'PASS: {label} extracted rebuild; {len(names)} public files and ZIP identity match.', flush=True)
    print('COMPLETE EXTRACTED NORMAL / -O REPLAY: PASS', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-only', action='store_true',
                        help='Regenerate and test data only; does not claim a complete reproducibility build.')
    parser.add_argument('--verify-replay', action='store_true',
                        help='After the complete build, compare fresh normal and -O extracted rebuilds.')
    arguments = parser.parse_args()
    require(not (arguments.data_only and arguments.verify_replay),
            '--data-only cannot be combined with --verify-replay')
    print('Deriving exact corrections Q0-Q3...', flush=True)
    r, q = derive()
    exact = independent_exact_checks(ROOT/'data')
    write_json(ROOT/'data/exact_checks.json', exact)
    print('Enumerating exact Stirling-Catalan checkpoints through n=2000...', flush=True)
    records = exact_checkpoints()
    low = numeric_at_precision(records, r, q, 80)
    high = numeric_at_precision(records, r, q, 110)
    compare_numeric(list(low), list(high))
    # Stable public digits are generated from the higher-precision run.
    asymptotic, inverse = high
    write_json(ROOT/'data/numerical_checks.json', asymptotic)
    write_json(ROOT/'data/inverse_checks.json', inverse)
    write_tables(asymptotic, inverse)
    validation = {'status': 'PASS', 'exact_checks': exact,
        'numeric_checkpoints': list(CHECKPOINTS), 'numerical_precisions_digits': [80, 110],
        'precision_replay_relative_tolerance': '1e-62',
        'finite_grid_checks': ['successive Q0-Q3 truncations improve relative residuals',
            'scaled residual regression ranges', 'carrier equation residual',
            'inverse first correction improves absolute error', 'I0 ceiling equals n+1 at each checkpoint'],
        'symbolic_checks': ['Q0-Q3 independent coefficient literals', 'Qj numerator degree bounds',
            'endpoint c0-c3', 'Bell first correction', 'Qj leading limits',
            'inverse d0/d1 matching equations and limits', 'carrier first and second derivatives'],
        'limitations': 'Numerical checks are finite floating diagnostics, not interval-certified global remainders, onset estimates, or inverse rounding guarantees.',
        'python': platform.python_version(), 'sympy': sp.__version__, 'mpmath': mp.__version__,
        'test_style': 'explicit exceptions; identical tests under python -O'}
    if arguments.data_only:
        write_json(ROOT/'data/validation.json', validation)
        print('Data-only checks PASS. PDF and ZIP were not built.', flush=True)
        return
    validation['manuscript'] = check_manuscript()
    print('Typesetting Report205.tex at least twice, through reference stabilization...', flush=True)
    validation['pdf_engine'] = typeset()
    write_json(ROOT/'data/validation.json', validation)
    count = package()
    print(f'PASS: {count} ZIP members, every member verified; {ARCHIVE}', flush=True)
    print('ZIP SHA-256: '+digest(ROOT/ARCHIVE), flush=True)
    if arguments.verify_replay:
        verify_replay()


if __name__ == '__main__':
    main()
