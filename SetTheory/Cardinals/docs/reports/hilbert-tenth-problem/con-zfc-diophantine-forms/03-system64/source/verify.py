#!/usr/bin/env python3
"""Read-only reproduction of the finite parts of the K215 construction.

This does not prove compiler universality or Con(ZFC). It reconstructs the
finite coefficient recipe and literal polynomial circuits, checks all pinned
inputs, and compares independent displayed formulas on diagnostic values.
Only --receipt writes a user-specified output. Python 3.9+ standard library.
"""
from pathlib import Path
from tempfile import TemporaryDirectory
from hashlib import sha256
import argparse
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
COMMIT = 'cdd582bec13f908df3711fa9e05d1ddac368a5db'
TABLE_HASH = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def run(script, *args):
    command = [sys.executable, str(ROOT/'source'/script), *map(str, args)]
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    require(result.returncode == 0,
            script + ' failed:\n' + result.stdout + '\n' + result.stderr)
    return result.stdout.strip()


def evaluate(rows, environment):
    values = dict(environment)
    for name, op, lhs, rhs in rows:
        a = values[lhs] if isinstance(lhs, str) else lhs
        b = values[rhs] if isinstance(rhs, str) else rhs
        require(op in ('+', '-', '*'), 'unexpected circuit operation')
        values[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return values


def displayed(values, ordinary):
    """Direct transcription of the report, independent of source row names."""
    J, F, alpha = (values[n] for n in ('Jrep', 'F', 'alpha'))
    t, h, i, T = (values[n] for n in ('transport_quotient', 'h', 'i', 'auxiliary_quotient'))
    s, w, tau = (values[n] for n in ('s', 'w', 'tau_root'))
    eta, zeta, y, Z, gamma = (values[n] for n in ('eta', 'zeta', 'y_aux', 'Z', 'gamma'))
    q = values['Bm1']*J+1
    X, Y = w*q, s*q**3
    E, k = X*Y, eta+zeta
    c, a = k*Y+eta, E+Y
    H = 4*a+3
    Delta, D0 = a*a+H, X+a*c+gamma*H
    C = q-F-Z-alpha-values['twice_cell_bits']
    W = C-Z
    R = (q*q-Z-q*F)*(q*q-1)+(values['MC']+q*values['MF'])*J
    L0 = E*(k*Y)
    N1, N2 = tau*tau-L0*(L0+k), D0*D0-Delta*c*c
    Nk = k-h*E-R
    Nt = (values['Kconstant']+w)*C+q-F-t*(q-1)
    marker = W-values['marker_constant']
    if ordinary:
        f = values['f']
        Ka = Delta*(f*f-1)
        V = c*(T*f-1)-R*f*f
        # This is the exact output order of the inert JSON comparison packet.
        return [N1-1, N2-1, Nk-1, Nt-1,
                Ka*(V*V-y*y)+y*y-1, (i*c*c)**2-Ka, marker]
    S = Delta*i*c*c
    Q = S*S
    D = 1+Delta*i*i*c**4
    bb, u = c+R*D, c*T
    AA = Q*(D*u*u+bb*bb)-(Q-1)*y*y-1
    BB = 2*Q*u*bb
    N = AA*AA-D*BB*BB
    return N1*N2*(1+marker*marker)*Nk*Nt*(N+1)-1


def displayed_checks():
    systems = read(ROOT/'artifacts/fixed_marker_systems.json')
    variants = read(ROOT/'artifacts/fixed_marker_variants.json')
    records = {}
    for ordinary, packet in ((True, systems['fixed_marker76_system']),
                              (False, variants['fixed_marker82'])):
        for case in range(40):
            # Generic signed and zero values test algebra off the solution set.
            # These small coefficient slices are diagnostic, not valid compilers.
            values = {name: ((case+7)*(j+3) % 11)-5
                      for j, name in enumerate(packet['free'])}
            values['Bm1'] = 3+case % 4
            source = evaluate(packet['source'], values)
            actual = ([source[lhs]-(source[rhs] if isinstance(rhs, str) else rhs)
                       for lhs, rhs in packet['comparisons']] if ordinary
                      else source[packet['output']])
            require(actual == displayed(values, ordinary), 'report formula mismatch')
        records['S16' if ordinary else 'P15'] = 40
    return records


def lean_table_binding():
    text = (ROOT/'vendor/KDense215.lean').read_text()
    literal = text.split('def rows215 :', 1)[1].split(':= [', 1)[1].split(']', 1)[0]
    actions = re.findall(r'\((true|false),\s*(true|false),\s*(\d+)\)', literal)
    require(len(actions) == 430, 'Lean literal table does not contain 430 actions')
    expected = {}
    for number, (write, right, target) in enumerate(actions):
        expected[(number//2, number % 2)] = (int(write == 'true'),
                                           'R' if right == 'true' else 'L', int(target))
    actual = {}
    for line in (ROOT/'source/k215.tm').read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        state, read_symbol, write, direction, target = line.split()
        key = (int(state), int(read_symbol))
        require(key not in actual, 'duplicate text transition')
        actual[key] = (int(write), direction, int(target))
    require(actual == expected, 'text table differs from Lean rows215')
    return len(actual)


def verify():
    manifest = read(ROOT/'vendor/manifest.json')
    require(manifest['commit'] == COMMIT, 'unexpected pinned commit')
    for name, entry in manifest['files'].items():
        require(digest(ROOT/'vendor'/name) == entry['sha256'], 'vendor hash: '+name)
    require(digest(ROOT/'source/k215.tm') == TABLE_HASH, 'literal K215 table hash')
    require((ROOT/'source/k215.tm').read_bytes() ==
            (ROOT/'vendor/k215.pinned.tm').read_bytes(), 'different K215 tables')
    regenerated = {}
    with TemporaryDirectory(prefix='k215-diophantine-') as temp:
        scratch = Path(temp)
        target = scratch/'artifacts'
        target.mkdir()
        run('compiler_k215.py', '--table', ROOT/'source/k215.tm', '--out', target)
        run('fixed_marker.py', '--root', ROOT/'vendor', '--out', target)
        run('domain_variants.py', '--root', scratch)
        for name in ('folded_machine.json', 'coefficient_recipe.json',
                     'compiler_checks.json', 'fixed_marker_variants.json',
                     'fixed_marker_systems.json', 'domain_variants.json'):
            require((target/name).read_bytes() == (ROOT/'artifacts'/name).read_bytes(),
                    'regenerated file differs: '+name)
            regenerated[name] = digest(target/name)
        review_path = scratch/'review.json'
        run('review_fixed_marker.py', '--upstream', 'vendor', '--artifacts', 'artifacts',
            '--output', review_path)
        review = read(review_path)
        require(review == read(ROOT/'checks/independent_review.json'),
                'independent review receipt differs')
        require(review['status'] == 'PASS', 'independent source audit')
    recipe = read(ROOT/'artifacts/coefficient_recipe.json')
    require(recipe['inner_bits'] == 5**42, 'inner radix exponent')
    require(recipe['cell_radix_length'] == 5**43, 'cell length')
    require(recipe['cell_bits'] == 5**85, 'cell bit width')
    require(recipe['corrected_unit_mod5'] == 2 and recipe['high_correction'] == 0,
            'compiler congruence')
    require(pow(2, recipe['inner_bits'], 5) == 2, 'inner radix mod 5')
    return {
        'status': 'PASS', 'repository_commit': COMMIT,
        'vendor_files_verified': len(manifest['files']),
        'k215_table_sha256': TABLE_HASH,
        'literal_actions_matching_Lean_rows215': lean_table_binding(),
        'regenerated_bytes_identical': regenerated,
        'independent_source_audit': 'PASS',
        'displayed_formula_diagnostic_cases': displayed_checks(),
        'domain_variants': {'integer_variables': [45, 48],
                            'quadratic_variables': 128, 'quadratic_equations': 87,
                            'quartic_degree': 4},
        'scope': ('Finite machine/layout, source, arithmetic and domain checks. '
                  'No proof by testing of universality, no ZFC consistency proof, '
                  'no new full Lean/Rocq build.')
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path,
                        help='Optionally save the deterministic check receipt.')
    args = parser.parse_args()
    result = verify()
    if args.receipt:
        args.receipt.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
