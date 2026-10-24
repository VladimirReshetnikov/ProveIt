#!/usr/bin/env python3
"""Exact composition of signed bootstrap, determinant, and pair guards.

Only Python's standard library is needed.  Fixed ports are never counted as
unknowns.  The complete integer bytes are bundled and checked separately.
"""
from pathlib import Path
import gzip
import hashlib
import json
from polynomial import Poly, parse, require

ROOT = Path(__file__).resolve().parent
PORTS = {'beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B'}


def write(name, data):
    (ROOT/name).write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')


def load(name):
    return json.loads((ROOT/name).read_text())


def check_sources():
    for record in load('SOURCE_PINS.json')['files']:
        raw = (ROOT/record['local']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == record['sha256'],
                'source SHA-256: '+record['local'])
        blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob == record['git_blob'], 'source Git blob: '+record['local'])
    values = {}
    for name, record in load('coefficients/BINDING.json')['payloads'].items():
        raw = gzip.decompress((ROOT/'coefficients'/record['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest() == record['raw_sha256'],
                'fixed integer SHA-256: '+name)
        value = int.from_bytes(raw, 'little')
        require(value.bit_length() == record['bits'], 'fixed integer bits: '+name)
        values[name] = value
    require(values['beta'] == (1 << 1064921)-1, 'literal Mersenne beta')
    require(values['cone_A'] == 1 << 1113, 'literal cone scale A')
    require(values['cone_B'] == 1 << 666104, 'literal cone scale B')
    require(0 < values['MC'] < values['beta'] < values['MF'] < 2*values['beta'],
            'actual native mask bounds')
    return {name: value.bit_length() for name, value in values.items()}


def eliminate(vs, rows, name, expression):
    rhs = parse(expression)
    require(name not in rhs.symbols(), 'acyclic monic elimination: '+name)
    lhs = Poly.symbol(name)-rhs
    matches = [i for i, row in enumerate(rows) if row == lhs or row == -lhs]
    require(len(matches) == 1, 'unique defining row: '+name)
    new_rows = [row.substitute({name: rhs}) for i, row in enumerate(rows)
                if i != matches[0]]
    return [v for v in vs if v != name], new_rows


def packet(name, vs, rows, degree, witness):
    live = set().union(*(p.symbols() for p in rows))
    require(live-PORTS == set(vs), name+': all and only listed variables live')
    require(live <= set(vs)|PORTS, name+': no hidden symbols')
    polynomial = sum((p*p for p in rows), Poly())
    require(polynomial.degree(vs) == degree, name+': exact symbolic degree')
    expected = witness['coefficient']
    require(polynomial.coefficient(witness['monomial'], vs) == expected,
            name+': fixed-port-independent exact leading coefficient')
    leading_identity = None
    if name in {'degree12_23','degree10_24','degree14_22'}:
        leading = Poly({mon:coef for mon,coef in polynomial.terms.items()
                        if sum(exponent for symbol,exponent in mon if symbol in vs)==degree})
        leading_identity = {
            'degree12_23':('256*beta**4*J**4*u**8+I**4*f**4*o**4'
                           '+eta**4*(-f*o+j*c+h*E)**4'),
            'degree10_24':('64*a**4*gamma**2*(c+2*gamma)**2*(a-E)**2'
                           '+4*I**4*f**2*o**2*(c+y)**2'),
            'degree14_22':'4*a**4*f**6*o**2*(c+y)**2'}[name]
        require(leading == parse(leading_identity),
                'exact highest homogeneous form of '+name)
    data = {'name': name, 'domain': 'unrestricted integers', 'variables': vs,
            'variable_count': len(vs), 'fixed_numerals': sorted(PORTS),
            'coefficient_binding': 'coefficients/BINDING.json',
            'residuals': [p.expression() for p in rows],
            'residual_count': len(rows), 'exact_degree': degree,
            'residual_degrees': [p.degree(vs) for p in rows],
            'single_polynomial': 'sum of the squares of the listed residuals',
            'exact_degree_certificate': witness,
            'symbolic_port_expansion_terms': len(polynomial.terms),
            'proof': 'PROOF.md',
            'scope': 'new algebraic composition; inherits named source75, source71, and source64 compiler/calibration theorems'}
    if leading_identity is not None:
        data['exact_leading_homogeneous_form'] = leading_identity
    write(name+'.json', data)
    return {key: data[key] for key in ['name', 'variable_count', 'residual_count',
            'exact_degree', 'symbolic_port_expansion_terms', 'exact_degree_certificate']}


def recover_signed34():
    old = load('upstream/quartic41.json')
    rows = [parse(s) for s in old['residuals']]
    aliases = {'q': parse('beta*J+1')}
    aliases['C'] = parse('q-F-alpha', aliases)
    # Source75's two genuine existential transformations, checked literally.
    rows[13] = parse('(K0*q+X)*C-q*F-Z*(q-1)', aliases)
    rows[22] = parse('X-4*q*u**2', aliases)
    rows.pop(2)
    vs = [v for v in old['variables'] if v not in {'w_scale', 'z'}]+['Z']
    ref40 = load('upstream/signed40_sextic.json')
    require(vs == ref40['variables'], 'signed40 variable identity')
    require(rows == [parse(s) for s in ref40['residuals']], 'signed40 row identity')
    # The shear tau_old=tau_new+P-k is invertible over the integers.
    center = parse('tau+P-eta-zeta')
    rows = [row.substitute({'tau': center}) for row in rows]
    for v, rhs in [
        ('P', 'eta+zeta+E*(c-eta)'),
        ('F2', 'f**2'), ('g', 'y**2-V**2'),
        ('N', '(beta*J+1)*(L+1)'), ('C2', 'c**2'),
        ('X', 'D-a*c-gamma*(4*a+3)')]:
        vs, rows = eliminate(vs, rows, v, rhs)
    ref34 = load('upstream/signed34_sextic.json')
    require(vs == ref34['variables'], 'signed34 variable identity')
    require(rows == [parse(s) for s in ref34['residuals']], 'signed34 row identity')
    return vs, rows


def cone31():
    vs, rows = recover_signed34()
    expected = [parse('F*alpha-1-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)'),
                parse('F*(beta*J+1-F-alpha)-1-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)')]
    require(rows[16:18] == expected, 'the two exact old sign guards')
    aliases = {'q': parse('beta*J+1')}
    aliases['C'] = parse('q-F-alpha', aliases)
    aliases['U'] = parse('cone_A*F', aliases)
    aliases['Vn'] = parse('cone_B*C', aliases)
    determinant = parse('U*Vn-(q-U-Vn)**2', aliases)
    cone_guard = determinant-parse('1+cone_pos1**2+cone_pos2**2+cone_pos3*(cone_pos3+1)')
    removed = {prefix+'_pos'+str(i) for prefix in ['FA', 'FC'] for i in range(1,4)}
    vs = [v for v in vs if v not in removed]+['cone_pos1','cone_pos2','cone_pos3']
    rows = rows[:16]+[cone_guard, rows[18]]
    require(len(vs) == 31 and len(rows) == 18, '31-variable dimensions')
    return vs, rows, determinant


def merge_guards(vs, rows, determinant):
    positive = parse('eta*zeta')
    cone = determinant-parse('1+cone_pos1**2+cone_pos2**2+cone_pos3*(cone_pos3+1)')
    ez = positive-parse('1+eta_zeta_pos1**2+eta_zeta_pos2**2+eta_zeta_pos3*(eta_zeta_pos3+1)')
    require(sum(row == cone for row in rows) == 1, 'unique determinant guard')
    require(sum(row == ez for row in rows) == 1, 'unique eta-zeta guard')
    cut = {prefix+str(i) for prefix in ['cone_pos','eta_zeta_pos'] for i in range(1,4)}
    add = ['pair_root','pair_pos1','pair_pos2','pair_pos3']
    vs = [v for v in vs if v not in cut]+add
    center = parse('pair_root**2')-determinant-positive+1
    merged = determinant*positive-center*center-parse('1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)')
    rows = [row for row in rows if row != cone and row != ez]+[merged]
    return vs, rows


def diagnostics():
    # These examples are diagnostics only; PROOF.md proves the universal lemma.
    from math import isqrt
    count = 0
    for x in range(1,151):
        for y in range(1,151):
            n = x+y-1
            m = isqrt(n)
            t = m if n-m*m <= m else m+1
            require(x*y-(t*t-x-y+1)**2 > 0, 'positive-pair diagnostic')
            count += 1
    signed = 0
    for x in range(-20,21):
        for y in range(-20,21):
            for t in range(-12,13):
                if x*y-(t*t-x-y+1)**2 > 0:
                    require(x > 0 and y > 0, 'signed-pair diagnostic')
                signed += 1
    return {'positive_pairs': count, 'signed_triples': signed,
            'scope': 'finite diagnostics, not the proof of the universal lemma'}


def main():
    bits = check_sources()
    vs, rows, determinant = cone31()
    audits = [packet('sextic31', vs, rows, 6,
                     {'monomial': {'r':2,'c':4}, 'coefficient':4})]
    for v, rhs in [('L','(beta*J+1)**2-1'),
                   ('Delta','a**2+4*a+3'), ('Baux','I**2')]:
        vs, rows = eliminate(vs, rows, v, rhs)
    require(len(vs) == 28 and len(rows) == 15, '28-variable intermediate')
    vs, rows = merge_guards(vs, rows, determinant)
    require(len(vs) == 26 and len(rows) == 14, '26-variable dimensions')
    vs26, rows26 = list(vs), list(rows)
    audits.append(packet('octic26', vs, rows, 8,
                         {'monomial': {'pair_root':8}, 'coefficient':1}))
    vs, rows = eliminate(vs, rows, 'zeta','1-V+j*c+h*E-eta')
    require(len(vs) == 25 and len(rows) == 13, '25-variable dimensions')
    audits.append(packet('degree12_25', vs, rows, 12,
                         {'monomial': {'eta':4,'j':4,'c':4}, 'coefficient':1}))
    vs, rows = eliminate(vs, rows, 'D',
                         '4*(beta*J+1)*u**2+a*c+gamma*(4*a+3)')
    vs, rows = eliminate(vs, rows, 'V', 'f*o-c')
    require(len(vs) == 23 and len(rows) == 11, '23-variable dimensions')
    audits.append(packet('degree12_23', vs, rows, 12,
                         {'monomial': {'eta':4,'j':4,'c':4}, 'coefficient':1}))
    vs23, rows23 = list(vs), list(rows)

    # At degree ten, keep zeta and absorb the two norm definitions instead.
    # Shear the auxiliary root by the integral polynomial f*o.
    vs, rows = list(vs26), [row.substitute({'y':parse('f*o+y')}) for row in rows26]
    vs, rows = eliminate(vs, rows, 'D',
                         '4*(beta*J+1)*u**2+a*c+gamma*(4*a+3)')
    vs, rows = eliminate(vs, rows, 'V', 'f*o-c')
    aliases = {'q':parse('beta*J+1'), 'H':parse('4*a+3'),
               'Y':parse('a-E')}
    aliases['X']=parse('4*q*u**2',aliases)
    aliases['Delta']=parse('a**2+H',aliases)
    aliases['b']=parse('a*c+gamma*H',aliases)
    aliases['D']=parse('X+b',aliases)
    main_norm=parse('D**2-Delta*c**2-1',aliases)
    reduced=parse('X*E+2*E*b+Y*(H*(2*a*c*gamma+H*gamma**2-c**2)-1)',aliases)
    require(reduced == parse('Y',aliases)*main_norm+
            parse('X+2*b',aliases)*parse('E-X*Y',aliases),
            'main-norm exact saturated row identity')
    require(sum(row==main_norm for row in rows)==1,'unique main norm to replace')
    rows=[reduced if row==main_norm else row for row in rows]
    require(len(vs)==24 and len(rows)==12,'24-variable dimensions')
    audits.append(packet('degree10_24',vs,rows,10,
                         {'monomial':{'I':4,'f':2,'o':2,'y':2},'coefficient':4}))

    # At degree fourteen, use the strong norm to remove I from the auxiliary
    # norm before deleting its monic definition. This prevents a degree-twenty
    # result from naive substitution.
    vs, rows = list(vs23), [row.substitute({'y':parse('f*o+y')}) for row in rows23]
    aliases={'Delta':parse('a**2+4*a+3'), 'V':parse('f*o-c'),
             'yold':parse('f*o+y')}
    aliases['Q']=parse('Delta*(f**2-1)',aliases)
    old_aux=parse('yold**2-I**2*(yold**2-V**2)-1',aliases)
    new_aux=parse('yold**2-Q*(c+y)*(2*f*o+y-c)-1',aliases)
    require(new_aux == old_aux+parse('I**2-Q',aliases)*
            parse('yold**2-V**2',aliases),'auxiliary exact row operation')
    require(sum(row==old_aux for row in rows)==1,'unique auxiliary norm to replace')
    rows=[new_aux if row==old_aux else row for row in rows]
    vs, rows=eliminate(vs,rows,'I','(2*r+1)*c**2')
    require(len(vs)==22 and len(rows)==10,'22-variable dimensions')
    audits.append(packet('degree14_22',vs,rows,14,
                         {'monomial':{'a':4,'f':6,'o':2,'y':2},'coefficient':4}))
    result = {'status':'PASS', 'results':audits, 'coefficient_bits':bits,
              'diagnostics':diagnostics(), 'proof_status':'ordinary mathematical proof; no new end-to-end proof-assistant certificate'}
    write('CHECKS.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
