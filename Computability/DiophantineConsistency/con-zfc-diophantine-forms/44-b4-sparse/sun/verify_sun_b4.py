#!/usr/bin/env python3
"""Independent literal B4 transcription and exact finite certificates.

Source coefficient reconstruction and norm expansion are inherited audit
utilities, not a formalization of the imported number-theoretic theorems.
"""
from pathlib import Path
from itertools import combinations_with_replacement
from math import gcd
import json,random,sys,hashlib
ROOT=Path(__file__).resolve().parent
if not __debug__:
    raise RuntimeError('Run without -O: assertions are part of the verification.')
sys.path.insert(0,str(ROOT/'sources'))
import verify_signed10 as old
from verify_signed10 import geometric,evaluate_norm,degree_certificate,fixed_leaves
from circuit import evaluate
from build_sun_b4 import construct

def literal(v, fixed, constants, modulus, merger, merged, scheme, norm):
    """Independent scalar transcription, with a literal 402-term source sum."""
    p = modulus
    adaptive = scheme != 'sun'
    red = lambda x: x % p
    weights=json.loads((ROOT/'B4_OPTIMIZED.json').read_text())['witness_weights']
    t, Lcode = max(weights), 4*max(weights)
    b = red(1 + 3 * v['f'])
    base = red(fixed['beta_sun'] * pow(b, 4, p))
    ell = sum(pow(base, w, p) for w in weights) % p
    Dcode = sum(fixed[row['name']] * pow(base, Lcode - sum(a*w for a,w in zip(row['alpha'][1:],weights)), p)
                for row in constants['coefficient_records']) % p
    N0 = pow(base, t + 1, p)
    N1 = red(4 * pow(base, 8 * t + 1, p))
    N = red(N0 * N1)
    Mcode = red(N0 - 1 - (b - 1) * ell)
    Tcode = red(Mcode + (base - 2) * pow(base, Lcode, p) * N0)
    Jcode = red(2 * pow(1 + v['g'], 4, p) * Dcode + base * geometric(base, 8 * t + 1, p))
    Scode = red(v['g'] + Jcode * N0)
    Rcode = red((Scode + Tcode + 1) * N + Tcode + 1)
    X = red((N - 1) * Rcode)
    Y = red(N * N)
    cap = red(b * pow(base, t, p))
    L = red(v['l'] * Y)
    U = red(2 * L * X)
    V = red(4 * v['g'] * v['w'] * Y)
    W = red(b * v['w'])
    A = red(U * (V + 1))
    B = red(2 * X + 1)
    C = red(B + (A - 2) * v['h'])
    K = red(X + 1 + v['k'] * (U * U * V - 2))
    S = red(2 * A - 5)
    T = red(3 * W * C - 2 * (W * W - 1))
    R2 = red((U ** 4 * V * V - 4) * K * K + 4)
    Delta = red(8 * cap ** 3 * v['g'] * K * K - v['g'] ** 2 * (32 * (C - K * L) ** 2 * cap ** 3 + v['g'] ** 2 * K * K))
    O0 = red(v['f'] ** 2 * v['l'] ** 2 * Delta)
    xi = red(v['z'] * v['x'])
    D = red((A * A - 4) * C * C + 4)
    E = red(C * C * D * xi)
    F = red(4 * (A * A - 4) * E * E + 1)
    Gstar = red(2 * (A + 2) * (A - 2) ** 2 * E * E - 1)
    Omega = red(16 * E)
    Hstar = red(C + (B - C) * F + Omega * F * v['y'])
    Istar = red((Gstar * Gstar - 1) * Hstar * Hstar + 1)
    Sigma = red(xi * pow(S, merger, p))
    r = red(T + S * v['y'])
    if merger == 5:
        Theta = red((r ** 3 - r * S * S - S ** 3) * (r * r + 23 * S * S))
    else:
        Theta = red((r * r - 13 * S * S) * (r * r - 17 * S * S) * (r * r - 221 * S * S))
    if merged:
        positivity = red(b * (1 + (3 * O0 - 4) * b * b * v['z'] ** 2))
        radicands = [positivity, R2, red(D * F * Istar)] if adaptive else [positivity, red(D * F * Istar), R2]
    else:
        radicands = [b, red((3 * O0 - 4) * v['z'] ** 2 + 1), red(D * F * Istar), R2]
    if scheme == 'structural':
        weight1 = radicands[0]
        weight2 = red(weight1 * ((U * U * V) ** 2 + K * K + 3))
        weights = [1, weight1, weight2]
    elif adaptive:
        weight1 = red(1 + radicands[0] ** 2)
        weight2 = red(weight1 * (1 + radicands[1] ** 2))
        weights = [1, weight1, weight2]
    else:
        weight = red(1 + sum(ai * ai for ai in radicands))
        weights = [pow(weight, i, p) for i in range(len(radicands))]
    center = red(Sigma * v['m'] - Theta)
    scaled = [red(Sigma * Sigma * weights[i] ** 2 * ai) for i, ai in enumerate(radicands)]
    answer = evaluate_norm(norm, [center] + scaled, p)
    named = dict(b=b, base=base, ell=ell, Dcode=Dcode, N0=N0, N1=N1, N=N,
                 Mcode=Mcode, Tcode=Tcode, Jcode=Jcode, Scode=Scode, Rcode=Rcode,
                 X=X, Y=Y, Ccap=cap, Lsmall=L, U=U, V=V, Wsmall=W, A=A, Bsmall=B,
                 C=C, K=K, Ssmall=S, Tsmall=T, R2=R2, Delta=Delta, O0=O0, xi=xi,
                 D=D, E=E, F=F, Gstar=Gstar, Omega=Omega, Hstar=Hstar, Istar=Istar,
                 Sigma=Sigma, Theta=Theta, norm_center=center, F10=answer)
    if adaptive:
        named.update(norm_weight1=weight1, norm_weight2=weight2)
    else:
        named['norm_weight'] = weight
    named.update({'A' + str(i + 1): ai for i, ai in enumerate(radicands)})
    return answer, named


def run():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for record in pins['files']:
        data=(ROOT/record['file']).read_bytes()
        assert hashlib.sha256(data).hexdigest()==record['sha256']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==record['git_blob_sha']
    certificate=json.loads((ROOT/'B4_OPTIMIZED.json').read_text())
    positions=certificate['weights_with_zero']
    construction=json.loads((ROOT/'B4_CERTIFICATE.json').read_text())
    modulus=certificate['modulus']
    assert gcd(certificate['multiplier'],modulus)==1
    reconstructed=sorted((certificate['multiplier']*v-certificate['translation_after_multiplier'])%modulus
                         for v in construction['positions_including_zero'])
    assert reconstructed==positions
    assert positions[0]==0 and positions[-1]==610895 and len(positions)==32
    seen=set()
    for ix in combinations_with_replacement(range(32),4):
        code=sum(positions[i] for i in ix)
        assert code not in seen
        seen.add(code)
    assert len(seen)==52360
    # The direct certificate above suffices, independently of construction.
    constants, coefficient_report=old.source_coefficients()
    ports,fixed_report=old.fixed_ports(constants)
    (old.ROOT/'generated').mkdir(exist_ok=True)
    norm,norm_report=old.norm_polynomial(3)
    body,aliases=construct()
    assert body['witness_positions']==positions[1:]
    assert body['path_base']=='Directory containing this generated JSON file'
    instance_path=ROOT/'generated'/body['fixed_binding']
    assert instance_path.resolve()==(ROOT/'INSTANCE.json').resolve()
    assert (ROOT/'generated'/body['proof']).is_file()
    instance=json.loads(instance_path.read_text())
    assert instance['witness_positions']==positions[1:]
    assert (instance['t'],instance['Lcode'])==(body['t'],body['Lcode'])
    assert instance['convolution_top']==8*body['t']
    assert instance['primary_equation']=='generated/sun_b4.json'
    degrees=[];comparison_count=0
    rng=random.Random(20261023)
    for prime in (101,1009,1000003):
        fixed=fixed_leaves(constants,ports,prime)
        degrees.append(degree_certificate(body,fixed,prime))
        for rep in range(40):
            v={name:rng.randrange(-20,21) for name in body['variables']}
            actual,an=evaluate(body,fixed,v,prime)
            expected,en=literal(v,fixed,constants,prime,5,True,'structural',norm)
            assert actual==expected
            for name,value in en.items():
                assert an[name]==value,(prime,rep,name)
                comparison_count+=1
    body['exact_degree']=body['degree_upper_bound']
    body['exact_degree_formula']='113856*t+27064, t=610895'
    body['degree_certification']='SUN_B4_VERIFICATION.json: exact leading coefficients at three primes'
    (ROOT/'generated/sun_b4.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
    old_degree=126496*5**31+27064
    report={'status':'PASS','unknowns':10,'operations':body['operation_counts'],
        'total_operations':sum(body['operation_counts'].values()),
        'exact_degree':body['exact_degree'],'old_degree':old_degree,
        'degree_reduction_factor_approx':old_degree/body['exact_degree'],
        'coefficient_reconstruction':coefficient_report,'fixed_constants':fixed_report,
        'B4_four_multisets':len(seen),'direct_B4_collision_check':True,
        'norm_identity':norm_report,'degree_certificates':degrees,
        'literal_modular_assignments':120,'named_value_comparisons':comparison_count,
        'scope':'Exact finite checks and bounded regression tests; imported Lucas and compiler theorems remain external. Universal equivalence is proved in SUN_B4_PROOF.tex.'}
    (ROOT/'SUN_B4_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return report

if __name__=='__main__':run()
