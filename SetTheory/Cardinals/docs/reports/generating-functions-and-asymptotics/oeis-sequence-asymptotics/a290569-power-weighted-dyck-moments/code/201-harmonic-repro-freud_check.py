#!/usr/bin/env python3
"""Finite Freud-comparison checks for pure-power weighted Dyck moments.

Exact mode uses only the Python standard library. Optional mpmath diagnostics
are not interval certificates, convergence proofs, or effective error bounds.
All source/output paths are package-relative and no network access is used.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from math import factorial
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
INTEGER_POWERS = (1, 2, 3, 4, 6)
NUMERICAL_POWERS = ('0.25', '0.5', '1', '1.5', '2', '3', '4', '6')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def write_json(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2, allow_nan=False)+'\n', encoding='utf-8')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def gamma_moments(p, degree):
    """E X^j for density exp(-|x|^(2/p))/(p Gamma(p/2)), integer p.

    Odd moments vanish. Even moments are the exact rising product
    Gamma(p*n+p/2)/Gamma(p/2); no floating-point Gamma evaluation occurs.
    """
    require(type(p) is int and p >= 1, 'Exact Gamma parameter must be a positive integer')
    out = []
    for j in range(degree+1):
        value = F(1)
        if j % 2:
            value = F(0)
        else:
            for k in range(p*(j//2)):
                value *= F(p, 2)+k
        out.append(value)
    return out


def ldl_norms(moments, degree):
    """Monic squared norms from rational LDL^T of the Hankel Gram matrix."""
    lower = [[F(0)]*(degree+1) for _ in range(degree+1)]
    norms = []
    for j in range(degree+1):
        diagonal = moments[2*j]-sum(lower[j][k]**2*norms[k] for k in range(j))
        require(diagonal > 0, f'Nonpositive Hankel pivot at degree {j}')
        norms.append(diagonal)
        lower[j][j] = F(1)
        for i in range(j+1, degree+1):
            lower[i][j] = (moments[i+j]-sum(lower[i][k]*lower[j][k]*norms[k]
                                           for k in range(j)))/diagonal
    return norms


def stieltjes_fraction(coefficients):
    """Formal nested S-fraction, independent of the walk implementation."""
    N = len(coefficients)
    child = [F(1)]+[F(0)]*N
    for weight in reversed(coefficients):
        parent = [F(1)]+[F(0)]*N
        for n in range(1, N+1):
            parent[n] = weight*sum(parent[k]*child[n-1-k] for k in range(n))
        child = parent
    return child


def integer_walk(p, N):
    """Exact time/height propagation of weights h^p for integer p."""
    weights = [0]+[h**p for h in range(1, N+1)]
    row = [1]+[0]*N
    values = [1]
    for step in range(1, 2*N+1):
        new = [0]*(N+1)
        for h in range(step % 2, min(step, 2*N-step, N)+1, 2):
            new[h] = (row[h-1] if h else 0)
            if h < N:
                new[h] += weights[h+1]*row[h+1]
        row = new
        if step % 2 == 0:
            values.append(row[0])
    return values


def constant_algebra():
    """Exact affine-in-p exponent vectors for bases 2, pi, p, I_p, Gamma(p/2).

    Each pair [a,b] denotes exponent a+b*p. Gamma duplication is a stated
    analytic identity, not proved by this finite exponent bookkeeping.
    """
    bases = ['2', 'pi', 'p', 'I_p', 'Gamma(p/2)']
    def vec(*pairs):
        return tuple(tuple(map(F, pair)) for pair in pairs)
    def add(a, b):
        return tuple(tuple(x+y for x, y in zip(v, w)) for v, w in zip(a, b))
    def scale(a, k):
        return tuple(tuple(k*x for x in v) for v in a)
    zero = (0, 0)
    A = vec(zero, zero, (0, F(1,2)), (0, F(1,2)), zero)
    H0 = add(vec(zero, zero, (1,0), zero, (1,0)), scale(A, -1))
    P = add(vec((0,F(-1,2)), (1,F(-1,2)), zero, zero, zero), scale(H0, -1))
    Cnu = vec((F(1,2),F(-1,2)), (F(1,2),F(-1,2)), (F(-1,2),F(1,2)), zero, (-1,0))
    amplitude = add(Cnu, scale(P, -1))
    expected_amplitude = vec((F(1,2),0), (F(-1,2),0), (F(1,2),0), (0,F(-1,2)), zero)
    require(amplitude == expected_amplitude, 'Exact C_nu/P amplitude simplification')
    exponential = add(vec((2,0), zero, (0,1), zero, zero), scale(A, -2))
    expected_exponential = vec((2,0), zero, zero, (0,-1), zero)
    require(exponential == expected_exponential, 'Exact 4*p^p/A^2 exponential simplification')
    product_correction = (F(-1,12), F(2,12)-F(1,12))
    require(product_correction == (F(-1,12), F(1,12)), 'Exact norm minus factorial correction')
    recurrence = []
    for k in range(2, 6):
        # [x^k] ((1/x-1/2)*(-log(1-x))-1) = 1/(k+1)-1/(2k).
        direct = F(1,k+1)-F(1,2*k)-F(1,6)
        expected = F(k-1,2*k*(k+1))-F(1,6)
        require(direct == expected, f'Exact smooth recurrence coefficient k={k}')
        recurrence.append({'inverse_height_power':k, 'constant':str(F(1,12)), 'coefficient_of_p':str(direct)})
    def serial(v):
        return {name:[str(x) for x in pair] for name,pair in zip(bases,v)}
    return {'checks':7, 'exponent_pair_convention':'[a,b] means a+b*p',
            'C_nu_over_P':serial(amplitude), 'd_p':serial(exponential),
            'product_log_1_over_N_coefficient':['-1/12','1/12'],
            'smooth_log_recurrence_coefficients':recurrence,
            'scope':'Exact algebra conditional on the stated Gamma, norm, and Stirling formulas; not a proof of the published Freud theorem or its remainder.'}


def exact_suite(N, degree):
    counts = {'gamma_moment_s_fraction':0, 'norm_telescoping':0,
              'normalized_norm_telescoping':0, 'gaussian_recurrence':0,
              'scaled_norms':0, 'scaled_moments':0, 'pure_classical_coefficients':0,
              'pure_walk_s_fraction':0, 'inclusive_crossings':0, 'positive_hankel_pivots':0}
    gamma_rows = []
    for p in range(1, 7):
        moments = gamma_moments(p, 2*degree)
        norms = ldl_norms(moments, degree)
        counts['positive_hankel_pivots'] += degree+1
        require(norms[0] == 1, 'Probability normalization q0=1')
        weights = [norms[h]/norms[h-1] for h in range(1, degree+1)]
        series = stieltjes_fraction(weights)
        product = F(1)
        normalized_product = F(1)
        for n in range(degree+1):
            require(series[n] == moments[2*n], f'Gamma moment / S-fraction p={p}, n={n}')
            counts['gamma_moment_s_fraction'] += 1
            if n:
                product *= weights[n-1]
                normalized_product *= weights[n-1]/n**p
                require(product == norms[n], f'Norm telescope p={p}, n={n}')
                counts['norm_telescoping'] += 1
                require(normalized_product == norms[n]/factorial(n)**p,
                        f'Normalized norm telescope p={p}, n={n}')
                counts['normalized_norm_telescoping'] += 1
                if p == 1:
                    require(weights[n-1] == F(n,2), f'Gaussian comparison recurrence n={n}')
                    counts['gaussian_recurrence'] += 1
        gamma_rows.append({'p':p, 'degree':degree, 'even_moments':[str(moments[2*n]) for n in range(degree+1)],
                           'monic_norms':[str(x) for x in norms], 'recurrence_weights':[str(x) for x in weights]})
        if p in (1,3,6):
            d = min(degree,8)
            for s in (F(4,9),F(9,4)):
                scaled = [moments[j]*s**(j//2) if j%2 == 0 else F(0) for j in range(2*d+1)]
                scaled_norms = ldl_norms(scaled,d)
                counts['positive_hankel_pivots'] += d+1
                scaled_series = stieltjes_fraction([scaled_norms[h]/scaled_norms[h-1] for h in range(1,d+1)])
                for h in range(d+1):
                    require(scaled_norms[h] == s**h*norms[h], f'Scaled monic norm p={p}, h={h}, scale={s}')
                    counts['scaled_norms'] += 1
                    require(scaled_series[h] == scaled[2*h], f'Scaled Gamma moment p={p}, n={h}, scale={s}')
                    counts['scaled_moments'] += 1
    pure = {p:integer_walk(p,N) for p in INTEGER_POWERS}
    secant = [F(1)]
    for n in range(1,degree+1):
        secant.append(-sum(F((-1)**k,factorial(2*k))*secant[n-k] for k in range(1,n+1)))
    for p in INTEGER_POWERS:
        formal = stieltjes_fraction([F(h**p) for h in range(1,degree+1)])
        for n in range(degree+1):
            require(formal[n] == pure[p][n], f'Pure exact walk/S-fraction p={p}, n={n}')
            counts['pure_walk_s_fraction'] += 1
            if p in (1,2):
                expected = F(factorial(2*n),2**n*factorial(n)) if p==1 else secant[n]*factorial(2*n)
                require(formal[n] == expected, f'Pure Gaussian/secant coefficient p={p}, n={n}')
                counts['pure_classical_coefficients'] += 1
    crossings=[]
    for p,seq in pure.items():
        for n in (16,32,64,128):
            if n+1 > N:
                continue
            for kind,Y in [('equal',seq[n]),('above',seq[n]+1),('midpoint',(seq[n]+seq[n+1])//2)]:
                crossing = next(k for k,value in enumerate(seq) if value>=Y)
                require(seq[crossing]>=Y and all(value<Y for value in seq[:crossing]),
                        f'Inclusive threshold p={p}, n={n}, type={kind}')
                counts['inclusive_crossings'] += 1
                crossings.append({'p':p,'base_index':n,'threshold_type':kind,'threshold_integer':str(Y),
                                  'exact_first_inclusive_crossing':crossing})
    algebra=constant_algebra()
    counts['constant_algebra']=algebra['checks']
    result={'status':'PASS','scope':'Finite exact integer/rational checks. They do not prove an asymptotic limit, rate, effective onset, or the cited Freud theorem.',
            'max_n':N,'norm_degree':degree,'arithmetic':'Python integers and fractions.Fraction',
            'check_counts':counts,'total_check_instances':sum(counts.values()),
            'gamma_probability_convention':'Unscaled density exp(-|x|^(2/p))/(p Gamma(p/2)); even moment Gamma(p*n+p/2)/Gamma(p/2). The article\'s scaled comparison adds (4/A^2)^n to these unscaled moments.',
            'gamma_norm_records':gamma_rows,'constant_algebra':algebra,
            'pure_integer_moment_generation':{'powers':list(INTEGER_POWERS),'max_n':N,'array_sha256':{
                str(p):sha256(json.dumps([str(x) for x in values],separators=(',',':')).encode('ascii')).hexdigest() for p,values in pure.items()}},
            'exact_inclusive_thresholds':crossings}
    return result,pure


def numerical_constants(mp,p):
    I=mp.beta(1/p,mp.mpf('0.5'))/p
    A=(p*I)**(p/2)
    H0=p*mp.gamma(p/2)/A
    P=mp.pi/(H0*(2*mp.pi)**(p/2))
    Cnu=(2*mp.pi)**((1-p)/2)*p**((p-1)/2)/mp.gamma(p/2)
    c=mp.sqrt(2*p/mp.pi)*I**(-p/2)
    d=4/I**p
    return I,A,H0,P,Cnu,c,d


def two_step_moments(mp,p,N):
    """Numerical two-step UU/UD/DU/DD walk, divided at time 2n by (n!)^p."""
    weights=[mp.mpf(0)]+[mp.power(h,p) for h in range(1,2*N+3)]
    row=[mp.mpf(1)]
    values=[mp.mpf(1)]
    for n in range(1,N+1):
        new=[mp.mpf(0)]*(n+1)
        scale=mp.power(n,p)
        for k,value in enumerate(row):
            h=2*k
            new[k+1]+=value/scale
            new[k]+=value*(weights[h+1]+weights[h])/scale
            if k:
                new[k-1]+=value*weights[h]*weights[h-1]/scale
        row=new
        values.append(row[0])
    return values


def numerical_suite(N,degree,exact,pure,dps):
    try:
        import mpmath as mp
    except ImportError as exc:
        raise RuntimeError('--diagnostics requires mpmath; exact mode does not') from exc
    mp.mp.dps=dps
    def fmt(x): return mp.nstr(x,30)
    def rational(s):
        value=F(s)
        return mp.mpf(value.numerator)/value.denominator
    samples=[n for n in (16,32,64,128,256,512) if n<=N]
    constants=[]; ratios=[]; gamma_limits=[]; norm_limits=[]; numerical_consistency=[]
    for ps in NUMERICAL_POWERS:
        p=mp.mpf(ps)
        I,A,H0,P,Cnu,c,d=numerical_constants(mp,p)
        errors=[abs(Cnu/P/c-1),abs((4*p**p/A**2)/d-1),
                abs((2*p*mp.gamma(2/p)/mp.gamma(1/p)**2)**p/d-1)]
        require(max(errors)<mp.power(10,-dps+8),f'Numerical constant normalization p={ps}')
        constants.append({'p':ps,'I_p':fmt(I),'A':fmt(A),'H0':fmt(H0),'P':fmt(P),
                          'c_p':fmt(c),'d_p':fmt(d),'max_relative_identity_error':fmt(max(errors))})
        normalized=two_step_moments(mp,p,N)
        for n in samples:
            log_ratio=mp.log(normalized[n])-mp.log(c)-n*mp.log(d)+mp.log(n)/2
            ratio=mp.exp(log_ratio)
            ratios.append({'p':ps,'n':n,'actual_over_leading':fmt(ratio),
                           'log_ratio_times_log_n_squared':fmt(log_ratio*mp.log(n)**2),
                           'relative_error_times_log_n_squared':fmt((ratio-1)*mp.log(n)**2)})
            if p==int(p) and int(p) in pure:
                reference=mp.mpf(pure[int(p)][n])/mp.factorial(n)**int(p)
                error=abs(normalized[n]/reference-1)
                require(error<mp.power(10,-dps+8),f'Numerical two-step / exact integer walk p={ps}, n={n}')
                numerical_consistency.append({'p':ps,'n':n,'relative_error':fmt(error)})
        n=1000
        log_gamma_ratio=n*mp.log(4/A**2)+mp.loggamma(p*n+p/2)-mp.loggamma(p/2) \
                        -mp.log(Cnu)-n*mp.log(d)-p*mp.loggamma(n+1)+mp.log(n)/2
        gamma_limits.append({'p':ps,'n':n,'explicit_gamma_moment_over_its_leading':fmt(mp.exp(log_gamma_ratio))})
    for row in exact['gamma_norm_records']:
        p=mp.mpf(row['p'])
        I,A,H0,P,Cnu,c,d=numerical_constants(mp,p)
        for n in (4,8,16,24):
            if n>degree: continue
            q=rational(row['monic_norms'][n])*(4/A**2)**n
            log_product=mp.log(q)-p*mp.loggamma(n+1)
            residual=log_product-mp.log(P)-(p-1)/(12*n)
            norm_limits.append({'p':row['p'],'degree':n,'normalized_norm_product_over_P':fmt(mp.exp(log_product)/P),
                                'corrected_log_product_residual':fmt(residual),
                                'n_log_n_squared_times_residual':fmt(n*mp.log(n)**2*residual)})
    inverse=[]
    for row in exact['exact_inclusive_thresholds']:
        p=mp.mpf(row['p']); seq=pure[row['p']]; Y=int(row['threshold_integer']); crossing=row['exact_first_inclusive_crossing']
        I,A,H0,P,Cnu,c,d=numerical_constants(mp,p)
        R=d**(1/p); b=(p-1)/2; Clog=mp.log(c*(2*mp.pi)**(p/2)); L=mp.log(Y)
        t=L/(p*mp.lambertw(R*L/(p*mp.e)))
        xi=t-(b*mp.log(t)+Clog)/(p*mp.log(R*t))
        if Y==seq[crossing]:
            xY=mp.mpf(crossing)
        else:
            k=crossing-1
            xY=k+(L-mp.log(seq[k]))/(mp.log(seq[k+1])-mp.log(seq[k]))
        inverse.append({**row,'xi':fmt(xi),'ceil_xi':int(mp.ceil(xi)),'xY_minus_xi':fmt(xY-xi),
                        'log_t_cubed_times_interpolation_error':fmt(mp.log(t)**3*(xY-xi)),
                        'note':'Crossing is checked with exact integers. Interpolated logs may round at adjacent-integer thresholds; the displayed center is not a rounding certificate.'})
    return {'status':'DIAGNOSTICS_ONLY','precision_decimal_digits':dps,'displayed_significant_digits':30,
            'scope':'Finite high-precision values, not interval certificates or proofs. The pure-power O_p(log(n)^-2) relative remainder and O_p(log(t)^-3) inverse radius have unspecified p-dependent constants and onsets. No finite radius is claimed here.',
            'attribution':'General-p absolute formula posted by Vaclav Kotesovec in OEIS A216966 on September 24, 2020. The article derives it via the published Freud leading-coefficient theorem and endpoint occupation; no novelty claim.',
            'constant_normalizations':constants,'pure_power_ratios':ratios,
            'numerical_two_step_vs_exact_integer_walk':numerical_consistency,
            'explicit_gamma_moment_diagnostics':gamma_limits,'freud_norm_product_diagnostics':norm_limits,
            'pure_integer_power_inverse_diagnostics':inverse}


def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=256,help='Pure moment depth, 48..512')
    parser.add_argument('--norm-degree',type=int,default=16,help='Exact Freud norm degree, 8..24')
    parser.add_argument('--diagnostics',action='store_true',help='Add optional mpmath diagnostics')
    parser.add_argument('--dps',type=int,default=65,help='Numerical precision, at least 45')
    parser.add_argument('--out',type=Path,default=HERE/'freud_generated',help='Output directory')
    args=parser.parse_args()
    require(48<=args.max_n<=512,'--max-n must be in 48..512')
    require(8<=args.norm_degree<=24,'--norm-degree must be in 8..24')
    require(args.dps>=45,'--dps must be at least 45')
    exact,pure=exact_suite(args.max_n,args.norm_degree)
    args.out.mkdir(parents=True,exist_ok=True)
    write_json(args.out/'exact_checks.json',exact)
    names=['exact_checks.json']
    if args.diagnostics:
        write_json(args.out/'numerical_diagnostics.json',numerical_suite(args.max_n,args.norm_degree,exact,pure,args.dps))
        names.append('numerical_diagnostics.json')
    manifest={'format':'report201-freud-v1','max_n':args.max_n,'norm_degree':args.norm_degree,
              'files':{name:digest(args.out/name) for name in names}}
    write_json(args.out/'manifest.json',manifest)
    print(json.dumps({'status':'PASS','exact_check_instances':exact['total_check_instances'],
                      'max_n':args.max_n,'norm_degree':args.norm_degree,'files':manifest['files']},sort_keys=True))


if __name__=='__main__':
    main()
