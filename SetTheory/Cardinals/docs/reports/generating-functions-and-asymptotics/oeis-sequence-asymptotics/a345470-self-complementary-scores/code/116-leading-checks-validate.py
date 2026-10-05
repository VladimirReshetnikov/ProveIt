#!/usr/bin/env python3
"""Exact finite arithmetic for report116; Python >=3.10, standard library only.
Limits in the article are proved analytically, not inferred from these tests.
All guards use explicit exceptions and remain active with python -O.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from math import comb, gcd, isqrt
from pathlib import Path
import sys

class ValidationError(Exception):
    pass

def require(condition, code, detail=''):
    if not condition:
        raise ValidationError(code + (': ' + detail if detail else ''))

def unique_object(pairs):
    out = {}
    for k, v in pairs:
        require(k not in out, 'SCHEMA_DUPLICATE_KEY', k)
        out[k] = v
    return out

def exact_keys(value, keys, code):
    require(type(value) is dict and set(value) == set(keys), code)

RANGES = {'self_max_n': 38, 'ordinary_max_n': 19, 'egz_max_n': 8,
          'lambda_cutoff': 1669, 'split_max_length': 1000,
          'atan_terms': 40, 'exp_terms': 60, 'log_terms': 60,
          'decimal_places': 30, 'sqrt_places': 40}
RATIONAL_KEYS = ['variance', 'span', 'gaussian_square_coefficient',
    'gaussian_residual_coefficient', 'gaussian_marginal_prefactor_square',
    'density_ratio_xw', 'density_ratio_yw', 'outer_s_power',
    'smoothing_alpha_power', 'bad_epsilon_power', 'bad_delta_power',
    'bad_n_power', 'survival_power', 'endpoint_power', 'half_length_power',
    'amplitude_power_after_sigma', 'convolution_far_power', 'inverse_loglog_power',
    'published_lambda_lower', 'published_lambda_upper', 'published_ratio_lower',
    'published_ratio_upper']
LIMITATIONS = [
 'The analytic survival theorem, conditional weak limit, local central limit theorem, smoothing limits, convolution asymptotics, and inverse asymptotics are not certified by finite tests.',
 'The lambda and exp(-lambda) intervals are rigorous rational enclosures conditional on the explicitly cited Kolesnik tail inequality; that imported theorem is not reproved by code.',
 'The amplitude A is characterized in the article and is not numerically evaluated, because its discrete harmonic value is not evaluated.',
 'No quantitative convergence rate or higher-order asymptotic correction is established.'
]

def read_fixtures(path):
    try:
        f = json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique_object)
    except (OSError, UnicodeError, json.JSONDecodeError) as e:
        raise ValidationError('SCHEMA_PARSE: ' + str(e)) from e
    exact_keys(f, ['schema_version', 'provenance', 'ranges', 'sequences', 'constants', 'limitations'], 'SCHEMA_ROOT_KEYS')
    require(type(f['schema_version']) is int and f['schema_version'] == 1, 'SCHEMA_VERSION')
    exact_keys(f['provenance'], ['prior_report', 'prior_results_sha256', 'sources'], 'SCHEMA_PROVENANCE_KEYS')
    require(f['provenance']['prior_report'] == 'report114 exact enumeration results', 'SCHEMA_PRIOR_REPORT')
    h = f['provenance']['prior_results_sha256']
    require(type(h) is str and h == '0fe74f29cd4ea09a022f7f5d71e33fef8684fffc8bdd567eaf0a3fb64180d0e6', 'SCHEMA_PRIOR_HASH')
    require(f['provenance']['sources'] == [
        'https://oeis.org/A345470', 'https://oeis.org/A351869',
        'https://cs.uwaterloo.ca/journals/JIS/VOL26/Stockmeyer/stock14.pdf',
        'https://link.springer.com/article/10.1007/s00493-023-00037-4',
        'https://www.numdam.org/articles/10.1214/13-AIHP577/'], 'SCHEMA_SOURCE_URLS')
    exact_keys(f['ranges'], RANGES, 'SCHEMA_RANGE_KEYS')
    require(all(type(f['ranges'][k]) is int and f['ranges'][k] == v for k, v in RANGES.items()), 'SCHEMA_RANGE_VALUE')
    exact_keys(f['sequences'], ['C', 'D', 'S', 'T', 'N'], 'SCHEMA_SEQUENCE_KEYS')
    for key in ['C', 'D', 'S', 'T', 'N']:
        seq = f['sequences'][key]
        require(type(seq) is list and len(seq) == (39 if key in ['C', 'D'] else 20), 'SCHEMA_SEQUENCE_LENGTH', key)
        require(all(type(v) is int and v >= 0 for v in seq), 'SCHEMA_INTEGER_TERM', key)
    exact_keys(f['constants'], RATIONAL_KEYS, 'SCHEMA_CONSTANT_KEYS')
    for key in RATIONAL_KEYS:
        pair = f['constants'][key]
        require(type(pair) is list and len(pair) == 2 and all(type(v) is int for v in pair) and pair[1] > 0, 'SCHEMA_RATIONAL_TYPE', key)
        require(gcd(pair[0], pair[1]) == 1, 'SCHEMA_RATIONAL_REDUCED', key)
    require(f['limitations'] == LIMITATIONS, 'SCHEMA_LIMITATIONS')
    return f

def constant(f, name):
    return F(*f['constants'][name])

def half_score_dp(n, strict):
    if n <= 1:
        return 1
    m, cap = n // 2, (n - 1) // 2
    states = {(0, 0): 1}
    for r in range(1, m + 1):
        new = defaultdict(int)
        for (last, total), count in states.items():
            for score in range(last, cap + 1):
                value = total + score
                if value >= r * (r - 1) // 2 + int(strict):
                    new[(score, value)] += count
        states = new
    return sum(states.values())

def walk_dp(n, strict):
    if n <= 1:
        return 1
    m = n // 2
    endpoint = -1 if n % 2 == 0 else 0
    states = {(1, 0): 1}
    for r in range(1, m + 2):
        remaining = m + 1 - r
        new = defaultdict(int)
        for (v, a), count in states.items():
            for velocity in range(v - 1, endpoint + remaining + 1):
                area = a + velocity
                if r <= m and area < int(strict):
                    continue
                new[(velocity, area)] += count
        states = new
    return sum(count for (v, a), count in states.items() if v == endpoint)

def ordinary_score_dp(n, strict):
    if n == 0:
        return 0 if strict else 1
    target = n * (n - 1) // 2
    states = {(0, 0): 1}
    for r in range(1, n + 1):
        new = defaultdict(int)
        for (last, total), count in states.items():
            for score in range(last, n):
                value = total + score
                if value > target:
                    break
                if value < r * (r - 1) // 2 + (int(strict) if r < n else 0):
                    continue
                if value + (n - r) * (n - 1) < target:
                    continue
                new[(score, value)] += count
        states = new
    return sum(count for (last, total), count in states.items() if total == target)

def egzs(cutoff):
    phi = list(range(cutoff + 1))
    for p in range(2, cutoff + 1):
        if phi[p] == p:
            for j in range(p, cutoff + 1, p):
                phi[j] -= phi[j] // p
    numerators = [0] * (cutoff + 1)
    for d in range(1, cutoff + 1):
        central = comb(2 * d, d)
        for k in range(d, cutoff + 1, d):
            numerators[k] += (-1) ** (k + d) * phi[k // d] * central
    out = [0]
    for k in range(1, cutoff + 1):
        require(numerators[k] % (2 * k) == 0 and numerators[k] > 0, 'EGZ_INTEGRAL_POSITIVE', str(k))
        out.append(numerators[k] // (2 * k))
    return out

def check_counts(f, result):
    C, D = [], []
    for strict, target in [(False, C), (True, D)]:
        for n in range(RANGES['self_max_n'] + 1):
            value = half_score_dp(n, strict)
            require(walk_dp(n, strict) == value, 'WALK_COUNT', f'n={n}, strict={strict}')
            target.append(value)
    require(C == f['sequences']['C'], 'C_FIXTURE_COUNT')
    require(D == f['sequences']['D'], 'D_FIXTURE_COUNT')
    S = [ordinary_score_dp(n, False) for n in range(RANGES['ordinary_max_n'] + 1)]
    T = [ordinary_score_dp(n, True) for n in range(RANGES['ordinary_max_n'] + 1)]
    N = egzs(RANGES['ordinary_max_n'])
    for key, seq in [('S', S), ('T', T), ('N', N)]:
        require(seq == f['sequences'][key], key + '_FIXTURE_COUNT')
    for n in range(1, len(S)):
        require(S[n] == sum(T[k] * S[n-k] for k in range(1, n+1)), 'S_STRONG_COMPONENT_RECURRENCE', str(n))
        require(n * S[n] == sum(N[k] * S[n-k] for k in range(1, n+1)), 'N_LOG_DERIVATIVE_RECURRENCE', str(n))
    for n in range(len(C)):
        require(C[n] == sum(D[n-2*k] * S[k] for k in range(n//2+1)), 'C_DS_CONVOLUTION', str(n))
        require(D[n] == C[n] - sum(T[k] * C[n-2*k] for k in range(1, n//2+1)), 'D_C_ONE_MINUS_T', str(n))
    for n in range(1, RANGES['egz_max_n'] + 1):
        direct = sum(sum(a) % n == 0 for a in combinations(range(1, 2*n), n))
        require(direct == N[n], 'EGZ_SUBSET_ENUMERATION', str(n))
    threshold_cases = gap_cases = 0
    for seq in [C, D]:
        targets = {x for v in seq[1:] for x in [v-1, v, v+1] if 1 <= x <= seq[-1]}
        for x in sorted(targets):
            n = next(i for i in range(1, len(seq)) if seq[i] >= x)
            require(seq[n] >= x and all(v < x for v in seq[1:n]), 'FINITE_INVERSE_MINIMUM')
            threshold_cases += 1
    # Only check the finite gaps actually in range; eventuality is an analytic result.
    for x in sorted({x for seq in [C, D] for v in seq[1:] for x in [v-1, v, v+1] if 1 <= x <= D[-1]}):
        nc = next(i for i in range(1, len(C)) if C[i] >= x)
        nd = next(i for i in range(1, len(D)) if D[i] >= x)
        require(nd >= nc, 'FINITE_STRONG_INVERSE_ORDER')
        gap_cases += 1
    result['exact_sequences'] = {'C': C, 'D': D, 'S': S, 'T': T, 'N': N,
        'self_range': [0, 38], 'ordinary_range': [0, 19], 'direct_egz_range': [1, 8],
        'finite_inverse_cases': threshold_cases, 'finite_inverse_order_cases': gap_cases,
        'formal_series_checked': ['C=D*S(z^2)', 'D=C*(1-T(z^2))', 'S=1/(1-T)', 'z*S_prime=S*sum(N_k*z^k)']}

# Laurent polynomials with exact rational coefficients; variables (x,y,t,w).
def add(*polys):
    out = defaultdict(F)
    for p in polys:
        for key, value in p.items():
            out[key] += value
    return {k: v for k, v in out.items() if v}

def scale(p, value):
    return {k: value * v for k, v in p.items() if value * v}

def mul(p, q):
    out = defaultdict(F)
    for kp, vp in p.items():
        for kq, vq in q.items():
            out[tuple(a+b for a,b in zip(kp,kq))] += vp*vq
    return {k: v for k, v in out.items() if v}

def mono(value, powers):
    return {tuple(powers): F(value)} if value else {}

def gaussian_exponent(x, y, v):
    delta = add(scale(x, -1), scale(mul(mono(1, (0,0,1,0)), y), -1))
    speed = add(v, scale(y, -1))
    return add(mul(mono(-6, (0,0,-3,0)), mul(delta,delta)),
               mul(mono(6, (0,0,-2,0)), mul(delta,speed)),
               mul(mono(-2, (0,0,-1,0)), mul(speed,speed)))

def check_algebra(f, result):
    c = lambda name: constant(f, name)
    x,y,t,w = [mono(1, powers) for powers in [(1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1)]]
    for sign in [-1,1]:
        v = scale(w, sign)
        original = gaussian_exponent(x, scale(y,-1), v)
        centered = add(x, scale(mul(t, add(y,scale(v,-1))), F(-1,2)))
        completed = add(mul(mono(c('gaussian_square_coefficient'), (0,0,-3,0)), mul(centered,centered)),
                        mul(mono(c('gaussian_residual_coefficient'), (0,0,-1,0)), mul(add(y,v),add(y,v))))
        require(original == completed, 'GAUSSIAN_COMPLETION')
    require(F(3,6) == c('gaussian_marginal_prefactor_square') == F(1,2), 'GAUSSIAN_MARGINAL_FACTOR')
    # Squared prefactor is (3/pi^2 t^4)*(pi*t^3/6)=1/(2*pi*t).
    require(F(-2)*2 + 3 == -1, 'GAUSSIAN_MARGINAL_TIME_POWER')
    ratio = add(gaussian_exponent(x,scale(y,-1),scale(w,-1)), scale(gaussian_exponent(x,scale(y,-1),w),-1))
    require(ratio == {(1,0,-2,1): c('density_ratio_xw'), (0,1,-1,1): c('density_ratio_yw')}, 'GAUSSIAN_DENSITY_RATIO')
    require(c('density_ratio_xw') == 12 and c('density_ratio_yw') == -4, 'GAUSSIAN_RATIO_VALUES')
    require(F(3,4)+F(1,2)-F(1,2) == c('outer_s_power') == F(3,4), 'OUTER_INTEGRABLE_POWER')
    require(c('outer_s_power') > -1 and F(-1,2) > -1, 'DOMINATION_ENDPOINT_INTEGRABILITY')
    q = F(1,2)
    S0,S1,S2 = 1/(1-q), q/(1-q)**2, q*(1+q)/(1-q)**3
    require((S1-S0)/2 == 0, 'INCREMENT_MEAN')
    require((S2-2*S1+S0)/2 == c('variance') == 2, 'INCREMENT_VARIANCE')
    require(gcd(0-(-1),1) == c('span') == 1, 'SPAN_ONE')
    require(F(-1,4)-F(1,2) == c('smoothing_alpha_power') == F(-3,4), 'SMOOTHING_ALPHA_POWER')
    require(F(1,2)+2 == c('bad_epsilon_power') == F(5,2), 'BAD_EVENT_EPSILON_POWER')
    require(-2 == c('bad_delta_power'), 'BAD_EVENT_DELTA_POWER')
    require(F(1,2)-1 == c('bad_n_power') == F(-1,2), 'BAD_EVENT_N_POWER')
    require(c('survival_power') == F(-1,4) and c('endpoint_power') == F(-3,4), 'SURVIVAL_ENDPOINT_POWERS')
    require(c('bad_n_power')+c('survival_power')-c('endpoint_power') == 0, 'SCALED_ERROR_N_CANCELLATION')
    require(c('half_length_power') == -c('endpoint_power') == F(3,4), 'HALF_LENGTH_FACTOR')
    require(c('half_length_power')-F(1,2) == c('amplitude_power_after_sigma') == F(1,4), 'AMPLITUDE_VARIANCE_FACTOR')
    require(F(3,4)-F(5,2)+F(1,4) == c('convolution_far_power') == F(-3,2), 'CONVOLUTION_FAR_POWER')
    require(c('inverse_loglog_power') == -c('endpoint_power') == F(3,4), 'INVERSE_LOGLOG_POWER')
    for cutoff in range(65):
        require(sum((F(1,2**(h+1)) for h in range(cutoff)),F()) + F(1,2**cutoff) == 1, 'SLACK_TOTAL_MASS')
    for ell in range(3, RANGES['split_max_length']+1):
        a,b=ell//2,ell-ell//2
        require(a+b == ell and a>0 and b>0 and 3*a>=ell and 2*b>=ell, 'BRIDGE_SPLIT_BOUNDS')
        require(a*a <= 2*ell*b and b*b <= 3*ell*a, 'BRIDGE_SQRT_BOUNDS')
    # For epsilon <= delta/[8(K+1)], the chosen H protects both area and endpoint.
    guards=0
    for delta in [F(1,7),F(1,2),F(1),F(3)]:
        for K in [F(1,9),F(1),F(4)]:
            eps=delta/(8*(K+1))
            H=delta/(4*eps)  # coefficient of sqrt(n)
            require(2*eps*(K+H) < delta, 'BAD_EVENT_AREA_PROTECTION')
            require(H >= 2*(K+1), 'BAD_EVENT_ENDPOINT_GUARD')
            guards+=1
    # Formal cancellation in log_2(a*2^h*h^-beta / x), h=L+beta*log_2(L)-log_2(a).
    beta=c('inverse_loglog_power')
    lhs={'log_a':F(1),'L':F(-1),'log_h':-beta}
    h={'L':F(1),'log_L':beta,'log_a':F(-1)}
    for key,value in h.items():lhs[key]=lhs.get(key,F())+value
    lhs={k:v for k,v in lhs.items() if v}
    require(lhs == {'log_h':-beta,'log_L':beta}, 'REFINED_INVERSE_CANCELLATION')
    # A noninteger displacement in (0,1) gives adjacent integer thresholds.
    staircase_cases=0
    for L in range(-4,5):
        for a in [F(1,8),F(1,3),F(7,8)]:
            for shift in [F(1,9),F(1,2),F(8,9)]:
                ceil=lambda x:-((-x.numerator)//x.denominator)
                require(ceil(L+a+shift)-ceil(L+a) in [0,1], 'STABLE_STAIRCASE_GAP')
                staircase_cases+=1
    # Natural-log form of the same inverse expansion, checked as a formal linear identity.
    inverse_natural={'log_A':F(1),'log_X':F(-1),'log_u':-beta}
    gamma_u={'log_X':F(1),'log_log_X':beta,'log_gamma':-beta,'log_A':F(-1)}
    for key,value in gamma_u.items():inverse_natural[key]=inverse_natural.get(key,F())+value
    inverse_natural={k:v for k,v in inverse_natural.items() if v}
    require(inverse_natural == {'log_u':-beta,'log_log_X':beta,'log_gamma':-beta}, 'NATURAL_INVERSE_CANCELLATION')
    # Lambert substitution: w=-(gamma/a)t, so t*exp(-gamma*t/a)=-(a/gamma)*w*exp(w).
    for a0 in [F(3,4),F(1,2),F(2)]:
        for gamma in [F(2,3),F(1),F(7,5)]:
            for w0 in [F(-1),F(-2),F(-7,3)]:
                t0=-a0*w0/gamma
                require(-gamma*t0/a0 == w0 and -a0/gamma*w0 == t0, 'LAMBERT_SUBSTITUTION')
                require(gamma-a0/t0 >= 0, 'LAMBERT_INCREASING_BRANCH')
    # At a threshold, m-1+e_prev<q<=m+e_m implies the two ceiling bounds.
    ceiling_cases=0
    ceil=lambda x:-((-x.numerator)//x.denominator)
    for m in range(2,8):
        for ep in [F(-1,8),F(0),F(1,8)]:
            for em in [F(-1,8),F(0),F(1,8)]:
                eta=max(abs(ep),abs(em))
                low,high=F(m-1)+ep,F(m)+em
                for theta in [F(1,7),F(1,2),F(1)]:
                    q0=low+theta*(high-low)
                    require(ceil(q0-eta)<=m<=ceil(q0+eta), 'INVERSE_CEILING_BRACKETS')
                    ceiling_cases+=1
    result['exact_algebra']={'gaussian_completion_both_signs':True,
        'gaussian_marginal':'(2*pi*t)^(-1/2)*exp(-(y+v)^2/(2*t))',
        'density_log_ratio':'12*x*w/t^2 - 4*y*w/t',
        'outer_s_power':'3/4','smoothing_alpha_power':'-3/4',
        'bad_event_powers':{'epsilon':'5/2','delta':'-2','n':'-1/2'},
        'scaled_error_n_power':'0','sigma_squared':'2','lattice_span':'1',
        'half_length_factor':'2^(3/4)','amplitude_after_sigma':'2^(1/4)',
        'convolution_far_power':'-3/2','bridge_lengths_checked':998,
        'area_endpoint_guard_cases':guards,'slack_partial_sum_and_tail_cases':65,
        'refined_inverse_identity':'log2(a*2^h*h^(-3/4)/x)=(3/4)*log2(L/h)',
        'staircase_cases':staircase_cases,'ceiling_bracket_cases':ceiling_cases,
        'lambert_substitution_cases':27,'natural_log_inverse_algebra':True}

def rising(a, n):
    out=F(1)
    for j in range(n):out*=a+j
    return out

def check_universal_factor(result):
    # Exact coefficient and prefactor algebra only; integral/series transformations
    # and convergence are justified analytically in the article.
    require(F(9,4)-F(1,2)-F(1,2)+F(7,4)-F(7,2) == F(-1,2), 'UNIVERSAL_TWO_POWER')
    require(F(1,2)-F(1,2)-F(1,2) == F(-1,2), 'UNIVERSAL_PI_POWER')
    require(F(-1,2)+F(7,4) == F(5,4), 'UNIVERSAL_S_POWER')
    require(-F(1,2)-F(1,2)+F(7,4) == F(3,4), 'UNIVERSAL_ONE_MINUS_S_POWER')
    require((F(5,4)*F(1,4))/6 == F(5,96), 'UNIVERSAL_GAMMA_PREFACTOR')
    for s in [F(1,9),F(1,3),F(1,2),F(3,4),F(8,9)]:
        P=(4-3*s)/(2*s*(1-s));Q2=3/(2*(1-s));z=-Q2/P
        require(z/(z-1)==3*s/4 and 1-z==4/(4-3*s), 'PFAFF_RATIONAL_ARGUMENT')
    a2=a3=F(1)
    for j in range(65):
        beta_ratio=rising(F(9,4),j)/rising(F(4),j)
        closed=rising(F(1),j)*rising(F(7,4),j)*rising(F(9,4),j)/(
            rising(F(3,2),j)*rising(F(4),j)*rising(F(1),j))*F(3,4)**j
        require(a2*beta_ratio == a3 == closed, 'HYPERGEOMETRIC_COEFFICIENT')
        ratio=F(3,4)*(j+F(7,4))*(j+F(9,4))/((j+F(3,2))*(j+4))
        require(0<ratio<F(3,4), 'HYPERGEOMETRIC_RATIO_BOUND')
        a2*=F(3,4)*(j+F(7,4))/(j+F(3,2))
        a3*=ratio
    # This polynomial identity proves the ratio bound for every nonnegative j.
    # (j+3/2)(j+4)-(j+7/4)(j+9/4)=(3/2)j+33/16 > 0.
    require(F(3,2)+4-F(7,4)-F(9,4) == F(3,2), 'HYPERGEOMETRIC_RATIO_LINEAR')
    require(F(3,2)*4-F(7,4)*F(9,4) == F(33,16), 'HYPERGEOMETRIC_RATIO_CONSTANT')
    result['universal_factor_algebra']={'coefficient_indices':[0,64],
        'positive_series_ratio_bound':'0 < term_(j+1)/term_j < 3/4 for j>=0',
        'gamma_recurrence_factor':'5/96','post_transformation_s_powers':['5/4','3/4'],
        'formula':'f_Y(0)=5*Gamma(7/4)^2/(96*sqrt(2*pi))*3F2(1,7/4,9/4;3/2,4;3/4)',
        'scope':'Exact coefficient and prefactor algebra. No decimal quadrature and no numeric amplitude A.'}

def atan_bounds(q, terms):
    require(q>1 and terms>0, 'ATAN_INPUT')
    partial=sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(terms)),F())
    next_term=F((-1)**terms,(2*terms+1)*q**(2*terms+1))
    return min(partial,partial+next_term),max(partial,partial+next_term)

def outward(value, places, upper=False):
    s=10**places
    n=(value.numerator*s)//value.denominator
    if upper and F(n,s)<value:n+=1
    return F(n,s)

def decimal_exact(value, places):
    scaled=value*10**places
    require(scaled.denominator == 1, 'DECIMAL_EXACT_DENOMINATOR')
    n=scaled.numerator
    require(n>=0, 'DECIMAL_NONNEGATIVE')
    return str(n//10**places)+'.'+str(n%10**places).zfill(places)

def sqrt_bounds(value, places):
    require(value>0, 'SQRT_INPUT')
    s=10**places
    k=isqrt(value.numerator*s*s//value.denominator)
    lo,hi=F(k,s),F(k+1,s)
    require(lo*lo<=value<hi*hi, 'SQRT_ENCLOSURE')
    return lo,hi

def exp_minus_bounds(value, terms):
    require(0<value<1 and terms>=2 and terms%2==0, 'EXP_INPUT')
    # Even partial sum through degree terms is an upper bound; next odd is lower.
    term=F(1);partial=F(1)
    for j in range(1,terms+1):
        term *= -value/j
        partial += term
    lower=partial+term*(-value)/(terms+1)
    require(lower<partial, 'EXP_ALTERNATING_ORDER')
    return lower,partial

def log_two_bounds(terms):
    # log(2)=2*atanh(1/3). Bound all remaining denominators below by 2*terms+1.
    partial=2*sum((F(1,(2*j+1)*3**(2*j+1)) for j in range(terms)),F())
    tail=2*F(1,(2*terms+1)*3**(2*terms+1))/(1-F(1,9))
    return partial,partial+tail

def interval(lo,hi,places=30):
    require(lo<=hi, 'INTERVAL_ORDER')
    return [decimal_exact(outward(lo,places),places),decimal_exact(outward(hi,places,True),places)]

def check_certificates(f,result):
    cutoff=RANGES['lambda_cutoff']
    N=egzs(cutoff)
    require(N[:20] == f['sequences']['N'], 'EGZ_CERTIFICATE_PREFIX')
    partial=sum((F(N[k],k*4**k) for k in range(1,cutoff+1)),F())
    a,b=atan_bounds(5,RANGES['atan_terms'])
    c,d=atan_bounds(239,RANGES['atan_terms'])
    # Machin identity: tan(4 atan(1/5)-atan(1/239))=1, angle in (0,pi/2).
    tan_double=lambda x:2*x/(1-x*x)
    tangent=tan_double(tan_double(F(1,5)))
    require((tangent-F(1,239))/(1+tangent*F(1,239)) == 1, 'MACHIN_TANGENT_IDENTITY')
    require(0 < 4*a-d < 4*b-c < 1, 'MACHIN_ANGLE_RANGE')
    pi_lo,pi_hi=16*a-4*d,16*b-4*c
    require(F(3)<pi_lo<pi_hi<F(22,7), 'MACHIN_PI_ENCLOSURE')
    sqrt_lo=sqrt_bounds(pi_lo*cutoff**3,RANGES['sqrt_places'])[0]
    sqrt_hi=sqrt_bounds(pi_hi*cutoff**3,RANGES['sqrt_places'])[1]
    # Imported theorem: Kolesnik Lemma 11, equation (17), not a finite-test inference.
    tail_lo=(1-F(2,cutoff))/(3*sqrt_hi)
    tail_hi=1/(3*sqrt_lo)
    require(tail_lo*3*sqrt_hi == 1-F(2,cutoff), 'IMPORTED_TAIL_LOWER_FORMULA')
    require(tail_hi*3*sqrt_lo == 1, 'IMPORTED_TAIL_UPPER_FORMULA')
    lambda_lo=outward(partial+tail_lo,RANGES['decimal_places'])
    lambda_hi=outward(partial+tail_hi,RANGES['decimal_places'],True)
    require(F('0.330237542') == constant(f,'published_lambda_lower') <= lambda_lo, 'PUBLISHED_LAMBDA_LOWER')
    require(lambda_hi <= constant(f,'published_lambda_upper') == F('0.330237546'), 'PUBLISHED_LAMBDA_UPPER')
    ratio_lo=exp_minus_bounds(lambda_hi,RANGES['exp_terms'])[0]
    ratio_hi=exp_minus_bounds(lambda_lo,RANGES['exp_terms'])[1]
    require(constant(f,'published_ratio_lower') == F('0.7187529762') < ratio_lo, 'PUBLISHED_RATIO_LOWER')
    require(ratio_hi < constant(f,'published_ratio_upper') == F('0.7187529792'), 'PUBLISHED_RATIO_UPPER')
    log_lo,log_hi=log_two_bounds(RANGES['log_terms'])
    shift_lo,shift_hi=lambda_lo/log_hi,lambda_hi/log_lo
    require(0<shift_lo<=shift_hi<1, 'INVERSE_DISPLACEMENT_BETWEEN_ZERO_ONE')
    require(F(1,2)<ratio_lo<=ratio_hi<1 and 2*ratio_lo>1, 'EVENTUAL_GAP_RATIO_CONDITIONS')
    payload=json.dumps(N,separators=(',',':')).encode()
    result['rational_certificates']={'cutoff':cutoff,'N_vector_sha256':sha256(payload).hexdigest(),
      'N_vector_hash_serialization':'JSON integer list N_0 through N_1669, separators comma and colon, no newline',
      'partial_sum_exact':{'numerator':str(partial.numerator),'denominator':str(partial.denominator)},
      'partial_sum_decimal_enclosure':interval(partial,partial),'pi_enclosure':interval(pi_lo,pi_hi),
      'tail_enclosure':interval(tail_lo,tail_hi),'lambda_enclosure':interval(lambda_lo,lambda_hi),
      'ratio_enclosure':interval(ratio_lo,ratio_hi),'log2_enclosure':interval(log_lo,log_hi),
      'inverse_displacement_enclosure':interval(shift_lo,shift_hi),
      'published_lambda_interval_verified':True,'published_ratio_interval_verified':True,
      'eventual_gap_conditions':'1/2 < exp(-lambda) < 1 and 0 < lambda/log(2) < 1',
      'method':'Exact divisor sums and Fraction partial sum; alternating Machin arctangents, integer-square-root bounds, alternating exponential bounds, positive atanh series for log(2). Decimal endpoints rounded outward.',
      'imported_tail_theorem':'Kolesnik, The Asymptotic Number of Score Sequences, Lemma 11, equation (17): (1-2/N)/(3*sqrt(pi)*N^(3/2)) <= sum_{k>N} N_k/(k*4^k) <= 1/(3*sqrt(pi)*N^(3/2)).',
      'source':'https://link.springer.com/article/10.1007/s00493-023-00037-4'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--fixtures',type=Path,default=Path(__file__).with_name('fixtures.json'))
    p.add_argument('--output',type=Path)
    p.add_argument('--only',choices=['all','schema','counts','algebra','certificates'],default='all')
    args=p.parse_args()
    try:
        f=read_fixtures(args.fixtures)
        result={'status':'PASS','arithmetic':'Python standard-library exact integers and fractions.Fraction only',
                'fixture_sha256':sha256(args.fixtures.read_bytes()).hexdigest()}
        if args.only in ['all','counts']:check_counts(f,result)
        if args.only in ['all','algebra']:
            check_algebra(f,result)
            check_universal_factor(result)
        if args.only in ['all','certificates']:check_certificates(f,result)
        result['limitations']=f['limitations']
        rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(rendered,encoding='utf-8')
        print(rendered,end='')
        return 0
    except ValidationError as e:
        print('VALIDATION_FAILURE '+str(e),file=sys.stderr)
        return 2

if __name__=='__main__':
    sys.exit(main())
