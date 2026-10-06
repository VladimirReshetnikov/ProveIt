#!/usr/bin/env python3
"""Independent finite exact regression companion for Report127; not an asymptotic certificate."""
import sys
sys.dont_write_bytecode = True
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent
MEMBERS = {'README.md', 'verify.py', 'negative_tests.py', 'evidence.json', 'provenance.json', 'manifest.sha256'}
PROOFS = {
    'sharp_upper': 'b8e88962f370ffd0d9c8c2826be7e30597f203c5b1af7685ad20c476632a46b8',
    'sharp_lower': '6b2c6fad019d31b7b3f2281d6ecbf157ab8766c78d74a171be036daaf84673ea',
    'local_kernel': '93046a0b03e75e328fd0cff3ae58272b6241784d5471d684e01aaf85017ab3ee',
    'corollaries': '77d9323ff29bf365bc8da3a3e99b795ac384f8bea7fea86cbfbcce1fde688492',
}
RANGES = {'row_height_max': 14, 'transform_b_max': 8, 'renewal_n_max': 22,
          'staircase_first': 256, 'staircase_last': 272, 'log_terms': 80,
          'repair_excess_samples': 96}
SCOPE = {'finite_only': True, 'asymptotics_certified': False, 'effective_onset': False,
         'numeric_asymptotic_tests': False, 'fitted_digits': False}

class Failure(Exception):
    pass

def demand(condition, message):
    if not condition:
        raise Failure(message)

def equal(actual, expected, message):
    demand(actual == expected, message)

def canonical(value):
    return json.dumps(value, sort_keys=True, indent=2) + '\n'

def digest(value):
    return sha256(canonical(value).encode()).hexdigest()

def inventory():
    paths = list(HERE.iterdir())
    demand(not any(p.is_symlink() for p in paths), 'INVENTORY: symlink')
    demand(not any(p.is_dir() for p in paths), 'INVENTORY: directory')
    demand(all(p.is_file() for p in paths), 'INVENTORY: nonregular member')
    equal({p.name for p in paths}, MEMBERS, 'INVENTORY: closed members')
    lines = (HERE / 'manifest.sha256').read_text(encoding='ascii').splitlines()
    entries = {}
    for line in lines:
        m = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_.-]+)', line)
        demand(m is not None, 'MANIFEST: syntax')
        h, name = m.groups()
        demand(name not in entries, 'MANIFEST: duplicate')
        entries[name] = h
    equal(set(entries), MEMBERS - {'manifest.sha256'}, 'MANIFEST: closed members')
    equal(list(entries), sorted(entries), 'MANIFEST: sorted members')
    for name, h in entries.items():
        equal(sha256((HERE / name).read_bytes()).hexdigest(), h, 'HASH: ' + name)

def pairs(items):
    result = {}
    for key, value in items:
        demand(key not in result, 'JSON: duplicate key ' + key)
        result[key] = value
    return result

def bad_number(value):
    raise Failure('JSON: nonfinite number')

def load(name):
    try:
        return json.loads((HERE / name).read_text(), object_pairs_hook=pairs, parse_constant=bad_number)
    except (ValueError, UnicodeError) as exc:
        raise Failure('JSON: invalid document') from exc

def keys(value, expected, label):
    demand(type(value) is dict and set(value) == set(expected), 'SCHEMA: ' + label + ' keys')

def integer(value, label):
    demand(type(value) is int, 'SCHEMA: ' + label + ' integer')

def rational(value, label):
    demand(type(value) is str, 'SCHEMA: ' + label + ' rational')
    try:
        answer = Q(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise Failure('SCHEMA: ' + label + ' rational') from exc
    equal(str(answer), value, 'SCHEMA: ' + label + ' canonical rational')
    return answer

def evidence():
    d = load('evidence.json')
    keys(d, {'schema', 'ranges', 'tilts', 'cutoffs', 'large_k', 'classes', 'floor_samples', 'algebra', 'scope'}, 'evidence')
    equal(d['schema'], 'report127-finite-evidence-v1', 'SCHEMA: version')
    keys(d['ranges'], RANGES, 'ranges')
    for k, v in d['ranges'].items():
        integer(v, 'ranges.' + k)
    equal(d['ranges'], RANGES, 'RANGE: mandatory coverage')
    demand(type(d['cutoffs']) is list, 'SCHEMA: cutoffs list')
    for c in d['cutoffs']:
        if c is not None:
            integer(c, 'cutoff')
    equal(d['cutoffs'], [None, 2, 4, 7], 'RANGE: boundary cutoffs')
    demand(type(d['large_k']) is list, 'SCHEMA: large_k list')
    for k in d['large_k']:
        integer(k, 'large_k')
    equal(d['large_k'], [512, 1024, 4096, 10000, 1000000, 100000000], 'RANGE: large staircase samples')
    keys(d['tilts'], {'u', 'v'}, 'tilts')
    for name in ('u', 'v'):
        demand(type(d['tilts'][name]) is list, 'SCHEMA: tilt list')
        d['tilts'][name] = [rational(x, 'tilt.' + name) for x in d['tilts'][name]]
    equal(d['tilts'], {'u': [Q(4,5), Q(1), Q(5,4)], 'v': [Q(4,5), Q(1), Q(6,5)]}, 'RANGE: rational tilts')
    keys(d['classes'], {'759', '247'}, 'classes')
    names = {'mu', 'x', 'y', 'alpha', 'D', 'a', 'A0', 'r', 'terminal_cap', 'counts', 'R_derivatives', 'A_derivatives'}
    for j, c in d['classes'].items():
        keys(c, names, 'class.' + j)
        for k in ('mu', 'x'):
            integer(c[k], j + '.' + k)
        if c['terminal_cap'] is not None:
            integer(c['terminal_cap'], j + '.terminal_cap')
        for k in ('y', 'alpha', 'D', 'a', 'A0', 'r'):
            c[k] = rational(c[k], j + '.' + k)
        demand(type(c['counts']) is list and len(c['counts']) == 9, 'SCHEMA: count prefix')
        for n in c['counts']:
            integer(n, 'count')
        for tag in ('R_derivatives', 'A_derivatives'):
            keys(c[tag], {'lambda', 'eta', 'lambda_lambda', 'lambda_eta', 'eta_eta'}, j + '.' + tag)
            c[tag] = {k: rational(v, j + '.' + tag + '.' + k) for k, v in c[tag].items()}
    demand(type(d['floor_samples']) is list, 'SCHEMA: floor samples')
    for entry in d['floor_samples']:
        demand(type(entry) is list and len(entry) == 3, 'SCHEMA: floor sample shape')
        for n in entry:
            integer(n, 'floor sample')
    equal([s[0] for s in d['floor_samples']], [256, 100000000], 'RANGE: floor anchors')
    keys(d['algebra'], {'sigma_cube_pi2', 'saddle_times_pi2', 'inverse_lambda_power', 'moment_leading', 'moment_loglog', 'moment_linear_offset', 'drift_sign', 'repair_bridge_sign', 'b0_duration'}, 'algebra')
    for k, v in d['algebra'].items():
        if k in ('sigma_cube_pi2', 'saddle_times_pi2'):
            keys(v, {'759', '247'}, 'algebra.' + k)
            d['algebra'][k] = {j: rational(x, 'algebra.' + k) for j, x in v.items()}
        else:
            d['algebra'][k] = rational(v, 'algebra.' + k)
    keys(d['scope'], SCOPE, 'scope')
    demand(all(type(v) is bool for v in d['scope'].values()), 'SCHEMA: scope boolean')
    equal(d['scope'], SCOPE, 'SCOPE: finite analytic boundary')
    return d

def provenance():
    p = load('provenance.json')
    keys(p, {'schema', 'source', 'proof_sha256', 'implementation', 'external_sequence_fixtures', 'fresh_network_retrieval', 'scope'}, 'provenance')
    equal(p['schema'], 'report127-finite-provenance-v1', 'PROVENANCE: version')
    equal(p['source'], {'authors': 'Nathan Britt and Nicholas Beaton', 'title': 'Completing the enumeration of inversion sequences avoiding triples of relations', 'version': 'arXiv:2512.21943v3', 'url': 'https://arxiv.org/html/2512.21943v3', 'locations': ['3.8', '3.9']}, 'PROVENANCE: primary source')
    equal(p['proof_sha256'], PROOFS, 'PROVENANCE: proof hashes')
    equal(p['implementation'], 'New standard-library implementation derived from the supplied formulas; no previous verifier is imported or executed', 'PROVENANCE: independence')
    demand(type(p['fresh_network_retrieval']) is bool, 'SCHEMA: provenance boolean')
    equal((p['external_sequence_fixtures'], p['fresh_network_retrieval']), ([], False), 'PROVENANCE: external data')
    equal(p['scope'], 'Finite checks and exact algebra only; hashes identify supplied mathematical inputs and do not certify their infinite-family statements', 'PROVENANCE: analytic boundary')

# Two-variable Taylor jets through total degree two. Coefficients are Taylor
# coefficients, so a pure quadratic coefficient is half the second derivative.
MONOMIALS = ((0,0), (1,0), (0,1), (2,0), (1,1), (0,2))
class Jet:
    def __init__(self, value):
        self.c = {k: Q(v) for k, v in value.items() if v} if type(value) is dict else ({(0,0): Q(value)} if value else {})
    def get(self, i, j):
        return self.c.get((i,j), Q(0))
    def __add__(self, other):
        b = other if isinstance(other, Jet) else Jet(other)
        return Jet({k: self.c.get(k,0) + b.c.get(k,0) for k in MONOMIALS})
    __radd__ = __add__
    def __neg__(self):
        return Jet({k:-v for k,v in self.c.items()})
    def __sub__(self, other):
        return self + (-other if isinstance(other,Jet) else -Q(other))
    def __rsub__(self, other):
        return -self + other
    def __mul__(self, other):
        b = other if isinstance(other, Jet) else Jet(other)
        answer = defaultdict(Q)
        for (i,j), a in self.c.items():
            for (k,l), v in b.c.items():
                if i+j+k+l <= 2:
                    answer[(i+k,j+l)] += a*v
        return Jet(dict(answer))
    __rmul__ = __mul__
    def inverse(self):
        c = self.get(0,0)
        demand(c != 0, 'JET: zero denominator')
        h = self*(1/c) - 1
        return (1 - h + h*h)*(1/c)
    def __truediv__(self, other):
        b = other if isinstance(other, Jet) else Jet(other)
        return self*b.inverse()
    def __rtruediv__(self, other):
        return self.inverse()*other
    def __pow__(self, exponent):
        demand(type(exponent) is int and exponent >= 0, 'JET: exponent')
        result = Jet(1)
        for _ in range(exponent):
            result = result*self
        return result
    def log_derivatives(self):
        c = self.get(0,0)
        h = self*(1/c)-1
        z = h-h*h*Q(1,2)
        return {'lambda': z.get(1,0), 'eta': z.get(0,1), 'lambda_lambda': 2*z.get(2,0), 'lambda_eta': z.get(1,1), 'eta_eta': 2*z.get(0,2)}

def exp_jet(value, axis):
    return Jet({(0,0): value, ((1,0) if axis == 0 else (0,1)): value,
                ((2,0) if axis == 0 else (0,2)): value/2})

def cat(b):
    return comb(2*b,b)//(b+1)

def choose(n, k):
    return comb(n,k) if 0 <= k <= n else 0

def multiplicity(kind, ell, b):
    return cat(b) * (choose(ell,b) if kind == 759 else choose(b+1,ell-b))

def transforms(kind, u, v):
    if kind == 759:
        A = v/(9*(1-1/(3*u)))
        R = 4*v/(9*(1-1/(3*u))*(1-u*v/3))
    else:
        A = v*(1+1/(2*u))/8
        R = v*(1+1/(2*u))/(2*(1-u*v/4))
    return A, R

def drop_cdf(kind, b, cutoff, u):
    # Probability recurrence, rather than summing multiplicity coefficients.
    if cutoff < b:
        return Q(0)
    if kind == 759:
        failure = 1/(3*u)
        term = (1-failure)**(b+1)
        result = term
        for k in range(cutoff-b):
            term *= Q(b+1+k,k+1)*failure
            result += term
        return result
    success = 1/(2*u+1)
    term = (1-success)**(b+1)
    result = term
    for k in range(min(cutoff-b,b+1)):
        term *= Q(b+1-k,k+1)*success/(1-success)
        result += term
    return result

def cdf_row(kind, p, u, v, mu, x):
    A, R = transforms(kind,u,v)
    return Q(x,mu)*u*v + A*sum(Q(cat(b),4**b)*R**b*drop_cdf(kind,b,p-1,u) for b in range(p))

def raw_row(kind, p, u, v, mu, x):
    # Sum legal finite ell first; sum the full original bulk duration by its
    # negative-binomial generating function. This formula also accepts Jets.
    t = x*u*v/mu
    answer = x*u*v/mu
    for b in range(p):
        removal = sum(multiplicity(kind,ell,b)*(1/(x*u))**ell for ell in range(b,p))
        bulk = (t/(1-t))**b if b else 1
        answer += (v/mu)*removal*bulk
    return answer

def raw_moments(kind, p, u, v, mu, x):
    t = x*u*v/mu
    answer = [Q(x,mu)*u*v]*6 # mass, Delta, L, Delta^2, Delta L, L^2
    for b in range(p):
        mean_w = Q(b)/(1-t)
        variance_w = b*t/(1-t)**2
        bulk = (t/(1-t))**b if b else 1
        for ell in range(b,p):
            weight = (v/mu)*multiplicity(kind,ell,b)*(1/(x*u))**ell*bulk
            md, ml = mean_w-ell, mean_w+1
            terms = [1, md, ml, variance_w+md*md, variance_w+md*ml, variance_w+ml*ml]
            answer = [a+weight*c for a,c in zip(answer,terms)]
    return answer

def local_checks(d):
    records = {}
    for kind in (759,247):
        c = d['classes'][str(kind)]
        mu,x = c['mu'],c['x']
        equal((mu,x,c['y'],c['terminal_cap']), (9,3,Q(1,2),None) if kind == 759 else (8,2,Q(1,3),2), 'MODEL: ' + str(kind))
        equal(c['a'], Q(x,mu), 'MODEL: ordinary edge')
        equal(Q(x,mu)*(1+1/c['y']), Q(1), 'MODEL: bulk probability row')
        u0,v0 = exp_jet(Q(1),0),exp_jet(Q(1),1)
        A,R = transforms(kind,u0,v0)
        equal(A.get(0,0), c['A0'], 'CRITICAL: A0')
        equal(R.get(0,0), Q(1), 'CRITICAL: R0')
        for name,value in R.log_derivatives().items():
            equal(value,c['R_derivatives'][name], 'CRITICAL: '+str(kind)+' R '+name)
        for name,value in A.log_derivatives().items():
            equal(value,c['A_derivatives'][name], 'CRITICAL: '+str(kind)+' A '+name)
        rd = R.log_derivatives()
        equal(rd['lambda'], Q(0), 'CRITICAL: centered per-b drift')
        equal(rd['eta'],c['alpha'],'CRITICAL: alpha')
        equal(rd['lambda_lambda']/rd['eta'],c['D'],'CRITICAL: diffusion')
        equal(c['a']+2*c['A0'], c['r'], 'CRITICAL: row mass')
        equal(1-c['r'], 2*c['A0'], 'CRITICAL: root constant cancellation')
        demand(0<c['r']<1, 'CRITICAL: killing')
        # The duration-conditioned warning follows by a Schur complement;
        # it is different from the unconstrained variance per genuine time.
        conditional = (rd['lambda_lambda']-rd['lambda_eta']**2/rd['eta_eta'])/rd['eta']
        equal(conditional,Q(1,2) if kind==759 else Q(1,6),'CRITICAL: conditional variance warning')
        transform_count = 0
        for u in d['tilts']['u']:
            for v in d['tilts']['v']:
                t,z = x*u*v/mu,1/(x*u)
                demand(0<t<1 and 0<z<1, 'RANGE: transform convergence')
                af,rf = transforms(kind,u,v)
                for b in range(d['ranges']['transform_b_max']+1):
                    ell_series = z**b/(1-z)**(b+1) if kind==759 else z**b*(1+z)**(b+1)
                    duration_series = (t/(1-t))**b if b else 1
                    equal((v/mu)*cat(b)*ell_series*duration_series,af*Q(cat(b),4**b)*rf**b,'TRANSFORM: fixed-b identity')
                    transform_count += 1
        row_count, moment_count, slopes = 0,0,[]
        for p in range(d['ranges']['row_height_max']+1):
            for u in d['tilts']['u']:
                for v in d['tilts']['v']:
                    direct = raw_row(kind,p,u,v,mu,x)
                    equal(cdf_row(kind,p,u,v,mu,x), direct, 'ROW: legal CDF equals raw drops')
                    row_count += 1
                    jet = raw_row(kind,p,exp_jet(u,0),exp_jet(v,1),mu,x)
                    m = raw_moments(kind,p,u,v,mu,x)
                    jet_m = [jet.get(0,0),jet.get(1,0),jet.get(0,1),2*jet.get(2,0),jet.get(1,1),2*jet.get(0,2)]
                    equal(jet_m,m,'MOMENT: raw law versus derivatives')
                    demand(m[2]>0,'DRIFT: positive duration')
                    slope = d['algebra']['drift_sign']*m[1]/m[2]
                    equal(m[1]+slope*m[2],Q(0),'DRIFT: implicit first derivative')
                    curvature = -(m[3]+2*slope*m[4]+slope*slope*m[5])/m[2]
                    # Substitute eta=lambda*slope+lambda^2*curvature/2 in
                    # the independently computed jet: both derivatives vanish.
                    equal(jet.get(1,0)+slope*jet.get(0,1),Q(0),'DRIFT: level-curve tangent')
                    equal(2*jet.get(2,0)+2*slope*jet.get(1,1)+2*slope*slope*jet.get(0,2)+curvature*jet.get(0,1),Q(0),'DRIFT: level-curve curvature')
                    demand(curvature<=0 and (p==0 or curvature<0),'DRIFT: concavity')
                    slopes.append([p,str(u),str(v),str(slope),str(curvature)])
                    moment_count += 1
            if p==0:
                equal(raw_row(kind,p,Q(1),Q(1),mu,x),c['a'],'ROW: root ordinary only')
            else:
                demand(raw_row(kind,p,Q(1),Q(1),mu,x)<c['r'],'ROW: legal zero-tilt killing')
        # Low-height b=0-only row: exact root is rational and no bulk duration.
        u = Q(5,4)
        B = raw_row(kind,1,u,Q(1),mu,x)
        root_v = 1/B
        equal(raw_row(kind,1,u,root_v,mu,x), Q(1), 'ROW: b0 exact root')
        equal(d['algebra']['b0_duration'],Q(1),'ROW: b0 duration')
        records[str(kind)] = {'fixed_b_transform_cases':transform_count,'legal_row_cases':row_count,'six_moment_and_drift_cases':moment_count,'drift_jet_sha256':digest(slopes),'conditional_variance_per_time':str(conditional),'row_root_height1_u5over4_v':str(root_v),'R_log_derivatives':{k:str(v) for k,v in rd.items()}}
    return records

# Original-time raw label propagation, independent of completed-cycle formula.
def raw_layers(kind, max_n, cap):
    states = {(0,0):1}
    boundaries = [{0:1}]
    for _ in range(max_n):
        nxt = defaultdict(int)
        for (p,c), count in states.items():
            targets = [((p+1,c),1)]
            if c:
                targets.append(((p+1,c-1),1))
            else:
                for ell in range(p):
                    for b in range(ell+1):
                        mult = multiplicity(kind,ell,b)
                        if mult:
                            targets.append(((p-ell,b),mult))
            for (height,commit),mult in targets:
                if cap is None or commit>0 or height<=cap:
                    nxt[(height,commit)] += count*mult
        states = dict(nxt)
        boundaries.append({p:value for (p,c),value in sorted(states.items()) if c==0})
    return boundaries

def countdown_counts(b, max_w):
    # Dynamic enumeration by the actual outstanding count. A return is emitted
    # once, at its first zero, and never propagated through the bulk process.
    if b == 0:
        return {0:1}
    states = {b:1}
    result = {}
    for w in range(1,max_w+1):
        nxt = defaultdict(int)
        for c,count in states.items():
            nxt[c] += count
            if c==1:
                result[w] = result.get(w,0)+count
            else:
                nxt[c-1] += count
        states = dict(nxt)
    return result

def renewal_layers(kind,max_n,cap):
    by_time = [defaultdict(int) for _ in range(max_n+1)]
    by_time[0][0]=1
    first_returns = {b:countdown_counts(b,max_n) for b in range(max_n+1)}
    for time in range(max_n):
        for p,count in list(by_time[time].items()):
            if cap is None or p+1<=cap:
                by_time[time+1][p+1] += count
            for ell in range(p):
                for b in range(ell+1):
                    mult = multiplicity(kind,ell,b)
                    if not mult:
                        continue
                    for w,ways in first_returns[b].items():
                        endtime = time+w+1
                        endpoint = p-ell+w
                        if endtime<=max_n and (cap is None or endpoint<=cap):
                            by_time[endtime][endpoint] += count*mult*ways
    return [dict(sorted(layer.items())) for layer in by_time]

def duration_checks(d):
    equal(countdown_counts(0,12),{0:1},'DURATION: b0 first return')
    first_count = 0
    for b in range(1,9):
        law = countdown_counts(b,18)
        for w in range(1,19):
            equal(law.get(w,0),choose(w-1,b-1),'DURATION: Pascal first return')
            first_count += 1
    out={}
    for kind in (759,247):
        comparisons=0
        hashes={}
        for cap in d['cutoffs']:
            raw=raw_layers(kind,d['ranges']['renewal_n_max'],cap)
            renewal=renewal_layers(kind,d['ranges']['renewal_n_max'],cap)
            equal(raw,renewal,'DURATION: '+str(kind)+' exact original-time recurrence')
            comparisons+=len(raw)
            hashes[str(cap)] = digest([{str(p):v for p,v in layer.items()} for layer in raw])
            if cap is None:
                terminal=d['classes'][str(kind)]['terminal_cap']
                counts=[sum(v for p,v in layer.items() if terminal is None or p<=terminal) for layer in raw]
                equal(counts[:9],d['classes'][str(kind)]['counts'],'DURATION: terminal prefix')
                demand(all(a<=d['classes'][str(kind)]['mu']**n for n,a in enumerate(counts)),'DURATION: finite coefficient growth bound')
                out[str(kind)]={'terminal_counts':counts}
        out[str(kind)].update({'boundary_distribution_comparisons':comparisons,'boundary_distribution_sha256':hashes})
    out['first_return_cases']=first_count
    return out

# Certified log enclosures: binary range reduction then the positive atanh
# series. The exact rational remainder is a geometric majorant.
def atanh_log(z, terms):
    demand(0<=z<1,'LOG: range reduction')
    total=Q(0)
    power=z
    for j in range(terms):
        total+=2*power/(2*j+1)
        power*=z*z
    remainder=2*power/((2*terms+1)*(1-z*z))
    return total,total+remainder

@lru_cache(None)
def log_bounds(n):
    demand(type(n) is int and n>=1,'LOG: positive integer')
    exponent=n.bit_length()-1
    power=1<<exponent
    z=Q(n-power,n+power)
    l2,u2=atanh_log(Q(1,3),RANGES['log_terms'])
    l,u=atanh_log(z,RANGES['log_terms'])
    return exponent*l2+l,exponent*u2+u

@lru_cache(None)
def certified_floor(k, power):
    lo,hi=log_bounds(k+1)
    lo*=k**power
    hi*=k**power
    demand(0<=hi-lo<Q(1,10**30),'LOG: certificate width')
    a,b=lo.numerator//lo.denominator,hi.numerator//hi.denominator
    equal(a,b,'LOG: unique certified floor')
    return a

def staircase(k):
    return certified_floor(k,2)

def support(kind,p,b,ell,w,alpha):
    demand(b>=1 and w>=b and b<=ell<=p-1,'STAIRCASE: legal support')
    if kind==247:
        demand(ell<=2*b+1,'STAIRCASE: binomial support')
    demand(abs(ell-alpha*b)<=Q(b,8) and abs(w-alpha*b)<=Q(b,8),'STAIRCASE: moderate window')
    return p+w-ell,w+1

def fill_runs(U,L,R):
    m=(U+L+R-1)//(L+R)
    excess=U-m*(L-R)
    demand(0<=excess<=2*R*m,'FILL: feasible excess')
    full,partial=divmod(excess,2*R)
    runs=[]
    if full:
        runs.append((L+R,full))
    if partial:
        runs.append((L-R+partial,1))
    remainder=m-full-(1 if partial else 0)
    if remainder:
        runs.append((L-R,remainder))
    demand(all(L-R<=length<=L+R and count>0 for length,count in runs),'FILL: interval support')
    equal(sum(length*count for length,count in runs),U,'FILL: exact duration')
    equal(sum(count for length,count in runs),m,'FILL: cycle count')
    return runs

def staircase_checks(d):
    ks=list(range(d['ranges']['staircase_first'],d['ranges']['staircase_last']+1))+d['large_k']
    for k,p,r in d['floor_samples']:
        equal([staircase(k),certified_floor(k,1)],[p,r],'LOG: frozen floor anchors')
    floors=[[k,staircase(k),certified_floor(k,1)] for k in ks]
    out={'floor_values':floors,'log_series_terms':RANGES['log_terms']}
    for kind in (759,247):
        alpha=d['classes'][str(kind)]['alpha']
        stage_checks=0
        local_bridges=0
        all_height_count=0
        fill_cases=0
        assemblies=0
        base=staircase(RANGES['staircase_first'])
        ascent=base
        descent=base-2
        witnesses=[]
        for k in ks:
            p,next_p=staircase(k),staircase(k+1)
            b=p//4
            center=alpha*b+Q(1,2)
            ell=center.numerator//center.denominator
            gap=next_p-p
            R=certified_floor(k,1)
            L=ell+1
            demand(0<R<L,'FILL: positive interval')
            for start,w,end in [(p,ell+gap,next_p),(next_p,ell-gap,p)]:
                got,_=support(kind,start,b,ell,w,alpha)
                equal(got,end,'STAIRCASE: stage endpoint')
                stage_checks+=1
            # Endpoint inequalities cover every plateau offset s in [-R,R].
            for s in (-R,0,R):
                got,duration=support(kind,p,b,ell+s,ell+s,alpha)
                equal((got,duration),(p,L+s),'STAIRCASE: return interval')
                stage_checks+=1
            for g in sorted({0,gap//2,gap-1}):
                up=support(kind,p,b,ell,ell+g,alpha)
                down=support(kind,p+g,b,ell,ell+d['algebra']['repair_bridge_sign']*g,alpha)
                equal(up,(p+g,ell+g+1),'BRIDGE: exact entrance')
                equal(down,(p,ell-g+1),'BRIDGE: exact repair')
                local_bridges+=2
            threshold=(L*L-R*R+2*R-1)//(2*R)
            # Explicit algebra behind the sufficient covering condition:
            # (U/(L+R)+1)*(L-R) <= U iff 2 R U >= L^2-R^2.
            demand(2*R*threshold>=L*L-R*R,'FILL: threshold rounding')
            test_U=list(range(threshold,threshold+RANGES['repair_excess_samples']))
            test_U += [threshold+offset for offset in (L-R-1,L-R,L+R-1,L+R,(L+R)**2,10**20)]
            for U in test_U:
                runs=fill_runs(U,L,R)
                fill_cases+=1
            # At a fixed m the greedy routine is tested across a full residue
            # system mod 2R at small/medium k; large k uses selected residues.
            if k<=RANGES['staircase_last']:
                m=(threshold+L+R-1)//(L+R)+2
                bottom=m*(L-R)
                for residue in range(2*R):
                    fill_runs(bottom+residue,L,R)
                    fill_cases+=1
                # Exhaust every height between successive certified steps.
                # We check bridge support and complete length assembly for each.
                for g in range(gap):
                    upward=support(kind,p,b,ell,ell+g,alpha)
                    downward=support(kind,p+g,b,ell,ell-g,alpha)
                    equal((upward[0],downward[0]),(p+g,p),'BRIDGE: exhaustive arbitrary height')
                    E=ascent+upward[1]
                    F=downward[1]+descent
                    U=threshold+(g % 97)
                    N=F+U
                    runs=fill_runs(U,L,R)
                    equal(downward[1]+sum(length*count for length,count in runs)+descent,N,'REPAIR: full exact residual time')
                    # Starting at root, E then N has the genuine summed clock;
                    # the repair terminal is exactly height two.
                    demand(E>0 and N>F and base>=3,'REPAIR: fixed base and terminal')
                    all_height_count+=1
                    assemblies+=1
                witnesses.append([k,p,gap,threshold,ascent,descent])
                ascent+=ell+gap+1
                descent+=ell-gap+1
        out[str(kind)]={'stage_and_return_endpoint_cases':stage_checks,'selected_bridge_cases':local_bridges,'exhaustive_arbitrary_heights':all_height_count,'exact_residual_time_assemblies':assemblies,'selected_and_residue_fill_cases':fill_cases,'assembly_witness_sha256':digest(witnesses)}
    return out

# Laurent polynomial algebra in (M,s,D,P), reduced by P=(2/3)D M^(-3).
# This verifies the displayed rational identities coefficientwise, rather than
# treating agreement at finitely many rational specializations as a proof.
def lp_add(a,b):
    out=dict(a)
    for power,value in b.items():
        out[power]=out.get(power,Q(0))+value
    return {power:value for power,value in out.items() if value}

def lp_mul(a,b):
    out={}
    for p,x in a.items():
        for q,y in b.items():
            key=tuple(i+j for i,j in zip(p,q))
            out[key]=out.get(key,Q(0))+x*y
    return {power:value for power,value in out.items() if value}

def lp_reduce(a):
    out={}
    for (m,s,d,p),v in a.items():
        key=(m-3*p,s,d+p)
        out[key]=out.get(key,Q(0))+v*Q(2,3)**p
    return {power:value for power,value in out.items() if value}

def formal_identities():
    term=lambda m,s,d,p,c=1:{(m,s,d,p):Q(c)}
    zero={}
    # (M^2 P / 2D)(s^(-1)-1) - (1/3M)(s^(-1)-1).
    kinetic=lp_add(term(2,-1,-1,1,Q(1,2)),term(2,0,-1,1,Q(-1,2)))
    potential=lp_add(term(-1,-1,0,0,Q(-1,3)),term(-1,0,0,0,Q(1,3)))
    equal(lp_reduce(lp_add(kinetic,potential)),zero,'FORMAL: variational first integral')
    equal(lp_reduce(lp_add(term(1,-2,0,1,Q(-1,2)),term(-2,-2,1,0,Q(1,3)))),zero,'FORMAL: Euler equation')
    equal(lp_reduce(lp_add(term(-3,0,0,0),term(0,0,-1,1,Q(-3,2)))),zero,'FORMAL: sigma cube')
    equal(lp_reduce(lp_add(term(3,0,0,0,3),term(0,0,1,-1,-2))),zero,'FORMAL: saddle constant')
    # In this independent two-variable polynomial identity M means a, s means x.
    square=lp_mul(lp_add(term(0,0,0,0),term(1,1,0,0,-3)),lp_add(term(0,0,0,0),term(1,1,0,0,-3)))
    square=lp_mul(square,term(0,-1,0,0,Q(1,3)))
    expected=lp_add(lp_add(term(0,-1,0,0,Q(1,3)),term(2,1,0,0,3)),term(1,0,0,0,-2))
    equal(square,expected,'FORMAL: dual square')
    # General convex residual, cleared of 3 g f^2: f^2-gf+g(g-f)=(g-f)^2.
    lhs=lp_add(lp_add(term(2,0,0,0),term(1,1,0,0,-2)),term(0,2,0,0))
    rhs=lp_mul(lp_add(term(0,1,0,0),term(1,0,0,0,-1)),lp_add(term(0,1,0,0),term(1,0,0,0,-1)))
    equal(lhs,rhs,'FORMAL: potential convex residual')
    return 6

# Algebraic regression, with P a formal positive stand-in for pi^2. Rational
# specializations verify identities subject to M^3 P = 2D/3. These evaluations
# do not compute pi, perform quadrature, or prove variational existence.
def constants_checks(d):
    cases=0
    for kind in (759,247):
        D=d['classes'][str(kind)]['D']
        equal(d['algebra']['sigma_cube_pi2'][str(kind)],3/(2*D),'CONSTANT: sigma cube')
        equal(d['algebra']['saddle_times_pi2'][str(kind)],2*D,'CONSTANT: derivative saddle')
        for M in (Q(1,3),Q(1),Q(7,2)):
            P=2*D/(3*M**3)
            sigma=1/M
            equal(sigma**3,3*P/(2*D),'VARIATIONAL: sigma normalization')
            for s in (Q(1,7),Q(1,2),Q(5,6)):
                f=M*s
                speed2=M*M*P*(1-s)/s
                equal(speed2/(2*D),(1/f-1/M)/3,'VARIATIONAL: first integral')
                second=-M*P/(2*s*s)
                equal(second,-D/(3*f*f),'VARIATIONAL: Euler equation')
                for g in (Q(1,4),Q(2,3),Q(3)):
                    equal(1/(3*g)-1/(3*f)+(g-f)/(3*f*f),(g-f)**2/(3*g*f*f),'VARIATIONAL: convex potential residual')
                cases+=1
            potential=2/(3*M)
            kinetic=1/(3*M)
            equal(potential+kinetic,sigma,'VARIATIONAL: action integral coefficients')
            equal(2*potential-kinetic,sigma,'VARIATIONAL: dual integral coefficients')
            equal(3/sigma**3,2*D/P,'CONSTANT: saddle normalization')
            for lam in (Q(2),Q(3),Q(5)):
                # Cubes remove every fractional exponent; lambda^(4/3)
                # becomes lambda^4 in the inverse correction coefficient.
                q=d['algebra']['inverse_lambda_power']
                equal(3*q,Q(4),'INVERSE: lambda scaling power')
                equal(sigma**3/lam**4,3*P/(2*D*lam**4),'INVERSE: correction cube')
        for a in (Q(1,5),Q(1),Q(3)):
            for x in (Q(1,7),Q(1),Q(5)):
                derivative=-3*a*a
                equal(1/(3*x)-derivative*x-2*a,(1-3*a*x)**2/(3*x),'DUAL: square identity')
                cases+=1
    # For psi=x^p (log x)^q, solving x=C k^a (log k)^b in
    # c psi(x)~k/p gives a=1/p, b=-q/p and the objective penalty -1/p.
    power,log_power=Q(1,3),Q(2,3)
    derived=(1/power,-log_power/power,-1/power)
    equal((d['algebra']['moment_leading'],d['algebra']['moment_loglog'],d['algebra']['moment_linear_offset']),derived,'DERIVATIVE: saddle coefficients')
    equal(d['algebra']['inverse_lambda_power'],1+power,'INVERSE: scaled regular variation')
    # d/d(log x) of psi(x) is psi(x)/3+2 psi(x)/(3 log x).
    for logarithm in (Q(1),Q(3),Q(7)):
        equal(Q(1,3)+Q(2,3)/logarithm,(1+2/logarithm)/3,'DERIVATIVE: saddle equation factor')
    # Exact exponent bookkeeping for H, S, theta and the drift rescaling.
    H=(Q(2,3),Q(1,3)); S=(Q(1,3),Q(2,3)); n=(Q(1),Q(0))
    add=lambda a,b:tuple(x+y for x,y in zip(a,b))
    sub=lambda a,b:tuple(x-y for x,y in zip(a,b))
    equal(add(H,H),add(n,S),'SCALE: H squared')
    equal(sub(H,n),sub(S,H),'SCALE: theta')
    equal(add(sub(n,S),sub(H,n)),sub(n,H),'SCALE: drift derivative')
    return {'coefficientwise_formal_identities':formal_identities(),'rational_variational_and_dual_cases':cases,'formal_pi2_only':True,'inverse_lambda_exponent':'4/3','moment_coefficients':['3','-2','-3'],'numeric_pi_evaluation':False}

def main():
    demand(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--output'),'USAGE: verify.py [--output PATH]')
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None:
        demand(output!=HERE and HERE not in output.parents,'OUTPUT: outside sealed checks required')
    inventory()
    before={p.name:sha256(p.read_bytes()).hexdigest() for p in HERE.iterdir()}
    d=evidence()
    provenance()
    result={'schema':'report127-finite-results-v1','status':'PASS','arithmetic':'integer and exact rational; no floating-point calculations','scope':SCOPE,'local_rows_and_moments':local_checks(d),'duration_recurrence':duration_checks(d),'staircase_and_repair':staircase_checks(d),'constant_algebra':constants_checks(d),'source_proof_sha256':PROOFS}
    inventory()
    equal({p.name:sha256(p.read_bytes()).hexdigest() for p in HERE.iterdir()},before,'IMMUTABILITY: source changed')
    if output is not None:
        output.write_text(canonical(result),encoding='utf-8')
    else:
        print(canonical(result),end='')
    if output is not None:
        print('PASS: Report127 independent finite exact checks')

if __name__=='__main__':
    try:
        main()
    except Failure as exc:
        print('FAIL: '+str(exc),file=sys.stderr)
        sys.exit(1)
