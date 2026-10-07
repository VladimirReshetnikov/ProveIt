#!/usr/bin/env python3
"""Report286 exact finite diagnostics, using only the Python standard library.

The universal existence and sparse-defect theorems are proved in article.tex.
This module enumerates explicitly bounded finite examples and exact rational
certificates. It does not construct the astronomical universal word, verify
Lean, or infer theorems from experiments. All validation remains live under -O.
The CLI accepts no input; public helpers reject nonexact and oversized inputs.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product
from math import comb, gcd
from pathlib import Path
import hashlib
import base64
import os
import stat
import json

ROOT = Path(__file__).absolute().parents[1]
MAX_BITS = 256
MAX_MODULUS = 256
MAX_ENERGY_MODULUS = 16
MAX_PREFIX = 4096
MAX_BRANCHES = 64


def require(condition, context):
    """Raise on a failed finite certificate, including under optimized Python."""
    if not condition:
        raise RuntimeError(context)


def _integer(value, name, low=0, high=MAX_PREFIX):
    """Accept only a bounded built-in integer, never bool or coercible text."""
    if type(value) is not int or not low <= value <= high:
        raise ValueError(name + ' must be a bounded built-in integer')
    return value


def rational(value):
    """Accept bounded built-in integers/Fractions only; no approximate input."""
    if type(value) not in (int, Q):
        raise ValueError('an exact integer or Fraction is required')
    result = Q(value)
    if (abs(result.numerator).bit_length() > MAX_BITS
            or result.denominator.bit_length() > MAX_BITS):
        raise ValueError('rational input exceeds the bit budget')
    return result


def _sequence(values, name, maximum, length=None):
    if type(values) not in (tuple, list) or len(values) > maximum:
        raise ValueError(name + ' must be a bounded tuple or list')
    if length is not None and len(values) != length:
        raise ValueError(name + ' has the wrong length')
    return values


def ceil_fraction(value):
    value = rational(value)
    return -((-value.numerator) // value.denominator)


def ln_unit_bounds(value, terms=45):
    """Rational atanh-series enclosure of log(value), for 1 <= value <= 2."""
    value = rational(value)
    _integer(terms, 'terms', 1, 128)
    if not 1 <= value <= 2:
        raise ValueError('logarithm argument must lie in [1,2]')
    z = (value - 1)/(value + 1)
    z2 = z*z
    power = z
    total = Q(0)
    for j in range(terms):
        total += 2*power/(2*j+1)
        power *= z2
    remainder = 2*power/((2*terms+1)*(1-z2))
    return total, total + remainder


def ln_integer_bounds(value, terms=45):
    _integer(value, 'logarithm argument', 1, (1 << MAX_BITS)-1)
    _integer(terms, 'terms', 1, 128)
    k = value.bit_length()-1
    l2, u2 = ln_unit_bounds(Q(2), terms)
    lm, um = ln_unit_bounds(Q(value, 1 << k), terms)
    return k*l2+lm, k*u2+um


def exact_L0(modulus, alphabet_size):
    """Certify the theorem's logarithm ceiling, never approximate it by floats."""
    _integer(modulus, 'modulus', 6, 1 << 40)
    _integer(alphabet_size, 'alphabet size', 2, modulus//3)
    count = 2*alphabet_size*modulus**3 + modulus**5
    lo, hi = ln_integer_bounds(2*count)
    # Series outputs are deliberately not restricted to the input bit budget.
    low = -((-128*alphabet_size*lo.numerator)//lo.denominator)
    high = -((-128*alphabet_size*hi.numerator)//hi.denominator)
    require(low == high, 'rational logarithm enclosure did not certify L0 ceiling')
    return max(8*alphabet_size, low)


def _interval_parameters(modulus, alphabet_size):
    _integer(modulus, 'modulus', 6, MAX_MODULUS)
    _integer(alphabet_size, 'alphabet size', 2, modulus//3)


def active_position_certificate(modulus, alphabet_size, delta, intercept, length):
    """Count active values along a prefix; the value sequence may repeat.

    This is an arithmetic certificate only. A length greater than the ambient
    modulus is allowed here, but is not called a proper domain progression.
    A zero value step is excluded because the half-density lemma is nonconstant.
    """
    _interval_parameters(modulus, alphabet_size)
    _integer(delta, 'nonzero value step', 1, modulus-1)
    _integer(intercept, 'intercept', 0, modulus-1)
    _integer(length, 'prefix length', 0, MAX_PREFIX)
    order = modulus//gcd(modulus, delta)
    period = tuple((intercept+delta*t) % modulus for t in range(order))
    count = sum(value < alphabet_size for value in period)
    whole, remainder = divmod(length, order)
    actual = sum((intercept+delta*t) % modulus < alphabet_size for t in range(length))
    period_upper = whole*count + min(remainder, count)
    require(len(set(period)) == order, 'value period is not a coset enumeration')
    require(count <= (alphabet_size*order+modulus-1)//modulus, 'coset ceiling')
    require(2*count <= order and count <= alphabet_size, 'coset half density')
    require(actual <= period_upper and 2*actual <= length+2*alphabet_size, 'prefix bound')
    if length >= 8*alphabet_size:
        require(8*actual <= 5*length, 'long-prefix active count')
    return dict(order=order, coset_hits=count, active_positions=actual,
                period_prefix_upper=period_upper, half_plus_alphabet=Q(length,2)+alphabet_size)


def affine_list_coverage(modulus, alphabet_size, start, step, word, branches):
    """Evaluate an arbitrary bounded affine list on one proper progression.

    Return counts, not a claim that this arbitrary word satisfies the theorem.
    Duplicate branches, empty lists, nonunit steps, and singleton restrictions
    are allowed. Coefficients are canonical residues; no silent normalization.
    """
    _integer(modulus, 'modulus', 1, MAX_MODULUS)
    _integer(alphabet_size, 'alphabet size', 1, modulus)
    _integer(start, 'start', 0, modulus-1)
    _integer(step, 'step', 0, modulus-1)
    _sequence(word, 'word', MAX_MODULUS)
    if not word or len(word) > modulus//gcd(modulus, step):
        raise ValueError('word must index a nonempty proper progression')
    for value in word:
        _integer(value, 'word symbol', 0, alphabet_size-1)
    _sequence(branches, 'branches', MAX_BRANCHES)
    for branch in branches:
        _sequence(branch, 'branch coefficient pair', 2, 2)
        for value in branch:
            _integer(value, 'branch coefficient', 0, modulus-1)
    points = tuple((start+step*t) % modulus for t in range(len(word)))
    covered = set()
    constants = set()
    restricted = []
    for alpha, beta in branches:
        values = tuple((alpha*x+beta) % modulus for x in points)
        constant = len(set(values)) == 1
        useful = values[0] if constant and values[0] < alphabet_size else None
        if useful is not None:
            constants.add(useful)
        hits = tuple(t for t, value in enumerate(values) if value == word[t])
        covered.update(hits)
        restricted.append(dict(constant=constant, useful_value=useful, agreements=len(hits)))
    counts = tuple(word.count(v) for v in range(alphabet_size))
    return dict(covered=len(covered), distinct_useful_constants=tuple(sorted(constants)),
                symbol_counts=counts, heaviest_mass=sum(sorted(counts, reverse=True)[:len(branches)]),
                restrictions=restricted)


def binomial_probability(trials, alphabet_size, first, last):
    """Exact P(first <= Bin(trials,1/R) <= last), allowing an empty interval."""
    _integer(trials, 'trials', 0, 1024)
    _integer(alphabet_size, 'alphabet size', 2, 64)
    _integer(first, 'first index', 0, trials+1)
    _integer(last, 'last index', -1, trials)
    if first > last:
        return Q(0)
    return Q(sum(comb(trials,k)*(alphabet_size-1)**(trials-k)
                 for k in range(first,last+1)), alphabet_size**trials)


def cube_root_bounds(value, bits=24):
    """Dyadic rational enclosure, certified by cubing, of a nonnegative cube root."""
    value = rational(value)
    _integer(bits, 'precision bits', 0, 64)
    if value < 0:
        raise ValueError('cube-root argument must be nonnegative')
    scale = 1 << bits
    target = value.numerator*scale**3
    low, high = 0, 1 << ((target.bit_length()+2)//3)
    while low < high:
        mid = (low+high+1)//2
        if mid**3*value.denominator <= target:
            low = mid
        else:
            high = mid-1
    lo = Q(low, scale)
    hi = lo if lo**3 == value else Q(low+1, scale)
    require(lo**3 <= value <= hi**3, 'cube-root rational enclosure')
    return lo, hi


def _energy_inputs(modulus, values, weights):
    _integer(modulus, 'energy modulus', 1, MAX_ENERGY_MODULUS)
    _sequence(values, 'map values', MAX_ENERGY_MODULUS, modulus)
    _sequence(weights, 'weights', MAX_ENERGY_MODULUS, modulus)
    for value in values:
        _integer(value, 'map value', 0, modulus-1)
    exact = tuple(rational(w) for w in weights)
    if any(w < 0 for w in exact):
        raise ValueError('weights must be nonnegative')
    return exact


def _energy(modulus, values, weights):
    total = Q(0)
    for x, y, z in product(range(modulus), repeat=3):
        t = (x+y-z) % modulus
        if (values[x]+values[y]-values[z]-values[t]) % modulus == 0:
            total += weights[x]*weights[y]*weights[z]*weights[t]
    return total


def respected_energy(modulus, values, weights):
    """Enumerate ordered additive quadruples respected by a residue-valued map."""
    weights = _energy_inputs(modulus, values, weights)
    return _energy(modulus, values, weights)


def sparse_energy_certificate(modulus, values, weights, support):
    """Certify the disjoint outside/inside energy bound for one finite input.

    The declared support may contain extra zeros, may be noninterval, and may
    be empty. Every map value outside it must be zero. This verifies rational
    nonnegative weights; the article proves the result for all real weights.
    """
    weights = _energy_inputs(modulus, values, weights)
    _sequence(support, 'support', MAX_ENERGY_MODULUS)
    for value in support:
        _integer(value, 'support element', 0, modulus-1)
    inside = set(support)
    if len(inside) != len(support):
        raise ValueError('support must have no repeated elements')
    if any(values[x] != 0 for x in range(modulus) if x not in inside):
        raise ValueError('map must vanish outside its declared support')
    return _sparse_certificate(modulus, values, weights, inside)


def _sparse_certificate(modulus, values, weights, inside):
    m = len(inside)
    A = sum((weights[x] for x in range(modulus) if x not in inside), Q(0))
    B = sum((weights[x] for x in inside), Q(0))
    convolution = [Q(0)]*modulus
    for x in range(modulus):
        if x in inside:
            continue
        for y in range(modulus):
            if y not in inside:
                convolution[(x+y) % modulus] += weights[x]*weights[y]
    outside = sum((v*v for v in convolution), Q(0))
    diagonal = sum((weights[x]**2 for x in inside), Q(0))**2
    lower = A**4/modulus + (B**4/(m*m) if m else Q(0))
    energy = _energy(modulus, values, weights)
    root_lo, root_hi = cube_root_bounds(Q(m*m,modulus))
    coefficient_lower = 1/(1+root_hi)**3
    holder_lower = coefficient_lower*(A+B)**4/modulus
    require(outside >= A**4/modulus, 'outside convolution Cauchy-Schwarz')
    require(not m or diagonal >= B**4/(m*m), 'inside diagonal Cauchy-Schwarz')
    require(energy >= outside+diagonal >= lower >= holder_lower,
            'sparse disjoint-family or Holder certificate')
    return dict(outside_mass=A, inside_mass=B, energy=energy, outside_energy=outside,
                inside_diagonal=diagonal, disjoint_lower=lower,
                root_interval=(root_lo,root_hi), coefficient_lower=coefficient_lower,
                holder_lower=holder_lower)


def simultaneous_energy(modulus, families, weights):
    """Weighted energy imposing every map's condition; an empty family imposes none."""
    _integer(modulus, 'energy modulus', 1, MAX_ENERGY_MODULUS)
    _sequence(families, 'map family', 8)
    exact = _energy_inputs(modulus, (0,)*modulus, weights)
    for values in families:
        _energy_inputs(modulus, values, exact)
    total = Q(0)
    for x,y,z in product(range(modulus),repeat=3):
        t = (x+y-z) % modulus
        if all((a[x]+a[y]-a[z]-a[t]) % modulus == 0 for a in families):
            total += exact[x]*exact[y]*exact[z]*exact[t]
    return total


def _poly_add(*polynomials):
    result = {}
    for polynomial in polynomials:
        for term, coefficient in polynomial.items():
            result[term] = result.get(term,0)+coefficient
    return {term:coefficient for term,coefficient in result.items() if coefficient}


def _poly_mul(first, second):
    result = {}
    for a,ca in first.items():
        for b,cb in second.items():
            term = tuple(x+y for x,y in zip(a,b))
            result[term] = result.get(term,0)+ca*cb
    return {term:coefficient for term,coefficient in result.items() if coefficient}


def _poly_power(polynomial, exponent):
    result = {(0,0,0):1}
    for unused in range(exponent):
        result = _poly_mul(result,polynomial)
    return result


def check_holder_identity():
    # Variables are (t,A,B). This is an exact polynomial identity, not a fit.
    one, t, A, B = ({(0,0,0):1},{(1,0,0):1},{(0,1,0):1},{(0,0,1):1})
    lhs = _poly_add(
        _poly_mul(_poly_power(_poly_add(one,t),3),
                  _poly_add(_poly_mul(_poly_power(t,3),_poly_power(A,4)),_poly_power(B,4))),
        {term:-coefficient for term,coefficient in
         _poly_mul(_poly_power(t,3),_poly_power(_poly_add(A,B),4)).items()})
    square = _poly_power(_poly_add(_poly_mul(t,A),{(0,0,1):-1}),2)
    positive = {(4,2,0):1,(3,2,0):3,(2,2,0):3,
                (3,1,1):2,(2,1,1):6,(1,1,1):2,
                (2,0,2):3,(1,0,2):3,(0,0,2):1}
    require(lhs == _poly_mul(square,positive), 'exact Holder factorization coefficients')
    require(all(coefficient > 0 for coefficient in positive.values()), 'positive Holder factor')
    N,m,A_mass,B_mass = 8,1,Q(2),Q(1)
    coefficient = Q(8,27)
    require(Q(m*m,N) == Q(1,2)**3, 'sharp Holder example root')
    require(A_mass**4/N+B_mass**4/(m*m) == coefficient*(A_mass+B_mass)**4/N == 3,
            'sharp Holder equality example')
    return dict(identity_terms=len(lhs),positive_factor_terms=len(positive),
        factorization='(1+t)^3(t^3 A^4+B^4)-t^3(A+B)^4=(tA-B)^2 P(t,A,B)',
        positive_factor=[dict(exponents=term,coefficient=positive[term]) for term in sorted(positive)],
        equality_example=dict(N=N,m=m,A=A_mass,B=B_mass,coefficient=coefficient,lower=3))


def check_family_energy():
    values = (1,0,0,0)
    ordinary = simultaneous_energy(4,(),(1,)*4)
    single = simultaneous_energy(4,(values,),(1,)*4)
    repeated = simultaneous_energy(4,(values,values),(1,)*4)
    constants = simultaneous_energy(4,((0,)*4,(2,)*4),(1,)*4)
    require(ordinary == constants == 64 and single == repeated == 34, 'empty/nonempty family distinction')
    rational_values = (1,2,0,0,0,0)
    weights = tuple(Q(x+1,x+2) for x in range(6))
    weighted_ordinary = simultaneous_energy(6,(),weights)
    weighted_respected = simultaneous_energy(6,(rational_values,)*3,weights)
    require(weighted_ordinary == Q(1956830316641,31116960000), 'rational ordinary energy')
    require(weighted_respected == Q(295080890747,10372320000), 'rational respected energy')
    require(simultaneous_energy(6,(),(0,)*6) == 0, 'zero-weight empty family')
    coefficient_cases = 0
    for gamma in (Q(1,2),Q(3,4)):
        for size in range(9):
            energy = simultaneous_energy(4,(values,)*size,(1,)*4)
            coefficient = gamma**(8*size)
            require(energy >= coefficient*64, 'all-family coefficient sample')
            if size:
                require(coefficient <= gamma**8, 'nonempty-family coefficient monotonicity')
            else:
                require(coefficient == 1 and energy == ordinary, 'empty-family coefficient one')
            coefficient_cases += 1
    return dict(N=4,coefficient_cases=coefficient_cases,empty_family=ordinary,single_map=single,repeated_map=repeated,
                constant_maps=constants,rational_ordinary=weighted_ordinary,
                rational_respected=weighted_respected,
                scope='Finite representatives of the all-family reduction; no enumeration of all real weights')


def check_named_identities():
    cubes = 0
    rows = []
    for N in range(1,10):
        a = tuple((y*y+1) % N if y < (N+1)//2 else 0 for y in range(N))
        good_pairs = set()
        for anchor,h,y in product(range(N),repeat=3):
            base_value = a[y]
            shifted_value = a[y]
            cube_value = (base_value-shifted_value) % N
            remainder = base_value
            phi_one = shifted_value
            require(cube_value == 0 and (phi_one-(-cube_value+remainder)) % N == 0,
                    'named k=1 zero cube and remainder identity')
            if anchor == 0:
                good_pairs.add((h,y))
            cubes += 1
        require(len(good_pairs) == N*N, 'full named good domain including h=0')
        rows.append(dict(N=N,cube_elements_per_side=N*N,good_pairs=len(good_pairs),
                         arrangements_fixed_side=N**31,arrangements_global=N**32))
    # Enumerate small arrangement cross sections; then the d=8,N=2 free data.
    arrangement_rows = []
    for N,d in ((1,1),(2,1),(3,1),(2,2),(3,2),(2,8)):
        completions = 0
        for prefix in product(range(N),repeat=2*d-1):
            last = (sum(prefix[:d])-sum(prefix[d:])) % N
            solutions = sum((sum(prefix[:d])-sum(prefix[d:])-candidate) % N == 0
                            for candidate in range(N))
            require(solutions == 1 and 0 <= last < N, 'unique arrangement coordinate completion')
            completions += 1
        require(completions == N**(2*d-1), 'arrangement free-coordinate count')
        arrangement_rows.append(dict(N=N,d=d,cross_section_completions=completions,
                                     fixed_side_count=N**(4*d-1),global_count=N**(4*d)))
    fourier = []
    for N in range(1,17):
        for frequency in range(N):
            order = N//gcd(N,frequency)
            coefficients = [0]*order
            for x in range(N):
                exponent = 0 if order == 1 else ((frequency//gcd(N,frequency))*x) % order
                coefficients[exponent] += N
            if frequency == 0:
                require(coefficients == [N*N], 'unnormalized zero-frequency coefficient')
                reduced = N*N
            else:
                require(order >= 2 and coefficients == [N*N//order]*order,
                        'uniform character exponents')
                # Equal coefficients are a scalar multiple of 1+z+...+z^(order-1),
                # which vanishes at every primitive root of order > 1.
                reduced = 0
            fourier.append(dict(N=N,frequency=frequency,character_order=order,
                                constant_correlation=N,transform=reduced))
    return dict(cube_identity_cases=cubes,domain_rows=rows,arrangement_rows=arrangement_rows,
                spectrum_rows=fourier,
                scope='Exact k=1 algebra and finite character cancellation; the large arrangement sets are counted, not enumerated')


def check_gamma_one_boundary():
    rows = []
    for N in range(1,6):
        full_energy_count = 0
        for values in product(range(N),repeat=N):
            energy = _energy(N,values,(1,)*N)
            alpha = (values[1]-values[0]) % N if N > 1 else 0
            affine = all(values[x] == (values[0]+alpha*x) % N for x in range(N))
            require((energy == N**3) == affine, 'coefficient-one affine rigidity boundary')
            full_energy_count += energy == N**3
        require(full_energy_count == N*N, 'all cyclic affine functions counted exactly')
        rows.append(dict(N=N,words=N**N,full_energy_words=full_energy_count))
    return dict(rows=rows,scope='Finite one-variable coefficient-one boundary, not a formal proof of the full endpoint theorem')


def dimension_certificate(k):
    """Bounded exact exponent comparisons; no astronomical iteration is evaluated."""
    _integer(k,'dimension parameter',1,32)
    # r0 >= 2^((k+3)*2^(2^(k+6))). Compare its exponent to log2(2 E_(k+1)).
    inner = 2**(k+6)
    exponent_lower = 2**(k+10)
    target_log2 = 1+2**(k+9)
    require(inner >= k+10 and k+3 >= 1 and exponent_lower >= target_log2,
            'iteration lower bound r0 >= 2 E_(k+1)')
    require(2**(k+9) == 2*2**(k+8), 'E_(k+1) = E_k squared at the exponent level')
    return dict(k=k,iteration_inner_exponent=inner,iteration_log2_lower=exponent_lower,
                target_log2_two_E=target_log2,global_arrangement_exponent=17*k+15,
                fixed_side_arrangement_exponent=16*k+15,cube_domain_exponent=k+1,
                full_correlation_exponent=k,zero_fourier_exponent=k+1)


def check_general_dimensions():
    dimensions = [dimension_certificate(k) for k in range(1,33)]
    boolean_rows = []
    for k in range(1,9):
        vertices = tuple(product((0,1),repeat=k))
        alternating = sum((-1)**sum(vertex) for vertex in vertices)
        remainder = -sum((-1)**(k+sum(vertex)) for vertex in vertices if not all(vertex))
        require(alternating == 0 and remainder == 1, 'general Boolean cube/remainder signs')
        boolean_rows.append(dict(k=k,vertices=len(vertices),alternating_sum=alternating,
                                 remainder_coefficient=remainder))
    geometry = []
    for k in range(1,9):
        for N in (2,4,6):
            free_cross_sections = N**15
            horizontal_bases = N**(16*k)
            sides = N**k
            require(horizontal_bases*free_cross_sections == N**(16*k+15), 'fixed-side arrangements')
            require(sides*horizontal_bases*free_cross_sections == N**(17*k+15), 'global arrangements')
            for frequency in range(N):
                order = N//gcd(N,frequency)
                coefficients = [0]*order
                for x in range(N):
                    exponent = 0 if order == 1 else ((frequency//gcd(N,frequency))*x) % order
                    coefficients[exponent] += N**k
                require(coefficients == [N**(k+1)//order]*order, 'general-dimensional Fourier cancellation')
            m = 2
            slab = N**k*m
            require(Q(slab,N**(k+1)) == Q(m,N), 'dimension-independent deleted-slab fraction')
            volume = m**(k+1)
            require(Q(5,16)*volume < Q(1,2)*volume, 'general-dimensional local mass gap')
            geometry.append(dict(k=k,N=N,cube_elements_per_side=N**(k+1),good_pairs=N**(k+1),
                arrangements_fixed_side=horizontal_bases*free_cross_sections,
                arrangements_global=sides*horizontal_bases*free_cross_sections,
                correlation=N**k,zero_fourier=N**(k+1),deleted_slab_fraction=Q(m,N)))
    return dict(dimensions=dimensions,boolean_rows=boolean_rows,geometry_rows=geometry,
        scope='Finite exponent comparisons k=1..32 and Boolean/geometry checks k=1..8; article proves every fixed k >= 1')


def local_cover_ratio(graph_budget, alphabet_size):
    """Algebraic fibre-cover fraction min(1,5Q/(4R)); no word is constructed."""
    graph_budget = rational(graph_budget)
    _integer(alphabet_size, 'alphabet size', 1, 1 << 40)
    if graph_budget < 0:
        raise ValueError('graph budget must be nonnegative')
    return min(Q(1), 5*graph_budget/(4*alphabet_size))


def check_cosets():
    cases = 0
    for N in range(6,121):
        for R in range(2,N//3+1):
            for order in range(2,N+1):
                if N % order:
                    continue
                spacing = N//order
                for intercept in range(spacing):
                    count = sum((s-intercept) % spacing == 0 for s in range(R))
                    ceiling = (R*order+N-1)//N
                    require(count <= ceiling <= (order+2)//3, 'coset ceiling chain')
                    require(2*((order+2)//3) <= order, 'one-third ceiling to half')
                    require(count <= R and 2*count <= order, 'coset hit bounds')
                    cases += 1
    return dict(cases=cases, scope='All subgroup cosets for 6 <= N <= 120 and 2 <= R <= floor(N/3)')


def check_prefixes():
    cases = long_cases = 0
    for N in range(6,41):
        for R in range(2,N//3+1):
            for delta in range(1,N):
                for intercept in range(N):
                    active = 0
                    for length in range(1,N+1):
                        active += (intercept+delta*(length-1)) % N < R
                        require(2*active <= length+2*R, 'active prefix bound')
                        if length >= 8*R:
                            require(8*active <= 5*length, 'long active prefix bound')
                            long_cases += 1
                        cases += 1
    examples = [active_position_certificate(*args) for args in
                ((6,2,3,0,0),(6,2,3,0,17),(40,2,20,0,20),(40,2,1,0,16))]
    return dict(cases=cases,long_prefix_cases=long_cases,examples=examples,
                scope='Every nonzero value step, intercept, and length 1..N for N=6..40')


def check_tails():
    certificates = []
    for R in range(2,9):
        for multiplier in (8,9,16,32,64):
            length = multiplier*R
            cases = (
                ('symbol_lower', length, 0, (7*length-1)//(8*R), Q(length,128*R)),
                ('symbol_upper', length, 5*length//(4*R)+1, length, Q(length,36*R)),
                ('affine_upper', (length+2*R)//2, 3*length//(4*R)+1,
                 (length+2*R)//2, Q(3*length,256*R)))
            for label, trials, first, last, exponent in cases:
                probability = binomial_probability(trials,R,first,last)
                base = 1-exponent/1024
                require(0 < base <= 1, 'positive rational exponential surrogate')
                # log(1-u) <= -u implies base**1024 <= exp(-exponent).
                require(probability <= base**1024, 'exact tail exceeds rational certificate')
                certificates.append(dict(event=label,R=R,L=length,trials=trials,
                    first=first,last=last,probability=probability,negative_exponent=exponent,
                    exponential_lower_base=base,exponential_lower_power=1024))
    require(Q(1,4)**2/(2+Q(1,4)) == Q(1,36), 'upper Chernoff coefficient')
    require(Q(1,8)**2/(2*(Q(5,8)+Q(1,8)/3)) == Q(3,256), 'Bernstein coefficient')
    return dict(cases=len(certificates),certificates=certificates,
                certificate_meaning='probability <= base^power <= exp(-negative_exponent)')


def check_list_example():
    N, R, step, length = 40, 2, 2, 20
    points = tuple(step*t % N for t in range(length))
    word = (0,)*10+(1,)*10
    entries = []
    nonconstant_maximum = 0
    aliases = []
    for alpha,beta in product(range(N),repeat=2):
        values = tuple((alpha*x+beta) % N for x in points)
        mask = sum(1 << t for t in range(length) if values[t] == word[t])
        constant = len(set(values)) == 1
        useful = values[0] if constant and values[0] < R else None
        if not constant:
            nonconstant_maximum = max(nonconstant_maximum,mask.bit_count())
            require(4*R*mask.bit_count() <= 3*length, 'finite nonconstant agreement')
        if alpha and useful is not None:
            aliases.append((alpha,beta,useful))
        entries.append((mask,useful))
    count = 0
    optimizers = {}
    for q in (1,2):
        optimizers[str(q)] = 0
        for indices in combinations_with_replacement(range(len(entries)),q):
            mask = 0
            constants = set()
            for index in indices:
                part, useful = entries[index]
                mask |= part
                if useful is not None:
                    constants.add(useful)
            covered = mask.bit_count()
            require(8*R*(10*q-covered) >= (q-len(constants))*length, 'exact finite list deficit')
            if covered == 10*q:
                require(len(constants) == q, 'optimizer constant-restriction rigidity')
                optimizers[str(q)] += 1
            count += 1
    negative_controls = {
        'duplicate':affine_list_coverage(N,R,0,step,word,((0,0),(0,0))),
        'outside_alphabet':affine_list_coverage(N,R,0,step,word,((0,0),(0,2))),
        'nonzero_slope_optimizer':affine_list_coverage(N,R,0,step,word,((20,0),(20,1)))}
    require(negative_controls['duplicate']['covered'] == 10, 'duplicate control')
    require(negative_controls['outside_alphabet']['covered'] == 10, 'outside-alphabet control')
    require(negative_controls['nonzero_slope_optimizer']['covered'] == 20, 'nonunit alias optimizer')
    return dict(N=N,R=R,step=step,length=length,word=word,lists=count,optimizers=optimizers,
                maximum_nonconstant_agreement=nonconstant_maximum,
                nonzero_slope_constant_aliases=aliases,negative_controls=negative_controls,
                scope='One fixed progression only; its length is below the universal theorem threshold')


def check_alphabet_boundary():
    cases = balanced = 0
    for N in (6,8,10,12):
        f = tuple((N//2)*x % N for x in range(N))
        g = tuple((v+N//2) % N for v in f)
        require(len(set(f)) == len(set(g)) == 2, 'obstruction maps are nonconstant')
        for bits in range(1 << N):
            word = tuple((N//2)*((bits >> x)&1) for x in range(N))
            require(all(word[x] in (f[x],g[x]) for x in range(N)), 'subgroup alphabet full cover')
            if bits.bit_count() == N//2:
                agreements = tuple(sum(word[x] == values[x] for x in range(N)) for values in (f,g))
                require(sum(agreements) == N and 2*max(agreements) >= N, 'balanced subgroup obstruction')
                balanced += 1
            cases += 1
    return dict(words=cases,balanced_words=balanced,moduli=(6,8,10,12),
                finding='Two nonconstant affine maps cover every binary subgroup-alphabet word')


def check_sparse_energy():
    rows = []
    for N,m in ((2,1),(3,1),(4,2),(5,2),(6,2),(7,2)):
        cases = 0
        minimum_slack = None
        for prefix in product(range(N),repeat=m):
            values = prefix+(0,)*(N-m)
            for weights in product(range(2),repeat=N):
                # Fixed internally generated integral inputs need no repeated public validation.
                A, B = sum(weights[m:]), sum(weights[:m])
                energy = _energy(N,values,weights)
                lower = Q(A**4,N)+Q(B**4,m*m)
                require(energy >= lower, 'enumerated sparse energy')
                if m*m <= N:
                    require(lower >= Q((A+B)**4,8*N), 'coarse Holder bound')
                if A+B:
                    slack = energy-lower
                    minimum_slack = slack if minimum_slack is None else min(minimum_slack,slack)
                cases += 1
        rows.append(dict(N=N,support_size=m,cases=cases,minimum_nonzero_weight_slack=minimum_slack))
    rational_examples = []
    for N in (1,2,4,6,9):
        support = tuple(x for x in range(N) if x % 3 == 1)
        values = tuple((2*x+1) % N if x in support else 0 for x in range(N))
        for weights in ((Q(0),)*N, (Q(1),)*N,
                        tuple(Q(x+1,(x % 3)+1) for x in range(N))):
            certificate = sparse_energy_certificate(N,values,weights,support)
            rational_examples.append(dict(N=N,support=support,certificate=certificate))
    return dict(binary_weight_cases=sum(row['cases'] for row in rows),binary_rows=rows,
                rational_weight_cases=len(rational_examples),rational_examples=rational_examples,
                scope='Finite exact examples, including composite moduli, noninterval and empty supports')


def check_cover_ratios():
    rows = []
    for budget in (Q(0),Q(1,4),Q(1),Q(7,3),Q(10),Q(101,7),Q(1000)):
        R = max(2,ceil_fraction(4*budget))
        ratio = local_cover_ratio(budget,R)
        require(ratio <= Q(5,16) < Q(1,2), 'local cover mass deficit')
        rows.append(dict(Q=budget,R=R,covered_fraction=ratio,required_fraction=Q(1,2),
                         deficit_at_least=Q(1,2)-ratio))
    # Unequal axis lengths and arbitrary cell areas test the two-input sum.
    cells = ((3,5),(7,2),(1,11))
    area = sum(x*y for x,y in cells)
    bound = sum(Q(5,16)*x*y for x,y in cells)
    require(bound == Q(5,16)*area and bound < Q(area,2), 'sum over fibres and cells')
    require(Q(4096,36) > 33, 'prime scale constant')
    require(Q(32768,36) > 897, 'all-moduli scale constant')
    independent_counts = dict(qGamma=8,qDelta=1,QGamma=8,QDelta=1)
    require(independent_counts['qGamma'] <= independent_counts['QGamma'], 'gamma-side count')
    require(independent_counts['qDelta'] <= independent_counts['QDelta'], 'delta-side count')
    return dict(ratios=rows,cell_axes=cells,total_area=area,covered_mass_bound=bound,
                independent_line_cover_counts=independent_counts,
                prime_scale_margin=Q(4096,36)-33,all_moduli_scale_margin=Q(32768,36)-897,
                scope='Algebraic mass accounting only; sample budgets are not the astronomical theorem parameters')


def check_thresholds():
    rows = []
    for N,R in ((16384,2),(32768,2),(65536,4),(131072,8),(1048576,100),(16777216,1000)):
        length = exact_L0(N,R)
        require(length <= N, 'explicit nonvacuity example')
        rows.append(dict(N=N,R=R,L0=length,step_two_order_reaches_L0=N//2 >= length))
    return dict(examples=rows,method='Exact rational logarithm enclosures with certified equal ceilings')


# These literal pins are fixed independently of the manifest read at run time.
# Changing both a snapshot and its manifest still fails the companion checks.
EXPECTED_MANIFEST_SHA256 = '76ce1f54312b2c11c549d2c44449e5fa8523671ddbd74620e630ee27a6c80f68'
EXPECTED_SOURCES = [{'bytes': 15504,
  'canonical_base64_sha256': 'dadc947fadc5d912095cbd58adf10d6565de7b4856cf49cdf7c98789626d3d9d',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': '97113b7afa6925a2dd4b76641eeaeff09597ab6a',
  'kind': 'git_blob',
  'name': 'Definitions.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean',
  'sha256': '17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean'},
 {'bytes': 24924,
  'canonical_base64_sha256': '87c759a76c5af16c7f31e60a6c890fc267d0625df5f47d269cd173c453a7ab4a',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': '302e8a223f56dcdabf29f30ca3c80ac62a7adbfc',
  'kind': 'git_blob',
  'name': 'Section10.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean',
  'sha256': '8b63d784485ba8291b614a9153399cae216d2adaf37c9770344521083523cb2d',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean'},
 {'bytes': 20864,
  'canonical_base64_sha256': '5a0a45312addf2b9bbe353db3b2a4d6f9c88fea28a3b5e834ca576fa3c53bfd7',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': '5d91dce37bbca59fc76dfd30ec3a485d72ba583c',
  'kind': 'git_blob',
  'name': 'Sections14_15.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean',
  'sha256': 'cc7782c87e1e6261b744f13b7fd62082efcb1b6b45a24a31e694a915ebe6c13b',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean'},
 {'bytes': 43323,
  'canonical_base64_sha256': '1c9b91e9991683a9028c469772f8321bdd6f12589ba7cdb08d0766014eb7865a',
  'commit': '17f048dfa919de04a1989035a2d680ec0865c774',
  'git_blob_sha1': 'c5c7d2bee91bc589de1d3082429f7ee3597e99f9',
  'kind': 'git_blob',
  'name': 'Section16.lean',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean',
  'sha256': 'be20dcf52ba6cb0bc54a03c194ad9b64f486562be032eccf788f14e97e1e65ed',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean'},
 {'archive_bytes': 517479,
  'archive_git_blob_sha1': '807facdac4171f57887a5d5b8affe2427a610a4f',
  'archive_member': 'ramsey_branch_complexity/article.tex',
  'archive_member_bytes': 82816,
  'archive_member_sha256': '792866e778a4bba567913d9961ad0948b1409457e4b989343a0db70993beba6a',
  'archive_sha256': '0282f4e9a073a71e4ebe58c9e37a68c2daa3bb7af5a87b0f6773df3a264e10de',
  'bytes': 82816,
  'canonical_base64_sha256': '2c51a963d73f8adf88eff62ebcfcb6fedd1141a850dc4d96ebdd8364820a9e98',
  'commit': '8c40adc24df2e6f338cea728887772aead4bf144',
  'kind': 'archive_member',
  'name': 'source50_article.tex',
  'repository': 'VladimirReshetnikov/ProveIt',
  'repository_path': 'docs/incoming/ramsey_branch_cover_obstructions.zip',
  'sha256': '792866e778a4bba567913d9961ad0948b1409457e4b989343a0db70993beba6a',
  'url': 'https://github.com/VladimirReshetnikov/ProveIt/blob/8c40adc24df2e6f338cea728887772aead4bf144/docs/incoming/ramsey_branch_cover_obstructions.zip'}]


def _read_bounded_regular(path, limit):
    if (os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW')
            or not hasattr(os, 'O_DIRECTORY') or os.open not in os.supports_dir_fd):
        raise RuntimeError('POSIX no-follow source reads are required')
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts, 'absolute provenance path required')
    parent = os.open('/',os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    descriptor = None
    identity = lambda info: (info.st_dev,info.st_ino,info.st_mode,info.st_nlink,
                             info.st_size,info.st_mtime_ns,info.st_ctime_ns)
    try:
        for component in path.parts[1:-1]:
            child = os.open(component,os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,dir_fd=parent)
            os.close(parent)
            parent = child
        before = os.stat(path.name,dir_fd=parent,follow_symlinks=False)
        require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1 and before.st_size <= limit,
                'provenance path must be a bounded, ordinary single-link file')
        descriptor = os.open(path.name,os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,dir_fd=parent)
        opened = os.fstat(descriptor)
        require(identity(before) == identity(opened), 'provenance file changed before opening')
        data = bytearray()
        while len(data) <= limit:
            block = os.read(descriptor,min(65536,limit+1-len(data)))
            if not block:
                break
            data.extend(block)
        require(len(data) <= limit, 'provenance source exceeds byte budget')
        require(identity(opened) == identity(os.fstat(descriptor)) == identity(
                    os.stat(path.name,dir_fd=parent,follow_symlinks=False)),
                'provenance file changed during reading')
        return bytes(data)
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.close(parent)


def check_sources():
    data = _read_bounded_regular(ROOT/'provenance/source_manifest.json',32768)
    require(hashlib.sha256(data).hexdigest() == EXPECTED_MANIFEST_SHA256,
            'pinned manifest bytes or identity changed')
    require(json.loads(data) == EXPECTED_SOURCES, 'pinned source metadata changed')
    for row in EXPECTED_SOURCES:
        raw = _read_bounded_regular(ROOT/'provenance/sources'/row['name'], 1 << 20)
        require(len(raw) == row['bytes'] and hashlib.sha256(raw).hexdigest() == row['sha256'],
                'pinned raw source bytes changed')
        encoded = base64.b64encode(raw)
        require(hashlib.sha256(encoded).hexdigest() == row['canonical_base64_sha256'],
                'canonical RFC4648 base64 hash changed')
        require(base64.b64decode(encoded,validate=True) == raw, 'canonical base64 round trip')
        if row['kind'] == 'git_blob':
            blob = b'blob '+str(len(raw)).encode('ascii')+b'\0'+raw
            require(hashlib.sha1(blob).hexdigest() == row['git_blob_sha1'], 'pinned Git blob changed')
    return dict(snapshots=len(EXPECTED_SOURCES),raw_sha256=True,canonical_base64_sha256=True,
                raw_git_blob_hashes=4,manifest_sha256=EXPECTED_MANIFEST_SHA256,
                boundary='Canonical base64 is a derived representation, not an original transport receipt. External archives and archive membership are not reverified offline.')


def serialized(value):
    if type(value) is Q:
        return str(value)
    if type(value) is dict:
        return {key:serialized(item) for key,item in value.items()}
    if type(value) in (tuple,list):
        return [serialized(item) for item in value]
    if type(value) in (str,int,bool) or value is None:
        return value
    raise ValueError('unsupported JSON diagnostic value')


def run_all():
    return serialized(dict(status='PASS',report=286,
        scope='Fixed finite exact diagnostics only; no astronomical universal word or Lean certificate is computed.',
        cosets=check_cosets(),prefixes=check_prefixes(),tails=check_tails(),
        lists=check_list_example(),alphabet_boundary=check_alphabet_boundary(),
        sparse_energy=check_sparse_energy(),holder_identity=check_holder_identity(),
        family_energy=check_family_energy(),named_identities=check_named_identities(),
        general_dimensions=check_general_dimensions(),gamma_one_boundary=check_gamma_one_boundary(),
        cover_ratios=check_cover_ratios(),thresholds=check_thresholds(),sources=check_sources()))


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if type(argv) not in (tuple,list) or argv:
        raise SystemExit('No command-line parameters are accepted; workloads are fixed and bounded.')
    print(json.dumps(run_all(),indent=2,sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
