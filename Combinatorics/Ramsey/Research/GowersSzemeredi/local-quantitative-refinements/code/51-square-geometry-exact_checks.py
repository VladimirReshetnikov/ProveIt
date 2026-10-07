#!/usr/bin/env python3
"""Bounded exact diagnostics for Report279: obstruction and actual-selection repair.
No full-budget numerical witness or new Lean verification is claimed.

Only standard-library integer arithmetic is used. Huge mathematical constants
are expression strings; exponent/log comparisons never evaluate those powers.
This program writes nothing. Its deterministic JSON is identical under -O.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import importlib.util
import json
from math import isqrt
from pathlib import Path
import re

ROOT = Path(__file__).absolute().parents[1]
MAX_MODULUS = 8192
MAX_LENGTH = 128
MAX_COVER_LENGTH = 64
MAX_RESIDUE_LENGTH = 32
MAX_CONVOLUTION_MODULUS = 31
MAX_ORDER = 8
MAX_SOURCE_SNAPSHOT_BYTES = 1024 * 1024
MAX_EXPONENT = 10_000_000
MAX_RECTIFICATION_PRIME = 43
MAX_FINAL_COVER_LENGTH = 32


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bounded(value, name, minimum, maximum):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f'{name} must be an integer in [{minimum}, {maximum}]')
    return value


def pow2_small(exponent):
    """The only evaluator of powers of two: at most 32 bits, including sign."""
    bounded(exponent, 'small exponent', 0, 30)
    return 1 << exponent


def symbolic_constants():
    # Deliberately opaque text: no eval, exponentiation, Fraction or giant N.
    return dict(K='2^762', q='2^763+1', theta1_lower='2^(-7995833)',
        d0='2^(-7995833)/(64*pi)', u0='2^(-15991666)/(16*q)',
        w='2^(-11*q)', r='u0*w/4', cP='d0/2', k0='2^1394',
        c0='2^(-2532*k0-1)', z0='2^(-2531*k0-1394)',
        beta0='2^(-13*2^9437184)', beta1='2^(-13*2^7340032)',
        f0='2^(-1892)', W0='2^2951', N='an unspecified sufficiently large prime',
        upstream_gamma='beta*f*g/4 = 2^(-386)*alpha^1856/2^(13*section13Q(alpha))')


def exponent_diagnostics():
    t = 1882 + 763 * 10477
    require(t == 7_995_833, 'theta1 exponent')
    identities = dict(t=t, two_t_plus_770=2*t+770,
        theta_lower=59+4*176, theta_upper=59+3*176,
        k0_from_section13=114+4*320, k0_from_section10=74+10*132,
        c0_multiplier=228+4*576, z0_multiplier=155+132*18,
        Q_lower_log2=1048576+3*2097152, Q_upper_log2=1048576+4*2097152,
        f0_exponent=100+4*448, W0_exponent=135+4*704,
        complete_square_binary_exponent=100+284+2,complete_square_alpha_exponent=448+1408)
    expected = dict(t=7995833, two_t_plus_770=15992436,
        theta_lower=763, theta_upper=587, k0_from_section13=1394,
        k0_from_section10=1394, c0_multiplier=2532, z0_multiplier=2531,
        Q_lower_log2=7340032, Q_upper_log2=9437184,
        f0_exponent=1892, W0_exponent=2951,
        complete_square_binary_exponent=386,complete_square_alpha_exponent=1856)
    require(identities == expected, 'uniform exponent identity')
    for value in identities.values():
        bounded(value, 'identity value', 0, 2*MAX_EXPONENT)
    # q=2^763+1 < 2^764 because 1<2^763, checked as exponent order.
    require(0 < 763 < 764, 'q power order')
    # 11q < 16*2^764 = 2^768, without constructing q.
    require(11 < pow2_small(4) and 764+4 == 768, '11q upper bound')
    require(2*t+770 < pow2_small(25), 'small exponent margin')
    # 2^25+2^768 < 2*2^768 = 2^769.
    require(25 < 768 and 768+1 == 769, 'exponent sum bound')
    # 2^769 < 13*2^7340032 since 769<7340032 and 1<13.
    require(769 < identities['Q_lower_log2'] and 1 < 13, 'beta1 versus r')
    # Lambda(alpha^32/16): 37+4*(11/2)=59 and 32*(11/2)=176.
    require(2*37+4*11 == 2*59 and 32*11 == 2*176, 'lambda exponent')
    return dict(integer_identities=identities,
        symbolic_constants=symbolic_constants(),
        decisive_chain=['q < 2^764', '11*q < 2^768',
            '2*t+770+11*q < 2^769', 'r > 2^(-2^769) > beta1'],
        evaluated_power_of_two_exponents=[4, 25],
        scope='Exponent arithmetic only; positivity, real-power monotonicity and the prime threshold are proved in the article')


def progression(modulus, start, step, length):
    bounded(modulus, 'modulus', 2, MAX_MODULUS)
    bounded(start, 'start', 0, modulus-1)
    bounded(step, 'step', 1, modulus-1)
    bounded(length, 'length', 1, min(modulus, MAX_LENGTH))
    values = tuple((start+j*step) % modulus for j in range(length))
    require(len(set(values)) == length, 'progression is not proper')
    return values


def difference_obstruction(modulus, length):
    bounded(length, 'length', 2, 64)
    bounded(modulus, 'modulus', length*length, MAX_MODULUS)
    s = set(progression(modulus, 0, 1, length))
    u = set(progression(modulus, 0, length, length))
    ds = {(x-y) % modulus for x in s for y in s}
    du = {(x-y) % modulus for x in u for y in u}
    common = sorted(ds & du)
    require(common == [0], 'difference obstruction failed')
    # Independent scan of every candidate common nonzero step.
    steps = [d for d in range(1, modulus)
             if any((x+d) % modulus in s for x in s)
             and any((y+d) % modulus in u for y in u)]
    require(not steps, 'a common nonzero two-point step exists')
    return dict(modulus=modulus, length=length, difference_intersection=common,
                scanned_nonzero_steps=modulus-1, common_nonzero_steps=steps)


def geometry_diagnostics():
    f47 = difference_obstruction(47, 5)
    count = 0
    for n in range(2, 17):
        for modulus in (n*n, n*n+1, 2*n*n+1):
            difference_obstruction(modulus, n)
            count += 1
    return dict(F47_geometry_only=f47, additional_cases=count,
                scope='Finite geometric examples only; none is asserted to satisfy the full analytic budgets')


def cover_indices(length, side):
    bounded(length, 'length', 1, MAX_LENGTH)
    bounded(side, 'side', 1, length)
    a, remainder = divmod(length, side)
    blocks = [tuple(range(i*side, (i+1)*side)) for i in range(a)]
    if remainder:
        blocks.append(tuple(range(length-side, length)))
    require(set().union(*map(set, blocks)) == set(range(length)), 'incomplete endpoint cover')
    require(all(len(b) == side for b in blocks), 'wrong block length')
    require(sum(map(len, blocks)) == side*((length+side-1)//side), 'wrong cover mass')
    require(sum(map(len, blocks)) < 2*length, 'endpoint cover exceeds mass bound')
    return tuple(blocks)


def residue_cover(length, stride, side):
    bounded(length, 'length', 1, MAX_COVER_LENGTH)
    bounded(stride, 'stride', 1, length)
    bounded(side, 'side', 1, length//stride)
    chains = [tuple(range(residue, length, stride)) for residue in range(stride)]
    blocks = tuple(tuple(chain[i] for i in block) for chain in chains
                   for block in cover_indices(len(chain), side))
    require(set().union(*map(set, blocks)) == set(range(length)), 'incomplete residue cover')
    require(all(len(block) == side for block in blocks), 'wrong residue block length')
    require(all(all(b[i+1]-b[i] == stride for i in range(side-1)) for b in blocks), 'wrong stride')
    require(len(blocks)*side < 2*length, 'residue cover exceeds mass bound')
    return blocks


def cover_diagnostics():
    interval_cases = residue_cases = weighted_cases = 0
    for n in range(1, MAX_COVER_LENGTH+1):
        for k in range(1, n+1):
            cover_indices(n, k); interval_cases += 1
    for length in range(1, MAX_RESIDUE_LENGTH+1):
        for stride in range(1, length+1):
            for side in range(1, length//stride+1):
                sb = residue_cover(length, stride, side); residue_cases += 1
                for height in sorted({side, side+1, 2*side+1}):
                    ub = cover_indices(height, side)
                    area = len(sb)*len(ub)*side*side
                    require(area < 4*length*height, 'product cover area bound')
                    for corners_only in (False, True):
                        weights = {(x,y): (int(x in (0,length-1) and y in (0,height-1))
                                   if corners_only else (17*x+23*y+x*y) % 7)
                                   for x in range(length) for y in range(height)}
                        mass = sum(weights.values())
                        cells = [sum(weights[x,y] for x in b for y in c) for b in sb for c in ub]
                        require(sum(cells) >= mass, 'cover misses mass')
                        require(max(cells)*4*length*height >= mass*side*side, 'quarter-density bound')
                        weighted_cases += 1
    for size in range(3, MAX_LENGTH+1):
        side = size-1
        corners = {(0,0),(0,size-1),(size-1,0),(size-1,size-1)}
        for x0 in (0,1):
            for y0 in (0,1):
                require(sum(x0<=x<x0+side and y0<=y<y0+side for x,y in corners) == 1,
                        'fixed-step four-corner count')
    for size in range(2, MAX_MODULUS+1):
        side = isqrt(size-1)
        require(side*side <= size-1 < (side+1)*(side+1), 'sqrt floor')
        require(size <= (side+1)*(side+1), 'square-root target')
    return dict(interval_cases=interval_cases, residue_cases=residue_cases,
        weighted_cases=weighted_cases, four_corner_sizes=[3,MAX_LENGTH],
        square_root_target_sizes=[2,MAX_MODULUS],
        scope='Contained endpoint covers; distinct from the upstream padded-cover construction')


def prime_small(modulus):
    bounded(modulus, 'small prime modulus', 2, MAX_CONVOLUTION_MODULUS)
    if any(modulus % d == 0 for d in range(2, isqrt(modulus)+1)):
        raise ValueError('small prime modulus required')
    return modulus


def cyclic_sum_counts(modulus, width, order):
    bounded(modulus, 'convolution modulus', 2, MAX_CONVOLUTION_MODULUS)
    bounded(width, 'width', 1, modulus)
    bounded(order, 'order', 1, MAX_ORDER)
    counts = [1]+[0]*(modulus-1)
    for _ in range(order):
        counts = [sum(counts[(s-x) % modulus] for x in range(width)) for s in range(modulus)]
    require(sum(counts) == width**order, 'convolution normalization')
    return tuple(counts)


def cyclotomic_reduce(coefficients):
    if type(coefficients) not in (tuple, list):
        raise ValueError('bounded coefficient list required')
    modulus = prime_small(len(coefficients))
    if any(type(x) is not int or abs(x).bit_length() > 128 for x in coefficients):
        raise ValueError('coefficients must be integers of at most 128 bits')
    # Modulo Phi_p(X)=1+...+X^(p-1), after first reducing modulo X^p-1.
    return tuple(coefficients[i]-coefficients[-1] for i in range(modulus-1))


def fourier_polynomial(modulus, width, frequency):
    prime_small(modulus)
    bounded(width, 'width', 1, modulus)
    bounded(frequency, 'frequency', 0, modulus-1)
    coefficients = [0]*modulus
    for x in range(width):
        coefficients[(-frequency*x) % modulus] += modulus
    return cyclotomic_reduce(coefficients)


def strip_diagnostics():
    arrangement_cases = fourier_cases = 0
    for modulus in (2,3,5,7,11,13,17,19,23,29,31):
        for width in sorted({1, max(1,modulus//8), modulus//2, modulus}):
            rho = cyclic_sum_counts(modulus, width, 8)
            energy = sum(value*value for value in rho)
            arrangement = modulus**16*energy
            require(modulus*energy >= width**16, 'Cauchy-Schwarz energy bound')
            # C(h) >= alpha^16 N^31, clearing alpha=b/N exactly.
            require(arrangement >= width**16*modulus**15, 'arrangement N exponent')
            arrangement_cases += 1
            total = [0]*(modulus-1)
            for frequency in range(modulus):
                coefficients = fourier_polynomial(modulus, width, frequency)
                raw_norm = [0]*modulus
                for i, a in enumerate(coefficients):
                    for j, b in enumerate(coefficients):
                        raw_norm[(i-j) % modulus] += a*b
                norm = cyclotomic_reduce(raw_norm)
                total = [a+b for a,b in zip(total,norm)]
                fourier_cases += 1
            require(fourier_polynomial(modulus,width,0) == (modulus*width,)+(0,)*(modulus-2),
                    'zero Fourier coefficient is not N*b')
            require(tuple(total) == (modulus**3*width,)+(0,)*(modulus-2),
                    'unnormalized Parseval is not N^3*b')
    return dict(arrangement_cases=arrangement_cases, exact_fourier_coefficients=fourier_cases,
        arrangement_formula='C(h)=N^16*sum_s rho(s)^2 >= b^16*N^15',
        zero_frequency='N*b', unnormalized_parseval='sum_xi |F(xi)|^2=N^3*b',
        fourier_method='Exact arithmetic in Z[X]/(1+X+...+X^(p-1)) for small primes',
        scope='Finite count and normalization regressions, not a numerical proof of the real sine bound')


def rectification_prime(modulus):
    bounded(modulus, 'rectification prime', 2, MAX_RECTIFICATION_PRIME)
    if any(modulus % d == 0 for d in range(2, isqrt(modulus)+1)):
        raise ValueError('prime modulus required')
    return modulus


def rectify_short_carrier(modulus, parent_length, indices):
    rectification_prime(modulus)
    bounded(parent_length, 'parent length', 2, (modulus+1)//2)
    if type(indices) not in (tuple,list) or not 2 <= len(indices) <= parent_length:
        raise ValueError('bounded proper progression of at least two terms required')
    for x in indices:
        bounded(x, 'parent index', 0, parent_length-1)
    if len(set(indices)) != len(indices):
        raise ValueError('proper indexed progression required')
    differences = [indices[i+1]-indices[i] for i in range(len(indices)-1)]
    if len({d % modulus for d in differences}) != 1:
        raise ValueError('one modular progression step required')
    require(len(set(differences)) == 1, 'short-carrier rectification failed')
    signed_stride = differences[0]
    require(signed_stride != 0, 'zero lifted step')
    stride = abs(signed_stride)
    oriented = tuple(indices if signed_stride > 0 else reversed(indices))
    require(stride*(len(indices)-1) <= parent_length-1, 'rectified span exceeds parent')
    return dict(stride=stride, reversed=signed_stride < 0, indices=oriented)


def balanced_chain_blocks(length, cap):
    bounded(cap, 'balanced cap', 2, MAX_COVER_LENGTH)
    bounded(length, 'chain length', cap-1, MAX_LENGTH)
    count = (length+cap-1)//cap
    low,remainder = divmod(length,count)
    sizes = [low+1]*remainder+[low]*(count-remainder)
    require(sum(sizes) == length, 'balanced block mass')
    require(min(sizes) >= (cap+1)//2 and max(sizes) <= cap, 'balanced block range')
    offset=0;blocks=[]
    for size in sizes:
        blocks.append(tuple(range(offset,offset+size)));offset+=size
    return tuple(blocks)


def aligned_parent_partition(total, stride, column_length):
    bounded(total, 'height length', 2, MAX_COVER_LENGTH)
    bounded(stride, 'parent stride', 1, total-1)
    bounded(column_length, 'column length', 2, MAX_COVER_LENGTH)
    if stride*(column_length-1) >= total:
        raise ValueError('strict integer span budget required')
    chains = [tuple(range(r,total,stride)) for r in range(stride)]
    blocks = tuple(tuple(chain[i] for i in block) for chain in chains
                   for block in balanced_chain_blocks(len(chain),column_length))
    flattened=[x for block in blocks for x in block]
    require(len(flattened) == total and set(flattened) == set(range(total)), 'parents do not partition')
    require(all((column_length+1)//2 <= len(b) <= column_length for b in blocks), 'parent length range')
    require(all(all(b[i+1]-b[i] == stride for i in range(len(b)-1)) for b in blocks), 'parent step')
    return blocks


def weighted_parent_choice(weights, blocks):
    if type(weights) not in (tuple,list) or not 2 <= len(weights) <= MAX_COVER_LENGTH:
        raise ValueError('bounded weight vector required')
    total=len(weights)
    for value in weights:
        bounded(value, 'integer weight', 0, MAX_LENGTH)
    if type(blocks) not in (tuple,list) or not 1 <= len(blocks) <= total:
        raise ValueError('bounded partition blocks required')
    for block in blocks:
        if type(block) not in (tuple,list) or not 1 <= len(block) <= total:
            raise ValueError('nonempty bounded partition block required')
        for x in block:
            bounded(x, 'partition index', 0, total-1)
    flattened=[x for block in blocks for x in block]
    if len(flattened) != total or set(flattened) != set(range(total)):
        raise ValueError('disjoint exact partition required')
    mass=sum(weights)
    candidates=[i for i,block in enumerate(blocks) if sum(weights[x] for x in block)*total >= mass*len(block)]
    require(bool(candidates), 'weighted density retention failed')
    return candidates[0]


def ambient_phase_coefficients(modulus, start, step, offset, a0, a1, b0, b1):
    rectification_prime(modulus)
    bounded(step, 'phase step', 1, modulus-1)
    for value in (start,offset,a0,a1,b0,b1):
        bounded(value, 'field representative', 0, modulus-1)
    inverse=next(i for i in range(1,modulus) if step*i % modulus == 1)
    return ((a0-a1*(start+offset)*inverse) % modulus,
            (b0-b1*(start+offset)*inverse) % modulus,
            a1*inverse % modulus,b1*inverse % modulus)


def constructive_diagnostics():
    prefixes=partitions=weighted=final_covers=phase_cases=short_cell_cases=0
    for p in range(2,MAX_RECTIFICATION_PRIME+1):
        if any(p % d == 0 for d in range(2,isqrt(p)+1)):
            continue
        for n in range(2,(p+1)//2+1):
            for start in range(n):
                for step in range(1,p):
                    indices=[start]
                    for j in range(1,n):
                        x=(start+j*step) % p
                        if x >= n:
                            break
                        indices.append(x)
                        result=rectify_short_carrier(p,n,indices)
                        require(result['stride']*(len(indices)-1) <= n-1,'prefix span')
                        prefixes+=1
    # A proper contained carrier beyond the shortness threshold need not rectify.
    counterexample=[0,3,1]
    require((3-0) % 5 == (1-3) % 5 and min(3,2)*2 > 3, 'F5 threshold example')
    for total in range(2,MAX_COVER_LENGTH+1):
        for stride in range(1,total):
            for length in range(2,(total-1)//stride+2):
                blocks=aligned_parent_partition(total,stride,length);partitions+=1
                for mode in range(3):
                    weights=tuple(0 if mode==0 else length*int(x in (0,total-1)) if mode==1
                                  else (17*x+x*x) % (length+1) for x in range(total))
                    choice=weighted_parent_choice(weights,blocks)
                    block=blocks[choice]
                    require(sum(weights[x] for x in block)*total >= sum(weights)*len(block),
                            'selected parent loses normalized density')
                    weighted+=1
    for length in range(2,MAX_FINAL_COVER_LENGTH+1):
        for m in range(2,length+1):
            side=m-1
            for stride in range(1,(length-1)//side+1):
                require(stride*side <= length-1 and isqrt(m) <= side,'side M-1 fit')
                sb=residue_cover(length,stride,side);ub=cover_indices(m,side)
                require(len(sb)*len(ub)*side*side < 4*length*m,'final cover capacity')
                weights={(x,y):(5*x+3*y+x*y) % 7 for x in range(length) for y in range(m)}
                mass=sum(weights.values())
                best=max(sum(weights[x,y] for x in b for y in c) for b in sb for c in ub)
                require(best*4*length*m >= mass*side*side,'final quarter-density bound')
                final_covers+=1
    for length in range(3,MAX_MODULUS+1):
        require(((length+1)//2)**2 >= length,'ceiling half-length square bound')
    for m in range(3,MAX_COVER_LENGTH+1):
        for n in (m,m+1):
            require(2*(n-1) <= 2*m < m*m,'selected-cell shortness')
            short_cell_cases+=1
    for p in (3,5,7,11):
        for m in range(2,min(p,5)+1):
            for start in (0,p-1):
                for step in range(1,p):
                    for offset in (0,p-1):
                        a0,a1,b0,b1=(2 % p,3 % p,4 % p,5 % p)
                        coefficients=ambient_phase_coefficients(p,start,step,offset,a0,a1,b0,b1)
                        reversed_coefficients=ambient_phase_coefficients(p,(start+(m-1)*step) % p,
                            (-step) % p,offset,(a0+(m-1)*a1) % p,(-a1) % p,
                            (b0+(m-1)*b1) % p,(-b1) % p)
                        require(coefficients == reversed_coefficients,'phase changes under reversal')
                        c0,cx,cz,cxz=coefficients
                        for j in range(m):
                            z=(start+j*step+offset) % p
                            for x in range(p):
                                require(((a0+a1*j)+(b0+b1*j)*x) % p ==
                                        (c0+cx*x+cz*z+cxz*x*z) % p,'original-coordinate phase formula')
                        phase_cases+=1
    require(2*135+14 == 284 and 2*704 == 1408 and 284+1 == 285,
            'coefficient and square exponent arithmetic')
    require(285+100 == 385 and 1408+448 == 1856,'composed exponent arithmetic')
    return dict(short_progression_prefixes=prefixes,aligned_parent_partitions=partitions,
        weighted_density_retention_cases=weighted,final_side_m_minus_one_covers=final_covers,
        original_coordinate_phase_cases=phase_cases,selected_cell_shortness_cases=short_cell_cases,
        ceiling_square_lengths=[3,MAX_MODULUS],shortness_counterexample=dict(modulus=5,parent_length=4,indices=counterexample),
        scope='Bounded geometric and phase diagnostics. The all-scale analytic coefficient API is imported in the article, not simulated or newly Lean-verified here')


def verify_source_bytes(raw, row):
    if type(raw) is not bytes or len(raw) > MAX_SOURCE_SNAPSHOT_BYTES:
        raise ValueError('bounded source bytes required')
    keys = {'file','repository_path','commit','bytes','sha256','git_blob','verified_url'}
    if type(row) is not dict or set(row) != keys:
        raise ValueError('exact curated source record required')
    if type(row['file']) is not str or not re.fullmatch(r'sources/[A-Za-z0-9_]+\.lean',row['file']):
        raise ValueError('ordinary selected Lean snapshot name required')
    expected_path = 'Combinatorics/Ramsey/Lean/GowersSzemeredi/'+row['file'].split('/')[-1]
    if row['repository_path'] != expected_path:
        raise ValueError('repository path does not match the selected snapshot')
    for key,width in (('commit',40),('git_blob',40),('sha256',64)):
        if type(row[key]) is not str or not re.fullmatch('[0-9a-f]{'+str(width)+'}',row[key]):
            raise ValueError('invalid '+key)
    expected_url = 'https://github.com/VladimirReshetnikov/ProveIt/blob/'+row['commit']+'/'+expected_path
    if row['verified_url'] != expected_url:
        raise ValueError('pinned verified URL does not match repository path and commit')
    bounded(row['bytes'], 'source size', 1, MAX_SOURCE_SNAPSHOT_BYTES)
    git_blob = hashlib.sha1(b'blob '+str(len(raw)).encode('ascii')+b'\0'+raw).hexdigest()
    require(len(raw) == row['bytes'], 'source byte length differs')
    require(git_blob == row['git_blob'], 'Git blob mismatch')
    require(hashlib.sha256(raw).hexdigest() == row['sha256'], 'SHA256 mismatch')
    return git_blob


def validate_source_manifest(manifest, files):
    if type(manifest) is not dict or set(manifest) != {'schema','scope','sources','unchanged_at_later_pins'}:
        raise ValueError('exact curated manifest schema required')
    if manifest['schema'] != 'report279-curated-sources-v1' or type(manifest['scope']) is not str:
        raise ValueError('unsupported curated manifest schema')
    rows = manifest['sources']; later = manifest['unchanged_at_later_pins']
    if type(rows) is not list or not 1 <= len(rows) <= 64 or type(later) is not list or len(later) > 64:
        raise ValueError('bounded curated source record lists required')
    names = set()
    for row in rows:
        if type(row) is not dict or type(row.get('file')) is not str:
            raise ValueError('curated source row required')
        name = 'provenance/'+row['file']
        require(name in files, 'curated snapshot missing')
        verify_source_bytes(files[name],row)
        require(name not in names, 'duplicate curated snapshot row')
        names.add(name)
    require(names == {name for name in files if name.startswith('provenance/sources/')},
            'curated source manifest/file inventory differs')
    later_keys = set()
    for row in later:
        if type(row) is not dict or type(row.get('file')) is not str:
            raise ValueError('curated later-pin row required')
        name = 'provenance/'+row['file']
        require(name in names, 'later-pin row lacks a selected snapshot')
        verify_source_bytes(files[name],row)
        key = (row['file'],row['commit'])
        require(key not in later_keys, 'duplicate later-pin row')
        later_keys.add(key)
    return len(rows),len(later)


def source_diagnostics():
    spec = importlib.util.spec_from_file_location('report279_build', ROOT/'build.py')
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    files = module.verified_snapshot()
    manifest = json.loads(files['provenance/source_manifest.json'])
    count,later = validate_source_manifest(manifest,files)
    return dict(verified_lean_snapshots=count, unchanged_later_pin_checks=later,
        provenance_files=sum(name.startswith('provenance/') for name in files),
        pins=sorted({row['commit'] for row in manifest['sources']+manifest['unchanged_at_later_pins']}),
        scope='Curated source byte identity, SHA256, Git blob and pinned URL checks only; no Lean compilation or axiom audit')


def diagnostics():
    return dict(status='passed', report=279, exponents=exponent_diagnostics(),
        geometry=geometry_diagnostics(), covers=cover_diagnostics(), strip=strip_diagnostics(),
        constructive=constructive_diagnostics(),
        sources=source_diagnostics(),
        caps=dict(modulus=MAX_MODULUS, geometry_length=64, interval_length=MAX_COVER_LENGTH,
                  residue_length=MAX_RESIDUE_LENGTH, convolution_modulus=MAX_CONVOLUTION_MODULUS,
                  convolution_order=MAX_ORDER, evaluated_power_of_two_exponent=30,
                  rectification_prime=MAX_RECTIFICATION_PRIME,aligned_parent_length=MAX_COVER_LENGTH,
                  final_constructive_cover_length=MAX_FINAL_COVER_LENGTH),
        excluded=['No astronomical constant evaluated', 'No full-budget numerical witness',
                  'No Lean proof, compilation or whole-project audit'])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    print(json.dumps(diagnostics(), indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
