#!/usr/bin/env python3
"""Bounded exact Report281 diagnostics, not a Lean proof or huge-N evaluation."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import re

ROOT = Path(__file__).absolute().parents[1]
MAX_COEFFICIENT = 10000000
MAX_RATIONAL_PART = 65536
MAX_MODULUS = 257
MAX_LENGTH = 512
MAX_SOURCE_SNAPSHOT_BYTES = 2 * 1024 * 1024
MAX_SOURCE_RECORDS = 64


def require(condition, message):
    if type(condition) is not bool or not condition:
        raise RuntimeError(message)


def bounded(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(name + ' outside bounded integer range')
    return value


def pow2_small(exponent):
    """The only evaluated binary powers; every astronomical exponent stays symbolic."""
    bounded(exponent, 'small binary exponent', 0, 30)
    return 1 << exponent


def affine(value):
    """Exact coefficients (p,q) of p+q*h; h is symbolic and nonnegative."""
    if type(value) is not tuple or len(value) != 2:
        raise ValueError('two integer coefficients required')
    for item in value:
        bounded(item, 'affine coefficient', -MAX_COEFFICIENT, MAX_COEFFICIENT)
    return value


def add(left, right):
    affine(left); affine(right)
    return affine((left[0] + right[0], left[1] + right[1]))


def scale(multiplier, value):
    bounded(multiplier, 'coefficient multiplier', -2097152, 2097152)
    affine(value)
    return affine((multiplier * value[0], multiplier * value[1]))


def strict_for_nonnegative_h(left, right):
    """Certify left(h)<right(h) for every h>=0 using coefficient comparison."""
    affine(left); affine(right)
    return left[0] < right[0] and left[1] <= right[1]


def exact_identities():
    theta = (-59, -176)
    t = add((-1882, 0), scale(10477, theta))
    b = add((1882, 0), scale(-10479, theta))
    Q = (1048576, 2097152)
    K = (114, 320)
    f = (-100, -448); g = (-284, -1408)
    fg = add(f, g); gamma_without_beta = add(fg, (-2, 0))
    inv_u_without_q = add((4, 0), scale(-2, t))
    recurrence_intermediate = add(inv_u_without_q, (21, 2))
    recurrence_final = add(recurrence_intermediate, b)
    values = dict(theta=theta, t=t, b=b, Q=Q, K=K, f=f, g=g, fg=fg,
        gamma_without_beta=gamma_without_beta,
        half_fg=add(fg, (-1, 0)), twice_gamma_without_beta=add(gamma_without_beta, (1, 0)),
        tb=add(t,b), minus_twice_theta=scale(-2,theta),
        b_over_half_Q=add(b,scale(-1,add(Q,(-1,0)))),
        inverse_u_without_q=inv_u_without_q,
        recurrence_intermediate=recurrence_intermediate, recurrence_final=recurrence_final,
        fgK=add(fg,K), C_plus_3_bound=add(K,(10,2)),
        safe_threshold_remainder=add(add(K,(10,2)),scale(-1,gamma_without_beta)))
    require(t == (-620025,-1843952), 't expansion')
    require(b == (620143,1844304), 'b expansion')
    require(values['tb'] == values['minus_twice_theta'], 't*b=theta^-2')
    require(values['half_fg'] == values['twice_gamma_without_beta'], 'beta*f*g/2=2*gamma')
    require(gamma_without_beta == (-386,-1856), 'gamma exponent')
    require(values['b_over_half_Q'] == (-428432,-252848), 'b/(Q/2) exponent')
    require(inv_u_without_q == (1240054,3687904), 'reciprocal u exponent')
    require(recurrence_intermediate == (1240075,3687906), 'intermediate recurrence exponent')
    require(recurrence_final == (1860218,5532210), 'final recurrence exponent')
    require(values['fgK'] == (-270,-1536), 'coefficient loss exponent')
    require(values['safe_threshold_remainder'] == (510,2178), 'double-log remainder')
    return values


def threshold_certificates():
    """Finite exact algebra used by the written all-h inequalities; no sampling of h."""
    checks = {
        'D_plus_2_below_2^21_times_1_plus_h': strict_for_nonnegative_h((620036,1843952),(pow2_small(21),pow2_small(21))),
        'recurrence_prefactor_below_2^21_times_1_plus_h': strict_for_nonnegative_h((620043,1843984),(pow2_small(21),pow2_small(21))),
        'recurrence_remainder_below_2^23_times_1_plus_h': strict_for_nonnegative_h((1860218,5532210),(pow2_small(23),pow2_small(23))),
        'recurrence_remainder_exponent_below_Q': strict_for_nonnegative_h((23,2),(1048576,2097152)),
        'safe_remainder_below_2^12_times_1_plus_h': strict_for_nonnegative_h((510,2178),(pow2_small(12),pow2_small(12))),
        'safe_remainder_exponent_below_Q': strict_for_nonnegative_h((12,2),(1048576,2097152)),
        'C_plus_3_polynomial_below_2^10_times_1_plus_h': strict_for_nonnegative_h((232,576),(pow2_small(10),pow2_small(10))),
        'C_dominates_D_polynomial': 114 > 21 and 228 > 1 and 576 > 1,
        'q_floor_at_least_512': 620143 >= 9 and pow2_small(9) == 512,
        'T2_constant_and_q_budget': 321+1-11 == 311 and 311 <= 512,
        'H_ceiling_strict_binary_bound': 160+2+1 == 163 and 163 < pow2_small(8),
        'Xstar_width_dominated': 284 > 8 and pow2_small(8) > 135 and 1408//2 == 704,
        'rounded_zeta_loss': 155+4*18 == 227 and 32*18 == 576 and 227+1 == 228,
        'term6_rescaled_strictness': strict_for_nonnegative_h((5,1),(12,4)),
        'recurrence_gap': 12//2+1 == 7 and 7 < 13,
        'coefficient_log_factor': 1536//2 == 768 and 576 <= 228*768,
        'coefficient_uniform_loss': 284 > 270 and 384 > 270 and 1+1+228 == 230 and 230 < 256 and 270-8 == 262 and 262 > 0,
        'mass_coefficient': 135+2 == 137,
        'clean_triple_at_x16': 16//2 == 8 and 8 > 1,
    }
    for name, passed in checks.items():
        require(passed, name)
    return dict(checks=checks, count=len(checks),
        interpretation='Exact coefficient certificates supporting the written proof for every h>=0; not a numerical evaluation of its exponential functions',
        symbolic_threshold='ceil((8/c(a0))^(1/gamma(a0)))',
        huge_powers_evaluated=False)


def rational(value, low=0):
    if type(value) is not Fraction:
        raise ValueError('exact Fraction required')
    if (abs(value.numerator) > MAX_RATIONAL_PART or value.denominator > MAX_RATIONAL_PART
            or value < low):
        raise ValueError('rational input outside bounded range')
    return value


def floor_half(value):
    rational(value, 8)
    half = (value.numerator // value.denominator) // 2
    require(Fraction(half) >= value/4, 'natural floor/half lower bound')
    return half


def floor_predecessor(value):
    rational(value, 4)
    length = value.numerator // value.denominator - 1
    require(Fraction(length) >= value/2, 'two-unit loss budget')
    return length


def ceiling_budget(value):
    rational(value, 1)
    m = -(-value.numerator // value.denominator)
    require(1 <= m and value <= m <= value+1 <= 2*value, 'ceiling budget')
    return m


def rounding_diagnostics():
    counts = dict(floor_half=0, floor_predecessor=0, ceiling=0)
    for denominator in range(1,17):
        for numerator in range(8*denominator,64*denominator+1):
            floor_half(Fraction(numerator,denominator)); counts['floor_half'] += 1
        for numerator in range(4*denominator,32*denominator+1):
            floor_predecessor(Fraction(numerator,denominator)); counts['floor_predecessor'] += 1
        for numerator in range(denominator,16*denominator+1):
            ceiling_budget(Fraction(numerator,denominator)); counts['ceiling'] += 1
    return counts



def short_parent_budget(m, parent_length, modulus):
    bounded(m,'rounded short side',3,64)
    bounded(parent_length,'selected parent length',m,m+1)
    bounded(modulus,'short-parent modulus',9,65536)
    if m*m > modulus:
        raise ValueError('square budget m*m<=N required')
    require(2*(parent_length-1) <= 2*m < m*m <= modulus, 'selected short-parent budget')
    return 2*(parent_length-1)


def triple_absorption(value):
    rational(value,16)
    lower=value*value*value*value/2-1
    require(lower >= value*value*value, 'clean triple-exponent absorption')
    return lower


def rectify_progression(modulus, parent_length, start, step, length):
    """Toy normalized carrier {0,...,r-1}; prove constant signed integer strides."""
    bounded(modulus,'modulus',3,MAX_MODULUS)
    bounded(parent_length,'parent length',2,min(MAX_LENGTH,modulus))
    bounded(start,'start',0,modulus-1); bounded(step,'step',1,modulus-1)
    bounded(length,'length',2,parent_length)
    if 2*(parent_length-1) >= modulus:
        raise ValueError('strict short-carrier hypothesis required')
    points = tuple((start+i*step)%modulus for i in range(length))
    if len(set(points)) != length or any(x >= parent_length for x in points):
        raise ValueError('proper progression inside the short carrier required')
    diffs = tuple(points[i+1]-points[i] for i in range(length-1))
    require(len(set(diffs)) == 1, 'short rectification has constant integer difference')
    oriented = points if diffs[0] > 0 else tuple(reversed(points))
    stride = abs(diffs[0]); span = stride*(length-1)
    require(stride > 0 and span <= parent_length-1, 'rectified stride/span')
    require(tuple(sorted(points)) == oriented, 'reversal preserves carrier and orders it')
    return dict(points=oriented,stride=stride,span=span)


def balanced_sizes(chain_length, column_length):
    bounded(chain_length,'chain length',1,MAX_LENGTH)
    bounded(column_length,'column length',2,64)
    if chain_length < column_length-1:
        raise ValueError('chain must have at least L-1 points')
    blocks = (chain_length+column_length-1)//column_length
    q,r = divmod(chain_length,blocks)
    sizes = (q+1,)*r + (q,)*(blocks-r)
    require(sum(sizes) == chain_length, 'balanced partition covers chain')
    require(min(sizes) >= (column_length+1)//2 and max(sizes) <= column_length,
            'balanced block interval')
    require(max(sizes)-min(sizes) <= 1, 'balanced block sizes')
    return sizes


def aligned_parents(parent_length, column_length, stride):
    bounded(parent_length,'aligned parent length',2,MAX_LENGTH)
    bounded(column_length,'column length',2,min(64,parent_length))
    bounded(stride,'stride',1,parent_length)
    if stride*(column_length-1) >= parent_length:
        raise ValueError('strict indexed span required')
    parents = []
    for residue in range(stride):
        chain = tuple(range(residue,parent_length,stride)); offset = 0
        for size in balanced_sizes(len(chain),column_length):
            parents.append(chain[offset:offset+size]); offset += size
    flattened = tuple(x for parent in parents for x in parent)
    require(len(flattened) == parent_length and set(flattened) == set(range(parent_length)),
            'aligned parents exactly partition the original carrier')
    require(all(all(block[i+1]-block[i] == stride for i in range(len(block)-1)) for block in parents),
            'aligned parents have the same stride')
    return tuple(parents)


def contained_cover(length, side):
    bounded(length,'cover length',1,MAX_LENGTH)
    bounded(side,'cover side',1,length)
    starts = list(range(0,length-side+1,side))
    if starts[-1]+side < length:
        starts.append(length-side)
    blocks = tuple(tuple(range(start,start+side)) for start in starts)
    require(set(x for block in blocks for x in block) == set(range(length)), 'endpoint cover')
    require(len(blocks)*side < 2*length, 'strict capacity below double length')
    require(len(blocks) == (length+side-1)//side, 'cover has ceiling block count')
    return blocks


def square_fit(column_length, parent_length, stride, cell_length):
    bounded(column_length,'column length',2,64)
    bounded(parent_length,'coefficient parent length',2,column_length)
    bounded(cell_length,'cell length',2,parent_length)
    bounded(stride,'second rectified stride',1,column_length)
    if stride*(cell_length-1) > parent_length-1:
        raise ValueError('rectified cell must fit its parent')
    side = cell_length-1
    require(stride*side <= column_length and side <= cell_length, 'common-step square-side fit')
    return side


def contained_square_cover(column_length, cell_length, stride):
    bounded(column_length,'column length',2,64)
    bounded(cell_length,'cell length',2,64)
    bounded(stride,'square stride',1,column_length)
    side = cell_length-1
    if stride*side > column_length:
        raise ValueError('common-step square-side fit required')
    columns = []
    for residue in range(stride):
        chain = tuple(range(residue,column_length,stride))
        for indices in contained_cover(len(chain),side):
            columns.append(tuple(chain[i] for i in indices))
    rows = contained_cover(cell_length,side)
    capacity = len(columns)*len(rows)*side*side
    require(capacity < 4*column_length*cell_length, 'product-cover capacity bound')
    require(set(x for col in columns for x in col) == set(range(column_length)), 'columns covered')
    require(set(y for row in rows for y in row) == set(range(cell_length)), 'rows covered')
    return dict(columns=tuple(columns),rows=rows,side=side,capacity=capacity)


def geometry_diagnostics():
    counts = dict(rectifications=0, balanced_partitions=0, aligned_parents=0,
                  covers=0,square_fits=0,mass_averaging_cases=0,short_parent_budgets=0)
    for m in range(3,65):
        for r in (m,m+1):
            for n in (m*m,m*m+1,m*m+37):
                short_parent_budget(m,r,n); counts['short_parent_budgets'] += 1
    for modulus in (17,31,61):
        for parent in range(2,min(13,(modulus+1)//2)):
            for start in range(parent):
                for stride in range(1,parent):
                    for length in range(2,(parent-1-start)//stride+2):
                        for initial,step in ((start,stride),(start+(length-1)*stride,modulus-stride)):
                            rectify_progression(modulus,parent,initial,step,length)
                            counts['rectifications'] += 1
    for L in range(2,33):
        for n in range(L-1,129):
            balanced_sizes(n,L); counts['balanced_partitions'] += 1
    for n in range(2,65):
        for L in range(2,min(17,n+1)):
            for stride in range(1,min(9,n)):
                if stride*(L-1) < n:
                    aligned_parents(n,L,stride); counts['aligned_parents'] += 1
        for side in range(1,n+1):
            contained_cover(n,side); counts['covers'] += 1
    for L in range(2,33):
        for v in range(2,L+1):
            for M in range(2,v+1):
                for stride in range(1,(v-1)//(M-1)+1):
                    square_fit(L,v,stride,M); counts['square_fits'] += 1
    for L,M,stride in ((7,4,2),(11,3,4),(16,5,3),(25,9,3),(32,16,2)):
        cover = contained_square_cover(L,M,stride); k=cover['side']
        for seed in range(5):
            points={(x,y) for x in range(L) for y in range(M) if (7*x+3*y+seed)%11 < 4}
            masses=[sum((x,y) in points for x in col for y in row)
                    for col in cover['columns'] for row in cover['rows']]
            require(sum(masses) >= len(points),'mass covered without discarding endpoints')
            require(4*L*M*max(masses) >= len(points)*k*k, 'factor-four density retained')
            counts['mass_averaging_cases'] += 1
    return dict(counts=counts,scope='Bounded exact finite models; the article supplies the general geometric proof')


def verify_source_bytes(raw, row):
    if type(raw) is not bytes or not 1 <= len(raw) <= MAX_SOURCE_SNAPSHOT_BYTES:
        raise ValueError('bounded nonempty source bytes required')
    keys={'name','repository_path','commit','url','bytes','sha256','git_blob_sha1','observed_commit','comparison_note'}
    if type(row) is not dict or set(row) != keys:
        raise ValueError('exact curated source record required')
    if type(row['name']) is not str or not re.fullmatch(r'[A-Za-z0-9_]+\.lean',row['name']):
        raise ValueError('ordinary selected Lean filename required')
    path='Combinatorics/Ramsey/Lean/GowersSzemeredi/'+row['name']
    if row['repository_path'] != path:
        raise ValueError('repository path differs from selected filename')
    for key,width in (('commit',40),('observed_commit',40),('git_blob_sha1',40),('sha256',64)):
        if type(row[key]) is not str or not re.fullmatch('[0-9a-f]{'+str(width)+'}',row[key]):
            raise ValueError('invalid '+key)
    url='https://github.com/VladimirReshetnikov/ProveIt/blob/'+row['commit']+'/'+path
    if row['url'] != url:
        raise ValueError('pinned URL differs from repository path and commit')
    if type(row['comparison_note']) is not str or not 1 <= len(row['comparison_note']) <= 4096:
        raise ValueError('bounded comparison note required')
    bounded(row['bytes'],'source size',1,MAX_SOURCE_SNAPSHOT_BYTES)
    blob=hashlib.sha1(b'blob '+str(len(raw)).encode('ascii')+b'\0'+raw).hexdigest()
    require(len(raw) == row['bytes'],'source byte length mismatch')
    require(hashlib.sha256(raw).hexdigest() == row['sha256'],'source SHA256 mismatch')
    require(blob == row['git_blob_sha1'],'source Git blob mismatch')
    return blob


def validate_source_manifest(manifest, files):
    if type(manifest) is not list or not 1 <= len(manifest) <= MAX_SOURCE_RECORDS or type(files) is not dict or len(files) > 128:
        raise ValueError('bounded curated manifest list and file dictionary required')
    if any(type(name) is not str or not 1 <= len(name) <= 1024 for name in files):
        raise ValueError('bounded string file names required')
    names=set()
    for row in manifest:
        if type(row) is not dict or type(row.get('name')) is not str:
            raise ValueError('curated source row required')
        name='provenance/sources/'+row['name']
        require(name in files,'curated source missing')
        verify_source_bytes(files[name],row)
        require(name not in names,'duplicate curated source')
        names.add(name)
    require(names == {name for name in files if name.startswith('provenance/sources/')},
            'source manifest/file inventory mismatch')
    return len(names)


def source_diagnostics():
    spec=importlib.util.spec_from_file_location('report281_build',ROOT/'build.py')
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    files=module.verified_snapshot()
    manifest=json.loads(files['provenance/source_manifest.json'])
    count=validate_source_manifest(manifest,files)
    return dict(verified_lean_snapshots=count,provenance_files=count+1,
        pins=sorted({row['commit'] for row in manifest}),
        observed_pins=sorted({row['observed_commit'] for row in manifest}),
        scope='Offline exact bytes, SHA256, Git blob and pinned URL identity; comparison-note history is not re-fetched, no Lean compilation or axiom audit')


def diagnostics():
    return dict(status='passed',report=281,identities=exact_identities(),thresholds=threshold_certificates(),
        rounding=rounding_diagnostics(),geometry=geometry_diagnostics(),sources=source_diagnostics(),
        caps=dict(binary_power_exponent=30,affine_coefficient=MAX_COEFFICIENT,
            rational_part=MAX_RATIONAL_PART,modulus=MAX_MODULUS,length=MAX_LENGTH),
        excluded=['No astronomical threshold or witness evaluated','No numerical real-power proof',
                  'No Lean implementation, kernel replay or axiom audit'])


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__); parser.parse_args(argv)
    print(json.dumps(diagnostics(),indent=2,sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
