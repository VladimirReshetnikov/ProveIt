#!/usr/bin/env python3
"""Bounded exact Report282 diagnostics; not formal proofs or huge-N evaluation."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from fractions import Fraction
import hashlib
import importlib.util
from itertools import combinations, product
import json
from math import gcd
from pathlib import Path
import re

ROOT = Path(__file__).absolute().parents[1]
MAIN_PIN = '95460768cc4015862fec316f83df5861b04d28bc'
MATHLIB_PIN = '81a5d257c8e410db227a6665ed08f64fea08e997'
MAX_COEFFICIENT = 100000000
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
    """The only evaluated binary powers; huge powers remain symbolic."""
    bounded(exponent, 'small binary exponent', 0, 30)
    return 1 << exponent


def affine(value):
    """Coefficients of log2(parameter)=p+q*h, for symbolic h=log2(1/a)."""
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
    affine(left); affine(right)
    return left[0] < right[0] and left[1] <= right[1]


def exact_identities():
    theta = (-59, -176)
    t = add((-1882, 0), scale(10477, theta))
    b = add((1882, 0), scale(-10479, theta))
    beta = add(add(scale(2, t), (-12, 0)), scale(-3, b))
    f = (-100, -448); g = (-284, -1408); fg = add(f, g)
    e = add(add(beta, fg), (-1, 0))
    values = dict(theta=theta, t=t, b=b, beta=beta, f=f, g=g, fg=fg, e=e,
        tb=add(t,b), inverse_u_without_q=add((4,0),scale(-2,t)),
        fgK=add(fg,(114,320)), maynard_numerator=add(e,(4,0)))
    expected = dict(t=(-620025,-1843952), b=(620143,1844304),
        beta=(-3100491,-9220816), e=(-3100876,-9222672), tb=(118,352),
        inverse_u_without_q=(1240054,3687904), fgK=(-270,-1536),
        maynard_numerator=(-3100872,-9222672))
    for name, value in expected.items():
        require(values[name] == value, name+' exact exponent identity')
    require(2*135+14 == 284 and 2*704 == 1408, 'localized coefficient exponent')
    require(135+2 == 137, 'factor-four covering mass')
    require(43+5 == 48 and 224+32 == 256, 'row mass weakening')
    return values


def recurrence_budget(q):
    bounded(q,'coefficient count',1,512)
    r=Fraction(1,128*q*q)
    s=1-(q+1)*r
    v=1-(q+1)*(44*q+1)*r
    require(90*q*q-(q+1)*(44*q+1) == (q-1)*(46*q+1), 'polynomial factorization')
    require(s >= Fraction(63,64) and v >= Fraction(19,64), 'uniform recurrence margins')
    q5=q*q*q*q*q
    require(Fraction(169,8)+Fraction(9,32*q5) <= Fraction(685,32) < 22, 'Lau denominator')
    return dict(r=r,s=s,v=v)


def coefficient_certificates():
    checks = {
        'Lau_specialization': Fraction(169,8)+Fraction(9,32) == Fraction(685,32) < 22,
        'Lau_denominator_slack': 22-Fraction(685,32) == Fraction(19,32),
        'Lau_power_margin': Fraction(90,128) == Fraction(45,64) and 1-Fraction(90,128) == Fraction(19,64),
        'factorization_coefficients': (90-44,-45,-1) == (46,1-46,-1),
        'old_power_base_and_growth': pow2_small(11) > 128 and pow2_small(11) > 4,
        'initial_length_two_unit_budget': 128 == 2*64,
        'recurrence_to_row_exponent': 16*128 == 2048 and 4096 == 2*2048,
        'Maynard_rescaling': 4096//256 == 16,
        'Maynard_gap_numerator': (2-2,2-1) == (0,1),
        'rounded_zeta_loss': 155+4*18 == 227 and 32*18 == 576 and 227+1 == 228,
        'coefficient_log_factor': 1536//2 == 768 and 576 <= 228*768,
        'coefficient_loss_below_one': 284 > 270 and 384 > 270 and 230 < pow2_small(8) and 8 < 270,
        'old_beta_affine_comparison': strict_for_nonnegative_h((3100491,9220816),(pow2_small(24),pow2_small(24))),
        'old_beta_exponent_comparison': strict_for_nonnegative_h((24,2),(1048576,2097152)),
        'beta_square_length_safe': 3100491 > 1 and 9220816 > 0,
        'weighted_threshold_denominator': (Fraction(1,8)-Fraction(1,16))*16 == 1,
        'clean_absorption_endpoint': Fraction(3*3,2)-1 >= 3,
    }
    for name, passed in checks.items(): require(passed,name)
    return dict(count=len(checks),checks=checks,
        scope='Exact coefficient certificates; the article proves the all-parameter implications',
        huge_powers_evaluated=False)


def printed_comparison_certificates():
    """Integer certificates for symbolic C+D(1+h) versus 2^(2^70*h)."""
    C=3100876; density_power=9222672
    checks={
        'C_below_2^22': C < pow2_small(22),
        'D_below_2^90': density_power < pow2_small(24) and 24+66 == 90,
        'C_plus_2D_below_2^92': C+2*density_power < pow2_small(26) and 26+66 == 92,
        'near_one_endpoint_2^70_times_2^-63': 70-63 == 7 and pow2_small(7) == 128,
        'near_one_log_margin': 92 < 128,
        'large_h_linear_margin': 93 < pow2_small(7) and 7 < 70,
        'mass_exponent_margin': 137 <= pow2_small(10)-704 and 66 > 0 and 10+66 == 76,
        'overlap_exponent_order': 63 > 16,
    }
    for name,passed in checks.items(): require(passed,name)
    return dict(C=C,D_symbolic='9222672 * 2^66',lower_range='0 < alpha <= 2^(-2^-63)',
        checks=checks,count=len(checks),huge_powers_evaluated=False,
        scope='Integer arithmetic supports the written real-exponential and overlap proof; no real powers are approximated')


def near_maximal_constants():
    eps=Fraction(1,pow2_small(16)); eta=1088*eps
    checks={
        'polarization_cube_loss': 1+16 == 17,
        'Markov_good_pair_loss': 17*64 == 1088,
        'eta_at_endpoint': eta == Fraction(17,1024),
        'slope_missing_fraction': 8*eta == Fraction(17,128) < Fraction(1,4),
        'mass_loss_coefficient': 9*1088 == 9792,
        'mass_at_endpoint': 1-9792*eps == Fraction(871,1024),
        'phase_L2_bound_without_sqrt': Fraction(63,64) >= (1-Fraction(1,64))*(1-Fraction(1,64)),
        'three_errors_below_character_separation': Fraction(9,32) < 2,
        'Fourier_return_above_three_quarters': Fraction(63,64) > (Fraction(3,4)+4*eps)*(Fraction(3,4)+4*eps),
        'three_column_intersection_above_half': 1-3*Fraction(1,8) == Fraction(5,8) > Fraction(1,2),
        'mass_above_printed_target_bound': Fraction(871,1024) > Fraction(1,2),
        'Fourier_above_target_bound': Fraction(3,4) >= Fraction(1,2),
    }
    for name,passed in checks.items(): require(passed,name)
    return dict(checks=checks,count=len(checks),
        scope='Exact rational constants; Parseval, cube identities, telescoping and rigidity are mathematical inputs/proofs, not validated by these constants alone')


def rational(value, low=0):
    if type(value) is not Fraction:
        raise ValueError('exact Fraction required')
    if (abs(value.numerator) > MAX_RATIONAL_PART or value.denominator > MAX_RATIONAL_PART
            or value < low):
        raise ValueError('rational input outside bounded range')
    return value


def floor_half(value):
    rational(value,8)
    half=(value.numerator//value.denominator)//2
    require(Fraction(half) >= value/4,'natural floor/half lower bound')
    return half


def floor_predecessor(value):
    rational(value,4)
    length=value.numerator//value.denominator-1
    require(Fraction(length) >= value/2,'two-unit loss budget')
    return length


def ceiling_budget(value):
    rational(value,1)
    m=-(-value.numerator//value.denominator)
    require(1 <= m and value <= m <= value+1 <= 2*value,'ceiling budget')
    return m


def rounding_diagnostics():
    counts=dict(floor_half=0,floor_predecessor=0,ceiling=0)
    for denominator in range(1,17):
        for numerator in range(8*denominator,64*denominator+1):
            floor_half(Fraction(numerator,denominator));counts['floor_half']+=1
        for numerator in range(4*denominator,32*denominator+1):
            floor_predecessor(Fraction(numerator,denominator));counts['floor_predecessor']+=1
        for numerator in range(denominator,16*denominator+1):
            ceiling_budget(Fraction(numerator,denominator));counts['ceiling']+=1
    return counts


def square_absorption(value):
    rational(value,3)
    lower=value*value/2-1
    require(lower >= value,'clean square-exponent absorption')
    return lower


def short_parent_budget(m, parent_length, modulus):
    bounded(m,'rounded short side',3,64)
    bounded(parent_length,'selected parent length',m,m+1)
    bounded(modulus,'short-parent modulus',9,65536)
    if m*m > modulus:
        raise ValueError('square budget m*m<=N required')
    require(2*(parent_length-1) <= 2*m < m*m <= modulus, 'selected short-parent budget')
    return 2*(parent_length-1)


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



def source16_blocks(length, minimum):
    bounded(length,'chain length',1,MAX_LENGTH)
    bounded(minimum,'block minimum',1,64)
    if length < minimum: raise ValueError('chain below block minimum')
    quotient,remainder=divmod(length,minimum)
    sizes=(minimum,)*(quotient-1)+(minimum+remainder,)
    require(sum(sizes)==length and minimum<=min(sizes)<=max(sizes)<2*minimum,
            'source16 exact integer block partition')
    return sizes


def source16_partition(R,L,T,s,seed=0):
    bounded(R,'initial length',4,256); bounded(L,'cell minimum',2,8)
    bounded(T,'Dirichlet cap',1,8); bounded(s,'quadratic step',1,32)
    bounded(seed,'finite partition seed',0,8)
    if s*L*T>R: raise ValueError('initial residue chains must have at least LT points')
    cells=[]
    for residue in range(s):
        chain=tuple(range(residue,R,s)); offset=0
        for size in source16_blocks(len(chain),L*T):
            block=chain[offset:offset+size];offset+=size
            t=1+(residue+offset+seed)%T
            for residue2 in range(t):
                subchain=block[residue2::t];offset2=0
                for size2 in source16_blocks(len(subchain),L):
                    cell=subchain[offset2:offset2+size2];offset2+=size2
                    require(all(y-x==s*t for x,y in zip(cell,cell[1:])), 'cell own-step identity')
                    cells.append(cell)
    flattened=tuple(x for cell in cells for x in cell)
    require(len(flattened)==R and set(flattened)==set(range(R)), 'source16 partition without endpoint loss')
    require(all(L<=len(cell)<2*L for cell in cells),'source16 cell lengths')
    return tuple(cells)


def rounded_row_model(c,d,z,X):
    for value in (c,d,z,X): rational(value)
    if not (0<c<=Fraction(1,2) and 0<d<1 and 0<z<=1
            and X>=max(3/c,2/d,1/(d*z))):
        raise ValueError('positive rounded-row budget hypotheses required')
    m=ceiling_budget(c*X)
    require(3<=m<=X,'row integer lower and upper bounds')
    require(m+1<=2*X<=d*X*X,'short parent fits coefficient cell')
    require(Fraction(m)/(d*X*X)<=1/(d*X)<=z,'direct actual-step Bohr budget')
    return m


def partition_and_rounding_diagnostics():
    counts=dict(source16_partitions=0,tolerance_guards=0,rounded_row_models=0,square_absorptions=0,
                recurrence_budget_samples=0)
    for q in range(1,513): recurrence_budget(q);counts['recurrence_budget_samples']+=1
    for R in (32,47,64,97,128,191,256):
        for L in range(2,7):
            for T in range(1,7):
                for s in range(1,min(8,R//(L*T))+1):
                    for seed in (0,3):
                        source16_partition(R,L,T,s,seed);counts['source16_partitions']+=1
    for L in range(2,9):
        for T in range(4,17):
            for denominator in range(2,17):
                delta=Fraction(1,denominator);eta=delta/(4*L*T*T)
                require(0<eta<=Fraction(1,256)<Fraction(1,100),'external tolerance range')
                require(delta/2+(2*L*T-1)*T*eta<delta,'own-step error budget')
                counts['tolerance_guards']+=1
    for c in (Fraction(1,2),Fraction(1,4),Fraction(1,16)):
        for d in (Fraction(1,2),Fraction(1,4),Fraction(1,8)):
            for z in (Fraction(1,2),Fraction(1,4),Fraction(1,8)):
                minimum=max(3/c,2/d,1/(d*z))
                for extra in (Fraction(0),Fraction(1,3),Fraction(7)):
                    rounded_row_model(c,d,z,minimum+extra);counts['rounded_row_models']+=1
    for denominator in range(1,17):
        for numerator in range(3*denominator,16*denominator+1):
            square_absorption(Fraction(numerator,denominator));counts['square_absorptions']+=1
    return dict(counts=counts,scope='Bounded exact regression models of partition, own-step and threshold guards')


def partial_additive(n,m,domain,values):
    bounded(n,'cyclic domain modulus',1,7);bounded(m,'cyclic codomain modulus',1,5)
    if type(domain) is not tuple or type(values) is not tuple or len(domain)!=len(values) or len(domain)>n:
        raise ValueError('bounded tuples for a function on a subset required')
    for a in domain:bounded(a,'domain element',0,n-1)
    for value in values:bounded(value,'codomain element',0,m-1)
    if tuple(sorted(set(domain)))!=domain:raise ValueError('strictly ordered distinct domain required')
    F=dict(zip(domain,values))
    return all((F[x]+F[y])%m==F[(x+y)%n] for x in domain for y in domain if (x+y)%n in F)


def dense_extension(n,m,domain,values):
    if not partial_additive(n,m,domain,values):raise ValueError('partial additivity required')
    if 4*len(domain)<=3*n:raise ValueError('strict density greater than three quarters required')
    F=dict(zip(domain,values));extension=[]
    for h in range(n):
        differences={(F[(u+h)%n]-F[u])%m for u in domain if (u+h)%n in F}
        require(len(differences)==1,'well-defined difference extension')
        extension.append(next(iter(differences)))
    require(all(extension[a]==F[a] for a in domain),'extension agrees on original domain')
    require(all(extension[(h+k)%n]==(extension[h]+extension[k])%m for h in range(n) for k in range(n)),
            'difference extension is additive')
    slopes=[slope for slope in range(m) if n*slope%m==0 and all(slope*a%m==F[a] for a in domain)]
    require(len(slopes)==1,'unique cyclic homomorphism extension')
    require(tuple(extension)==tuple(slopes[0]*a%m for a in range(n)),'slope and difference extension agree')
    return tuple(extension)


def dense_extension_diagnostics():
    subsets=candidates=partial_maps=0
    for n in range(1,7):
        for m in range(1,5):
            for size in range(3*n//4+1,n+1):
                for domain in combinations(range(n),size):
                    subsets+=1
                    for values in product(range(m),repeat=size):
                        candidates+=1
                        if partial_additive(n,m,domain,values):
                            dense_extension(n,m,domain,values);partial_maps+=1
    kernels=0
    for n in range(2,129):
        require(len({x%n for x in range(n)})==n and 1%n!=0,'proper nonzero-step full cycle')
        for d in range(1,n):
            kernel=sum(d*a%n==0 for a in range(n))
            require(kernel==gcd(d,n) and 2*kernel<=n,'nonzero multiplication kernel bound')
            kernels+=1
    return dict(domain_moduli='1..6',codomain_moduli='1..4',subsets=subsets,
        candidate_maps=candidates,partially_additive_maps=partial_maps,
        kernel_moduli='2..128',nonzero_multiplier_kernels=kernels,
        scope='Exhaustive small cyclic instances only; arbitrary finite-abelian dense extension and all-cyclic kernel arguments are proved in the article')


def verify_source_bytes(raw,row):
    if type(raw) is not bytes or not 1<=len(raw)<=MAX_SOURCE_SNAPSHOT_BYTES:
        raise ValueError('bounded nonempty source bytes required')
    keys={'name','repository','repository_path','commit','url','bytes','sha256','git_blob_sha1'}
    if type(row) is not dict or set(row)!=keys:raise ValueError('exact curated source record required')
    name=row['name']
    if type(name) is not str or not re.fullmatch(r'[A-Za-z0-9_-]+\.(lean|json)',name):
        raise ValueError('ordinary selected source filename required')
    if name=='Mathlib_Fourier_ZMod.lean':
        repository='leanprover-community/mathlib4';commit=MATHLIB_PIN;path='Mathlib/Analysis/Fourier/ZMod.lean'
    else:
        repository='VladimirReshetnikov/ProveIt';commit=MAIN_PIN
        path='lake-manifest.json' if name=='lake-manifest.json' else 'Combinatorics/Ramsey/Lean/GowersSzemeredi/'+name
        if not (name.endswith('.lean') or name=='lake-manifest.json'):raise ValueError('selected source extension required')
    if (row['repository'],row['repository_path'],row['commit'])!=(repository,path,commit):
        raise ValueError('repository path or immutable pin differs from selected source')
    for key,width in (('git_blob_sha1',40),('sha256',64)):
        if type(row[key]) is not str or not re.fullmatch('[0-9a-f]{'+str(width)+'}',row[key]):raise ValueError('invalid '+key)
    if row['url']!='https://github.com/'+repository+'/blob/'+commit+'/'+path:
        raise ValueError('pinned URL differs from repository path and commit')
    bounded(row['bytes'],'source size',1,MAX_SOURCE_SNAPSHOT_BYTES)
    blob=hashlib.sha1(b'blob '+str(len(raw)).encode('ascii')+b'\0'+raw).hexdigest()
    require(len(raw)==row['bytes'],'source byte length mismatch')
    require(hashlib.sha256(raw).hexdigest()==row['sha256'],'source SHA256 mismatch')
    require(blob==row['git_blob_sha1'],'source Git blob mismatch')
    return blob


def validate_source_manifest(manifest,files):
    if type(manifest) is not list or not 1<=len(manifest)<=MAX_SOURCE_RECORDS or type(files) is not dict or len(files)>128:
        raise ValueError('bounded curated manifest list and file dictionary required')
    if any(type(name) is not str or not 1<=len(name)<=1024 for name in files):raise ValueError('bounded string file names required')
    names=set()
    for row in manifest:
        if type(row) is not dict or type(row.get('name')) is not str:raise ValueError('curated source row required')
        name='provenance/sources/'+row['name']
        require(name in files,'curated source missing')
        verify_source_bytes(files[name],row)
        require(name not in names,'duplicate curated source');names.add(name)
    require(names=={name for name in files if name.startswith('provenance/sources/')},'source manifest/file inventory mismatch')
    if 'provenance/sources/lake-manifest.json' in files:
        lake=json.loads(files['provenance/sources/lake-manifest.json'])
        matching=[p for p in lake['packages'] if p.get('name')=='mathlib']
        require(len(matching)==1 and matching[0]['rev']==MATHLIB_PIN,'exact Mathlib dependency pin')
    return len(names)


def source_diagnostics():
    spec=importlib.util.spec_from_file_location('report282_build',ROOT/'build.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    files=module.verified_snapshot();manifest=json.loads(files['provenance/source_manifest.json'])
    count=validate_source_manifest(manifest,files)
    return dict(verified_source_snapshots=count,verified_lean_snapshots=sum(row['name'].endswith('.lean') for row in manifest),
        pins=sorted({row['commit'] for row in manifest}),
        scope='Offline exact byte lengths, SHA256, Git blob SHA1 and pinned repository URL identity; no network, Lean compilation or axiom audit')


def diagnostics():
    return dict(status='passed',report=282,identities=exact_identities(),coefficients=coefficient_certificates(),
        printed_comparison=printed_comparison_certificates(),near_maximal=near_maximal_constants(),
        rounding=rounding_diagnostics(),geometry=geometry_diagnostics(),
        partition_and_rounding=partition_and_rounding_diagnostics(),dense_extension=dense_extension_diagnostics(),
        sources=source_diagnostics(),
        caps=dict(binary_power_exponent=30,affine_coefficient=MAX_COEFFICIENT,rational_part=MAX_RATIONAL_PART,
                  modulus=MAX_MODULUS,length=MAX_LENGTH),
        excluded=['No astronomical threshold or witness evaluated','No floating-point or numerical real-power proof',
                  'No proof of imported analytic extraction or external recurrence theorems',
                  'No Lean implementation, kernel replay or axiom audit'])


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__);parser.parse_args(argv)
    print(json.dumps(diagnostics(),indent=2,sort_keys=True));return 0


if __name__=='__main__':raise SystemExit(main())
