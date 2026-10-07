#!/usr/bin/env python3
"""Exact, read-only certificates for Report293 (Python 3.10+, standard library)."""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path

MAX_INTEGER_BITS = 4096
MAX_DIMENSION = 16


def require(condition, explanation):
    """A mathematical guard that stays active under python -O."""
    if type(condition) is not bool or type(explanation) is not str:
        raise ValueError('require needs a bool and a string')
    if not condition:
        raise RuntimeError(explanation)


def integer(value, name='integer'):
    if type(value) is not int or value.bit_length() > MAX_INTEGER_BITS:
        raise ValueError(name + ' must be a bounded exact integer (not bool)')
    return value


def matrix(value, name='matrix'):
    if type(value) not in (list, tuple) or not 1 <= len(value) <= MAX_DIMENSION:
        raise ValueError(name + ' must have 1..16 rows')
    if type(value[0]) not in (list, tuple) or not 1 <= len(value[0]) <= MAX_DIMENSION:
        raise ValueError(name + ' must have 1..16 columns')
    n = len(value[0])
    for row in value:
        if type(row) not in (list, tuple) or len(row) != n:
            raise ValueError(name + ' must be rectangular')
        for entry in row:
            integer(entry, name + ' entry')
    return [list(row) for row in value]


def transpose(value):
    return [list(row) for row in zip(*matrix(value))]


def multiply(left, right):
    left, right = matrix(left), matrix(right)
    if len(left[0]) != len(right):
        raise ValueError('matrix multiplication dimensions do not match')
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*right)] for row in left]


def determinant(value):
    value = matrix(value)
    if len(value) != len(value[0]):
        raise ValueError('determinant needs a square matrix')
    a = [[Fraction(x) for x in row] for row in value]
    result = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        p = a[j][j]
        result *= p
        for i in range(j+1, len(a)):
            q = a[i][j] / p
            for k in range(j, len(a)):
                a[i][k] -= q*a[j][k]
    require(result.denominator == 1, 'integer determinant has a denominator')
    return int(result)


def row_lattice(rows):
    """Return a row-Hermite basis, unimodular U, and R=U*rows.

    Every reduction is a row swap, sign change, or integral row addition.
    The complete integer identity and determinant are checked independently.
    """
    original = matrix(rows, 'lattice generators')
    a = [row[:] for row in original]
    m, n = len(a), len(a[0])
    u = [[int(i == j) for j in range(m)] for i in range(m)]

    def swap(i, j):
        a[i], a[j] = a[j], a[i]
        u[i], u[j] = u[j], u[i]

    def add_row(i, j, q):
        a[i] = [x+q*y for x, y in zip(a[i], a[j])]
        u[i] = [x+q*y for x, y in zip(u[i], u[j])]

    k = 0
    for j in range(n):
        p = next((i for i in range(k, m) if a[i][j]), None)
        if p is None:
            continue
        swap(k, p)
        for i in range(k+1, m):
            while a[i][j]:
                q = a[k][j] // a[i][j]
                add_row(k, i, -q)
                swap(k, i)
        if a[k][j] < 0:
            a[k] = [-x for x in a[k]]
            u[k] = [-x for x in u[k]]
        for i in range(k):
            add_row(i, k, -(a[i][j] // a[k][j]))
        k += 1
        if k == m:
            break
    require(multiply(u, original) == a, 'unimodular reconstruction failed')
    require(abs(determinant(u)) == 1, 'row transformation is not unimodular')
    require(all(not any(row) for row in a[k:]), 'nonzero reduction tail')
    return tuple(tuple(row) for row in a[:k]), u, a


def member(basis, vector):
    """Exact membership in a nonzero row-Hermite basis; no saturation."""
    basis = matrix(basis, 'basis')
    if type(vector) not in (tuple, list) or len(vector) != len(basis[0]):
        raise ValueError('vector dimension differs from basis dimension')
    rem = [integer(x, 'vector entry') for x in vector]
    pivots = []
    previous = -1
    for row in basis:
        j = next((i for i, x in enumerate(row) if x), None)
        if j is None or j <= previous or row[j] <= 0:
            raise ValueError('basis must have increasing positive pivots')
        previous = j
        pivots.append(j)
    for row, j in zip(basis, pivots):
        if rem[j] % row[j]:
            return False
        q = rem[j] // row[j]
        rem = [x-q*y for x, y in zip(rem, row)]
    return not any(rem)


POINTS = tuple((i, j) for j in range(3) for i in range(3))
INDEX = {p: k for k, p in enumerate(POINTS)}
DIRECTIONS = ((1, 0), (0, 1), (1, 1), (1, 2))


def add(x, y):
    return ((x[0]+y[0]) % 3, (x[1]+y[1]) % 3)


def quadruples():
    return tuple((x, y, z, INDEX[((POINTS[x][0]+POINTS[y][0]-POINTS[z][0]) % 3,
                                  (POINTS[x][1]+POINTS[y][1]-POINTS[z][1]) % 3)])
                 for x, y, z in product(range(9), repeat=3))


QUADS = quadruples()


def exact_weights(weights, nonnegative=True):
    if type(weights) not in (tuple, list) or len(weights) != 9:
        raise ValueError('weights need exactly nine entries in row-major order')
    for w in weights:
        if type(w) not in (int, Fraction):
            raise ValueError('weights must be exact integers or Fractions')
        if max(abs(w.numerator).bit_length(), w.denominator.bit_length()) > 256:
            raise ValueError('weight exceeds the 256-bit rational bound')
        if nonnegative and w < 0:
            raise ValueError('weights must be nonnegative')
    return tuple(weights)


def target_values(values, modulus):
    if type(values) not in (tuple, list) or len(values) != 9:
        raise ValueError('target needs exactly nine integer values')
    for v in values:
        integer(v, 'target value')
    if modulus is not None:
        integer(modulus, 'modulus')
        if modulus < 1:
            raise ValueError('modulus must be positive, or None for Z')
    return tuple(values)


def energies(values, weights, modulus=None, method='quadruples'):
    """Return (E_a,E), for target Z or C_modulus and exact nonzero weights."""
    values = target_values(values, modulus)
    weights = exact_weights(weights)
    if not any(weights):
        raise ValueError('weights must be nonzero')
    if type(method) is not str or method not in ('quadruples', 'pairs'):
        raise ValueError('method must be quadruples or pairs')
    if method == 'pairs':
        ordinary, respected = defaultdict(int), defaultdict(int)
        for x, y in product(range(9), repeat=2):
            s = add(POINTS[x], POINTS[y])
            target = values[x] + values[y]
            if modulus is not None:
                target %= modulus
            ordinary[s] += weights[x]*weights[y]
            respected[s, target] += weights[x]*weights[y]
        return sum(v*v for v in respected.values()), sum(v*v for v in ordinary.values())
    total = retained = 0
    for x, y, z, w in QUADS:
        term = weights[x]*weights[y]*weights[z]*weights[w]
        total += term
        defect = values[x]+values[y]-values[z]-values[w]
        if defect == 0 if modulus is None else defect % modulus == 0:
            retained += term
    return retained, total


def histograms(values, modulus=None):
    values = target_values(values, modulus)
    result = []
    for direction in DIRECTIONS:
        counts = Counter()
        for k, p in enumerate(POINTS):
            defect = values[INDEX[add(p, direction)]] - values[k]
            counts[defect if modulus is None else defect % modulus] += 1
        result.append(sum(n*n for n in counts.values()))
    return result


def partitions(n, maximum=None):
    integer(n, 'partition size')
    if not 0 <= n <= 16:
        raise ValueError('partition size must be 0..16')
    if maximum is not None:
        integer(maximum, 'maximum part')
        if maximum < 1:
            raise ValueError('maximum part must be positive')
    if not n:
        yield ()
        return
    for head in range(min(n, maximum or n), 0, -1):
        for tail in partitions(n-head, head):
            yield (head,) + tail


def check_upper_bound():
    """Exhaustive universal relation choices and exact branch witnesses."""
    # Reconstruct the nine transversal lines from the domain, then deduplicate
    # their literal target triples after translation by the first value.
    formal = [[(0,0,0),(1,0,0),(2,0,0)],
              [(0,1,0),(1,1,0),(2,1,0)],
              [(1,0,1),(2,0,1),(0,0,1)]]
    triples=[];line_to_triple=[]
    for slope,start in product(range(3),repeat=2):
        t=[formal[j][(start+slope*j)%3] for j in range(3)]
        normalized=tuple(tuple(x-y for x,y in zip(r,t[0])) for r in t)
        if normalized not in triples:triples.append(normalized)
        line_to_triple.append({'slope':slope,'start':start,'triple_number':triples.index(normalized)+1})
    require(len(triples)==6,'Wrong number of distinct transversal conditions')
    relations=[[[3*t[k][coordinate]-sum(p[coordinate] for p in t)
                 for coordinate in range(3)] for k in range(3)] for t in triples]

    # Independently reduced bases are matched against the displayed candidates.
    # The original basis list is not used to compute our 729 normal forms.
    claimed_bases = LATTICE_BASES
    basis_lookup={row_lattice(transpose(b))[0]:(b,c) for b,c in claimed_bases}
    basis_reconstructions=[]
    for b,c in claimed_bases:
        nf,u,reduced=row_lattice(transpose(b))
        basis_reconstructions.append({'claimed_column_basis':b,'transpose_generators':transpose(b),
           'unimodular_U':u,'U_times_generators':reduced,'independent_row_basis':nf})
    require(len(basis_lookup)==8,'Candidate lattices are not distinct')
    counts=Counter();records=[]
    for choice in product(range(3),repeat=6):
        generators=[relations[i][choice[i]] for i in range(6)]
        normal,u,reduced=row_lattice(generators)
        require(normal in basis_lookup,'Unlisted relation lattice')
        basis,expected_count=basis_lookup[normal];counts[normal]+=1
        excluded=member(normal,(3,0,0))
        if not excluded:
            require(all(member(normal,vec) for vec in [(6,0,0),(0,6,0),(0,0,6)]),'Six-torsion not forced')
            require(any(member(normal,(-3*e,3,0)) for e in (0,1)),'3b not binary')
            require(any(member(normal,(-3*e,0,3)) for e in (0,1)),'3c not binary')
        records.append({'choice':choice,'relation_generators_rows':generators,
                        'unimodular_U':u,'U_times_generators':reduced,
                        'independent_row_basis':normal,'claimed_column_basis':basis,
                        'forces_3v_zero':excluded})
    require(set(counts)==set(basis_lookup),'Missing relation lattice')
    for normal,count in counts.items():require(count==basis_lookup[normal][1],'Wrong class count')
    # High-Q midpoint branches in the universal free abelian relation group.
    # Coordinates here are (b,c,delta), with 2delta=0 imposed in every choice.
    high_triples=[[(0,0,0),(1,0,0),(0,1,e)] for e in (0,1)]
    high_relations=[[[3*t[k][r]-sum(p[r] for p in t) for r in range(3)]
                     for k in range(3)] for t in high_triples]
    high_branch_records=[]
    for choice in product(range(3),repeat=2):
        relations_now=[(0,0,2)]+[high_relations[i][choice[i]] for i in range(2)]
        normal,_,_=row_lattice(relations_now)
        excluded=member(normal,(0,0,1))
        branches=[]
        if member(normal,(1,-2,0)):branches.append('I')
        if member(normal,(1,1,0)) and member(normal,(-3,0,1)):branches.append('II')
        if member(normal,(-2,1,0)) and member(normal,(3,0,1)):branches.append('III')
        require(excluded or bool(branches),'Uncovered high-Q midpoint choice')
        high_branch_records.append({'midpoints':choice,'forces_delta_zero':excluded,'implied_branches':branches})
    require(sum(x['forces_delta_zero'] for x in high_branch_records)==2,'High-Q excluded choices')

    # All exceptional-edge configurations, with genuine affine source changes.
    # A row with edge tail e has values baseline+((i-e-1) mod 3)*v.
    edge_records=[]
    for edges in product(range(3),repeat=3):
        aligned=any(all(edges[j]==(b*j+c)%3 for j in range(3))
                    for b,c in product(range(3),repeat=2))
        wanted=(2,2,2) if aligned else (2,2,1)
        found=None
        for orientation,b,c in product((1,-1),range(3),range(3)):
            new=tuple((edges[j]-b*j-c)%3 if orientation==1
                      else (b*j+c-edges[j]-1)%3 for j in range(3))
            if new!=wanted:continue
            coefficients=[[((orientation*i+b*j+c-edges[j]-1)%3) for i in range(3)] for j in range(3)]
            for j in range(3):
                base=coefficients[j][0 if j<2 or aligned else 2]
                reduced=[x-base for x in coefficients[j]]
                target=[0,1,2] if j<2 or aligned else [1,2,0]
                require(reduced==[orientation*x for x in target],'Invalid edge normal form coefficients')
            found={'orientation':orientation,'shear':b,'translation':c};break
        require(found is not None,'Unnormalized exceptional-edge configuration')
        edge_records.append({'edges':edges,'aligned':aligned,'affine_change':found,'normal_edges':wanted})
    require(sum(x['aligned'] for x in edge_records)==9,'Aligned count')

    # Symbolic derivative partition exclusions, without bounded-target testing.
    derivative_records=[]
    for kind in [(8,1),(7,1,1),(7,2)]:
        assignments=[]
        if kind==(8,1):
            for p in range(9):assignments.append([int(i==p) for i in range(9)])
        elif kind==(7,2):
            for ps in combinations(range(9),2):assignments.append([int(i in ps) for i in range(9)])
        else:
            for p,q in product(range(9),repeat=2):
                if p!=q:assignments.append([1 if i==p else 2 if i==q else 0 for i in range(9)])
        impossible_AP=forced_collapse=surviving=0
        for assignment in assignments:
            cycles=[assignment[3*j:3*j+3] for j in range(3)]
            if any(len(set(c))==3 for c in cycles):impossible_AP+=1;continue
            n=max(assignment)+1
            cycle_relations=[[c.count(k) for k in range(n)] for c in cycles]
            basis,_,_=row_lattice(cycle_relations)
            if any(member(basis,[-1]+[int(k==j) for k in range(1,n)]) for j in range(1,n)):
                forced_collapse+=1;continue
            require(kind==(7,2),'Unexpected possible high partition')
            require(member(basis,(3,0)) and member(basis,(-2,2)),'High-direction torsion missing')
            surviving+=1
        derivative_records.append({'partition':kind,'assignments':len(assignments),
                 'three_distinct_cycle':impossible_AP,'forced_equal_values':forced_collapse,
                 'possible_7_2_configurations':surviving})

    partitions9=list(partitions(9))
    require([p for p in partitions9 if sum(x*x for x in p)==45]==[(6,3)],'Q45 partitions')
    require([p for p in partitions9 if sum(x*x for x in p)>45 and len(p)>1]
            ==[(8,1),(7,2),(7,1,1)],'High partitions')
    require(max(sum(x*x for x in p) for p in partitions9 if p[0]<=6 and p!=(6,3))==41,'Low partition maximum')
    cycle_k=[k for k in product(range(4),repeat=3) if sum(k)==3]
    require(set(tuple(sorted(k)) for k in cycle_k)=={(0,0,3),(0,1,2),(1,1,1)},'Q45 cycle types')
    for ks in cycle_k:
        basis,_,_=row_lattice([[3-k,k] for k in ks])
        if tuple(sorted(ks))==(0,1,2):require(member(basis,(-1,1)),'Mixed Q45 cycles not excluded')
        elif tuple(sorted(ks))==(0,0,3):require(member(basis,(3,0)) and member(basis,(0,3)),'Case A torsion')
        else:require(member(basis,(2,1)),'Case B increment relation')

    points=POINTS;index=INDEX;quads=QUADS
    require(len(quads)==729,"Quadruple count")

    line_indices=[index[(i,0)] for i in range(3)]
    line_coeffs=Counter()
    for x,y,z,w in quads:
        if all(p in line_indices for p in (x,y,z,w)):
            coefficients=tuple(int(x==p)+int(y==p)-int(z==p)-int(w==p) for p in line_indices)
            canonical=min(coefficients,tuple(-v for v in coefficients))
            line_coeffs[canonical]+=1
    require(line_coeffs[(0,0,0)]==15 and sorted(v for k,v in line_coeffs.items() if any(k))==[4,4,4],'Line 15+4m formula')

    patterns={
     'order_nine':([0,0,0,2,2,2,1,4,7],9,[1]*9,(369,729),[33,33,33,45]),
     'aligned_cap':([0,1,0,1,0,1,0,1,0],2,[1]*9,(425,729),[41,41,45,45]),
     'two_point':([1,1,0,0,0,0,0,0,0],2,[2,2,2,1,1,1,1,1,1],(1330,2322),None),
     'cross_II':([0,0,0,1,1,1,1,1,0],2,[1,1,1,1,1,1,2,2,2],(1354,2322),[45,45,45,53]),
     'cross_III':([0,0,0,1,1,1,0,0,1],2,[1,1,1,1,1,1,2,2,2],(1354,2322),[45,45,45,53]),
    }
    witness_results={}
    for name,(values,modulus,weights,expected,expected_qs) in patterns.items():
        es=energies(values,weights,modulus);qs=histograms(values,modulus)
        require(es==energies(values,weights,modulus,method='pairs'),'Independent pair witness '+name)
        require(es==expected,'Witness energy '+name)
        if expected_qs is not None:require(sorted(qs)==expected_qs,'Histogram '+name)
        require(energies(values,[1]*9,modulus)[0]==81+2*sum(qs),'Energy identity '+name)
        require(Fraction(*es)<Fraction(7,12),'Witness exceeds separator '+name)
        witness_results[name]={'values':values,'modulus':modulus,'weights':weights,'E_a':es[0],'E':es[1],'ratio':str(Fraction(*es)),'Q':qs}

    binary_results=[]
    for e,f in product(range(2),repeat=2):
        values=[0,1,0,e,e^1,e,f^1,f,f]
        qs=histograms(values,2);es=energies(values,[1]*9,2)
        expect=[41,41,41,45] if (e,f)==(0,0) else [45,45,45,53]
        require(sorted(qs)==expect,'Nonaligned binary histograms')
        if (e,f)==(0,0):require(es==(417,729),'Nonaligned low witness')
        require(es[0]==81+2*sum(qs),'Nonaligned energy identity')
        binary_results.append({'e':e,'f':f,'values':values,'Q':qs,'E_a':es[0],'E':es[1]})

    spike_values=[1]+[0]*8
    spike_N=[0]*5;spike_D=[0]*5
    for quad in quads:
        degree=quad.count(0);spike_D[degree]+=1
        if sum(spike_values[p] for p in quad)%2==0:spike_N[degree]+=1
    require(spike_N==[456,0,48,0,1] and spike_D==[456,224,48,0,1],'Spike polynomials')
    # Maximize t/N: N-tN' has coefficients 456,-48,-3 in t^0,t^2,t^4.
    stationary=[(1-i)*n for i,n in enumerate(spike_N)]
    require(stationary==[456,0,-48,0,-3],'Spike stationary polynomial')
    # Formal arithmetic in Q[s]/(s^2-6).
    def addq(a,b):return (a[0]+b[0],a[1]+b[1])
    def mulq(a,b):return(a[0]*b[0]+6*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    def scaleq(n,a):return(n*a[0],n*a[1])
    t2=(-8,6)
    require(Fraction(2)**2<6,'sqrt(6)>2 and u^2>0')
    require(mulq(t2,addq(t2,(24,0)))==scaleq(8,(11,6)),'Equivalent kappa expressions')
    kappa_square = scaleq(Fraction(1,3136), mulq(t2,mulq(addq(t2,(24,0)),addq(t2,(24,0)))))
    require(kappa_square == (1,Fraction(81,196)), 'Exact kappa square')
    stability_c = addq((1,0),scaleq(Fraction(-4,9),kappa_square))
    require(stability_c == (Fraction(5,9),Fraction(-9,49)), 'Exact stability constant')
    require(Fraction(2)**2 < 6 < Fraction(5,2)**2, 'Stability radical brackets')
    require(Fraction(5,9)-Fraction(9,49)*Fraction(5,2) == Fraction(85,882)>0,
            'Stability constant strictly positive')
    require(Fraction(5,9)-Fraction(9,49)*2 == Fraction(83,441)<Fraction(1,2),
            'Stability constant below one half')
    require(addq(addq(scaleq(3,mulq(t2,t2)),scaleq(48,t2)),(-456,0))==(0,0),'Stationary root identity')
    N_at=addq(addq(mulq(t2,t2),scaleq(48,t2)),(456,0))
    require(N_at==scaleq(32,(11,6)),'Lambda simplification')
    comparison=addq(scaleq(25,mulq((11,6),(11,6))),scaleq(-2401,t2))
    require(comparison==(27633,-11106),'Exact comparison polynomial')
    require(Fraction(49,20)**2>6 and Fraction(27633)-11106*Fraction(49,20)==Fraction(4233,10),'Strict positive comparison')
    require(Fraction(5,9)<Fraction(7,12) and Fraction(409,729)<Fraction(7,12),'Remaining witnesses')
    # Cross-check all binary maps by affine/complement orbits. This is a sanity
    # check of binary reductions, never evidence for arbitrary-target universality.
    perms=[]
    for a,b,c,d,tx,ty in product(range(3),repeat=6):
        if (a*d-b*c)%3:
            perms.append(tuple(index[((a*x+b*y+tx)%3,(c*x+d*y+ty)%3)] for x,y in points))
    require(len(set(perms))==432,'Affine group size')
    representatives={
     'constant':(0,)*9,
     'cut':(1,1,1,0,0,0,0,0,0),
     'spike':tuple(spike_values),
     'two_point':(1,1,0,0,0,0,0,0,0),
     'noncollinear_three':tuple(binary_results[0]['values']),
     'line_plus_point':tuple(patterns['cross_III'][0]),
     'cap':tuple(patterns['aligned_cap'][0]),
    }
    covered={};orbit_counts={}
    for name,values in representatives.items():
        orbit={tuple(values[p]^flip for p in perm) for perm in perms for flip in (0,1)}
        require(not any(v in covered for v in orbit),'Binary orbits overlap')
        for v in orbit:covered[v]=name
        orbit_counts[name]=len(orbit)
    require(len(covered)==512,'Binary orbit completeness')
    for values in product(range(2),repeat=9):
        qs=histograms(values,2)
        require((81 in qs)==(covered[values] in ('constant','cut')),'Constant derivative family test')
        require(energies(values,[1]*9,2)[0]==81+2*sum(qs),'All-binary energy identity')


    certificate = {'schema_version': 1,
        'method': 'Integer U with determinant +/-1 and U times generators equal row-Hermite form',
        'bases': basis_reconstructions,
        'records': [{'choice': r['choice'], 'basis_index': next(i for i,(b,_) in enumerate(claimed_bases) if b==r['claimed_column_basis']), 'generators': r['relation_generators_rows'], 'U': r['unimodular_U'], 'R': r['U_times_generators']} for r in records]}
    summary = {
     'transversal_lines':line_to_triple,'six_triples':triples,'midpoint_relations':relations,
     'midpoint_choices_checked':len(records),'distinct_lattices':len(counts),
     'relation_lattice_classes':[{'claimed_column_basis':basis_lookup[nf][0],'independent_row_basis':nf,
           'count':count,'forces_3v_zero':member(nf,(3,0,0))} for nf,count in counts.items()],
     'excluded_choices':sum(c for nf,c in counts.items() if member(nf,(3,0,0))),
     'surviving_choices':sum(c for nf,c in counts.items() if not member(nf,(3,0,0))),
     'exceptional_edge_configurations':edge_records,'derivative_exclusions':derivative_records,
     'high_Q_midpoint_branches':high_branch_records,
     'Q45_cycle_count_lists':sorted(set(tuple(sorted(k)) for k in cycle_k)),
     'ordered_quadruples':len(quads),'witnesses':witness_results,'nonaligned_binary_patterns':binary_results,
     'spike_N_coefficients':spike_N,'spike_E_coefficients':spike_D,'stationary_coefficients':stationary,
     'lambda_comparison_square_difference':comparison,
     'stability_radicals': {'kappa_squared': kappa_square, 'c': stability_c,
                            'c_strict_lower_bound': Fraction(85,882), 'c_strict_upper_bound': Fraction(83,441)},
     'binary_affine_complement_orbit_sizes':orbit_counts,
    }
    return summary, certificate


class Polynomial:
    """Small sparse Q-polynomial ring; monomials are sorted variable names.

    Equality compares every rational coefficient. There is no interpolation,
    randomized identity testing, symbolic-library dependency, or floating point.
    """
    def __init__(self, terms=None):
        if terms is None:
            terms = {}
        if type(terms) is not dict or len(terms) > 100000:
            raise ValueError('polynomial terms must be a bounded dictionary')
        result = {}
        for monomial, coefficient in terms.items():
            if (type(monomial) is not tuple or len(monomial) > 16
                    or any(type(v) is not str or not v.isidentifier() or len(v) > 20 for v in monomial)
                    or tuple(sorted(monomial)) != monomial):
                raise ValueError('monomial must be a sorted tuple of variable identifiers, degree <=16')
            if type(coefficient) not in (int, Fraction):
                raise ValueError('coefficient must be an exact integer or Fraction')
            if max(abs(coefficient.numerator).bit_length(), coefficient.denominator.bit_length()) > 4096:
                raise ValueError('coefficient exceeds exact-size bound')
            if coefficient:
                result[monomial] = Fraction(coefficient)
        self.terms = result

    @classmethod
    def variable(cls, name):
        return cls({(name,): 1})

    @classmethod
    def constant(cls, value):
        return cls({(): value})

    @staticmethod
    def coerce(value):
        if type(value) is Polynomial:
            return value
        if type(value) in (int, Fraction):
            return Polynomial.constant(value)
        raise ValueError('polynomial operation needs exact coefficients')

    def __add__(self, other):
        other = self.coerce(other)
        terms = self.terms.copy()
        for mon, value in other.terms.items():
            terms[mon] = terms.get(mon, 0) + value
        return Polynomial(terms)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({mon: -value for mon, value in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        terms = defaultdict(Fraction)
        for mon1, value1 in self.terms.items():
            for mon2, value2 in other.terms.items():
                terms[tuple(sorted(mon1+mon2))] += value1*value2
        return Polynomial(dict(terms))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if type(other) not in (int, Fraction) or not other:
            raise ValueError('polynomial division requires a nonzero exact scalar')
        return self * (1/Fraction(other))

    def __pow__(self, exponent):
        integer(exponent, 'polynomial exponent')
        if not 0 <= exponent <= 16:
            raise ValueError('polynomial exponent must be 0..16')
        value = Polynomial.constant(1)
        for _ in range(exponent):
            value *= self
        return value

    def __eq__(self, other):
        if type(other) in (int, Fraction):
            other = self.constant(other)
        return type(other) is Polynomial and self.terms == other.terms

    def evaluate(self, values):
        if type(values) is not dict:
            raise ValueError('evaluation needs a dictionary')
        variables = set(v for mon in self.terms for v in mon)
        if set(values) != variables:
            raise ValueError('evaluation needs exactly the polynomial variables')
        for value in values.values():
            if type(value) not in (int, Fraction):
                raise ValueError('evaluation needs exact rational values')
        total = Fraction(0)
        for mon, coefficient in self.terms.items():
            term = coefficient
            for var in mon:
                term *= values[var]
            total += term
        return total


def convolution(left, right):
    """Internal exact convolution, also valid for symbolic polynomials."""
    if len(left) != 9 or len(right) != 9:
        raise ValueError('convolution needs two nine-entry vectors')
    return [sum(left[i]*right[INDEX[((s[0]-p[0]) % 3, (s[1]-p[1]) % 3)]]
                for i, p in enumerate(POINTS)) for s in POINTS]


def moments(vector):
    if len(vector) != 9:
        raise ValueError('moments need a nine-entry vector')
    square = sum(v*v for v in vector)
    paired = sum(vector[i]*vector[INDEX[((-p[0]) % 3, (-p[1]) % 3)]]
                 for i, p in enumerate(POINTS))
    conv = convolution(vector, vector)
    cubic = sum(vector[i]*vector[j]*vector[INDEX[add(p, q)]]
                for i, p in enumerate(POINTS) for j, q in enumerate(POINTS))
    energy = sum(v*v for v in conv)
    return square, paired, 4*square+2*paired, cubic, energy


def check_spike_lower_bound():
    """Universal coefficient identities plus explicitly separate sanity tests."""
    checks = []

    def identity(name, left, right=0):
        require(left == right, 'polynomial identity failed: ' + name)
        checks.append(name)

    z = [Polynomial.variable('h'+str(i)) for i in range(1, 8)]
    t, m, k = [Polynomial.variable(name) for name in ('t', 'm', 'kappa')]
    h = [Polynomial.constant(0)] + z + [-sum(z)]
    b = [0]+[1]*8
    g = [m*b[i]+h[i] for i in range(9)]
    f = [t]+g[1:]
    identity('all seven centered parameters are free; h(0)=sum(h)=0', sum(h))
    bb, bh = convolution(b, b), convolution(b, h)
    require(bb == [8]+[7]*8, 'b*b convolution failed')
    identity('b*h=-h at all nine points', sum((bh[i]+h[i])**2 for i in range(9)))
    require(moments(b) == (8, 8, 48, 56, 456), 'uniform nonspike moment constants')
    sh, ph, ah, ch, bh = moments(h)
    _, _, ag, cg, bg = moments(g)
    identity('A(mb+h)=48m^2+A(h)', ag, 48*m*m+ah)
    identity('C(mb+h)=56m^3-m*A(h)/2+C(h)', cg, 56*m**3-m*ah/2+ch)
    identity('B(mb+h)=456m^4+m^2*A(h)-4m*C(h)+B(h)', bg, 456*m**4+m*m*ah-4*m*ch+bh)

    total = Polynomial.constant(0)
    retained = Polynomial.constant(0)
    retained_count = 0
    for quad in QUADS:
        term = Polynomial.constant(1)
        for point in quad:
            term *= f[point]
        total += term
        if quad.count(0) % 2 == 0:
            retained += term
            retained_count += 1
    require(retained_count == 505, 'unweighted retained spike quadruples')
    n = t**4+t*t*ag+bg
    lost = 4*t*cg
    identity('direct 729-quadruple retained polynomial N=t^4+t^2*A(g)+B(g)', retained, n)
    identity('direct 729-quadruple total polynomial E=N+4t*C(g)', total, n+lost)
    scalar = t**4+48*t*t*m*m+456*m**4-224*k*t*m**3
    alpha, beta = t*t+m*m+2*k*t*m, m+k*t
    identity('full centered N-kappa*L identity', n-k*lost,
             scalar+ah*alpha-4*beta*ch+bh)

    real, imag_scaled = [], []
    for xi in DIRECTIONS:
        groups = [sum(h[i] for i, point in enumerate(POINTS)
                      if (xi[0]*point[0]+xi[1]*point[1]) % 3 == j) for j in range(3)]
        real.append(groups[0]-(groups[1]+groups[2])/2)
        imag_scaled.append((groups[2]-groups[1])/2)
    x = sum(a*a for a in real)
    qi = [a*a+3*c*c for a, c in zip(real, imag_scaled)]
    r, tt, u = sum(qi), sum(q*q for q in qi), sum(a*q for a, q in zip(real, qi))
    identity('Fourier real parts sum to zero', sum(real))
    identity('Fourier S(h)=2R/9', sh, 2*r/9)
    identity('Fourier P(h)=2(2X-R)/9', ph, 2*(2*x-r)/9)
    identity('Fourier A(h)=4(2X+R)/9', ah, 4*(2*x+r)/9)
    identity('Fourier B(h)=2T/9', bh, 2*tt/9)
    identity('Fourier C(h)=2U/9', ch, 2*u/9)

    xx, rr, uu = [Polynomial.variable(name) for name in ('X', 'R', 'u')]
    identity('Fourier inequality residual=(R-X)(8R-5X)',
             2*(2*xx+rr)*(4*rr-xx)-9*xx*(3*rr-xx), (rr-xx)*(8*rr-5*xx))
    identity('completed-square bracket', alpha-4*beta**2/9,
             (1-4*k*k/9)*t*t+5*m*m/9+10*k*t*m/9)
    # Here kappa_* = u(u^2+24)/56. The residual is exactly a multiple
    # of 3u^4+48u^2-456, independently checked in Q[sqrt(6)] below.
    scalar_star = t**4+48*t*t*m*m+456*m**4-4*uu*(uu*uu+24)*t*m**3
    factor = (t-uu*m)**2*(t*t+2*uu*t*m+(3*uu*uu+48)*m*m)
    identity('double-root scalar factorization modulo stationary relation',
             scalar_star-factor, m**4*(456-48*uu*uu-3*uu**4))
    identity('unit-mass Cauchy residual', 65*(t*t+m*m)-(t+8*m)**2, (8*t-m)**2)
    identity('unit-mass orthogonal mean coefficient', t*t+8*(-t/8)**2, 9*t*t/8)
    require(Fraction(2**4+48*2**2+456, 224*2) == Fraction(83, 56), 'F(2)')
    require(Fraction(83, 56) < Fraction(3, 2), 'kappa applicability bound')

    # Supplementary, not a universal proof: signed integer centered vectors.
    count, minimum = 0, None
    for vals in product((-1, 0, 1), repeat=7):
        vector = [0]+list(vals)+[-sum(vals)]
        _, _, aa, cc, bb = moments(vector)
        slack = aa*bb-9*cc*cc
        require(slack >= 0, 'centered signed-grid lemma test')
        if aa:
            require(aa > 0 and slack > 0, 'nonzero signed-grid slack test')
            minimum = slack if minimum is None else min(minimum, slack)
        count += 1
    return {'universal_coefficient_identities': checks,
            'number_of_coefficient_identities': len(checks),
            'free_centered_parameters': 7,
            'direct_total_polynomial_terms': len(total.terms),
            'direct_retained_polynomial_terms': len(retained.terms),
            'retained_unweighted_quadruples': retained_count,
            'scalar_factorization': '(t-u*m)^2*(t^2+2*u*t*m+(3*u^2+48)*m^2)',
            'scalar_stationary_relation': '3*u^4+48*u^2-456=0',
            'kappa_applicability': {'F(2)': '83/56', 'upper_endpoint': '3/2'},
            'supplementary_signed_grid': {'count': count, 'minimum_nonzero_slack': minimum,
                                         'scope': 'Sanity check only; not proof of the centered inequality'}}


def check_generic_branch():
    """Universal formal row-sum and parity condition, no finite target model."""
    # Source rows j=0,1,2; spike at (0,1). For 3c outside {0,delta},
    # |k|<=1 gives k*3c+m*delta=0 exactly when k=0 and m is even.
    spike = INDEX[(0, 1)]
    retained = Counter()
    for x, y, z, w in QUADS:
        if (POINTS[x][1]+POINTS[y][1] == POINTS[z][1]+POINTS[w][1]
                and ((x == spike)+(y == spike)-(z == spike)-(w == spike)) % 2 == 0):
            retained[(POINTS[x][1]+POINTS[y][1]) % 3] += 1
    require(sorted(retained.values()) == [87, 87, 187], 'generic row-sum slice counts')
    require(sum(retained.values()) == 361, 'generic high-branch full indicator')
    require(Fraction(677, 1161)-Fraction(425, 729) == Fraction(4, 31347), 'runner-up difference')
    candidates = {'no_midpoint_line': Fraction(5, 9), 'generic_high': Fraction(361, 729),
                  'two_point': Fraction(665, 1161), 'cross_branch': Fraction(677, 1161),
                  'order_nine': Fraction(41, 81), 'aligned_cap': Fraction(425, 729),
                  'nonaligned_low': Fraction(139, 243), 'no_Q45': Fraction(409, 729)}
    require(max(candidates.values()) == Fraction(677, 1161), 'uniform plane runner-up bound')
    require(Fraction(677, 1161) < Fraction(7, 12), 'strict separator')
    return {'row_sum_residue_slices': [{'residue': i, 'retained': retained[i]} for i in range(3)],
            'E_a': 361, 'E': 729, 'ratio': '361/729',
            'outside_affine_cut_spike_witness_bounds': {name: str(value) for name, value in candidates.items()},
            'runner_up_bound': '677/1161', 'runner_up_minus_cap': '4/31347'}


# Columns of each displayed matrix generate the relation lattice in (v,b,c).
LATTICE_BASES = (
    ([[3,0,1],[0,3,1],[0,0,1]],690),
    ([[3,1],[0,-2],[0,1]],1),
    ([[3,1],[0,1],[0,1]],1),
    ([[3,2],[0,-1],[0,2]],1),
    ([[6,0,1],[0,3,1],[0,0,1]],3),
    ([[6,0,4],[0,3,1],[0,0,1]],27),
    ([[6,3,1],[0,3,1],[0,0,1]],3),
    ([[6,3,4],[0,3,1],[0,0,1]],3),
)


def lattice_problem():
    """Generate all conditions from the nine formal point values afresh."""
    formal = (((0,0,0),(1,0,0),(2,0,0)),
              ((0,1,0),(1,1,0),(2,1,0)),
              ((1,0,1),(2,0,1),(0,0,1)))
    triples = []
    for slope, start in product(range(3), repeat=2):
        triple = [formal[j][(start+slope*j) % 3] for j in range(3)]
        normalized = tuple(tuple(x-y for x,y in zip(row,triple[0])) for row in triple)
        if normalized not in triples:
            triples.append(normalized)
    require(len(triples) == 6, 'formal transversal coverage')
    return [[[3*triple[k][r]-sum(point[r] for point in triple) for r in range(3)]
             for k in range(3)] for triple in triples]


def _keys(value, keys, label):
    if type(value) is not dict or set(value) != set(keys):
        raise ValueError(label+' has missing, unknown, or malformed fields')


def verify_lattice_certificate(certificate):
    """Validate supplied integer certificates without trusting normal-form labels.

    Exact U*M=R and det(U)=+/-1 certify both lattice containments at once.
    Every choice, original generator, displayed basis, rank, and class count is
    independently checked. False, truncated, or duplicate records are rejected.
    """
    _keys(certificate, ('schema_version','method','bases','records'), 'certificate')
    if type(certificate['schema_version']) is not int or certificate['schema_version'] != 1:
        raise ValueError('unsupported certificate schema')
    if certificate['method'] != 'Integer U with determinant +/-1 and U times generators equal row-Hermite form':
        raise ValueError('unsupported certificate method')
    if type(certificate['bases']) is not list or len(certificate['bases']) != 8:
        raise ValueError('certificate needs eight basis reconstructions')
    if type(certificate['records']) is not list or len(certificate['records']) != 729:
        raise ValueError('certificate needs all 729 records')
    normals = []
    for entry, (claimed, _) in zip(certificate['bases'], LATTICE_BASES):
        _keys(entry, ('claimed_column_basis','transpose_generators','unimodular_U',
                      'U_times_generators','independent_row_basis'), 'basis reconstruction')
        column_basis = matrix(entry['claimed_column_basis'])
        require(column_basis == claimed, 'certificate displayed basis changed')
        generators = matrix(entry['transpose_generators'])
        require(generators == transpose(claimed), 'basis generators changed')
        u = matrix(entry['unimodular_U'])
        r = matrix(entry['U_times_generators'])
        normal = matrix(entry['independent_row_basis'])
        require(len(u) == len(u[0]) == len(generators), 'basis transformation dimensions')
        require(abs(determinant(u)) == 1, 'basis transformation is not unimodular')
        require(multiply(u, generators) == r == normal, 'basis transformation identity failed')
        require(tuple(map(tuple, normal)) == row_lattice(generators)[0], 'basis normal form changed')
        normals.append(normal)
    relations = lattice_problem()
    seen, counts, excluded = set(), Counter(), 0
    for record in certificate['records']:
        _keys(record, ('choice','basis_index','generators','U','R'), 'choice record')
        choice = record['choice']
        if (type(choice) not in (tuple, list) or len(choice) != 6
                or any(type(x) is not int or not 0 <= x <= 2 for x in choice)):
            raise ValueError('midpoint choice must have six integers in 0..2')
        choice = tuple(choice)
        require(choice not in seen, 'duplicate midpoint choice')
        seen.add(choice)
        index = record['basis_index']
        if type(index) is not int or not 0 <= index < 8:
            raise ValueError('invalid basis index')
        generators = matrix(record['generators'])
        require(generators == [relations[i][choice[i]] for i in range(6)], 'choice generators changed')
        u = matrix(record['U'])
        r = matrix(record['R'])
        require(len(u) == len(u[0]) == 6, 'choice transformation must be 6 by 6')
        require(abs(determinant(u)) == 1, 'choice transformation is not unimodular')
        expected_r = normals[index]+[[0,0,0]]*(6-len(normals[index]))
        require(multiply(u, generators) == r == expected_r, 'choice lattice identity failed')
        counts[index] += 1
        if member(normals[index], (3,0,0)):
            excluded += 1
        else:
            require(all(member(normals[index], vector) for vector in ((6,0,0),(0,6,0),(0,0,6))),
                    'surviving certificate does not force exponent six')
            require(any(member(normals[index], (-3*e,3,0)) for e in (0,1)), '3b not binary')
            require(any(member(normals[index], (-3*e,0,3)) for e in (0,1)), '3c not binary')
    require(seen == set(product(range(3), repeat=6)), 'incomplete midpoint coverage')
    require([counts[i] for i in range(8)] == [count for _, count in LATTICE_BASES], 'lattice class counts changed')
    require(excluded == 693, 'excluded lattice choice count')
    return {'records': 729, 'basis_reconstructions': 8, 'unimodular_identities': 737,
            'excluded_choices': excluded, 'surviving_choices': 729-excluded}


def jsonable(value):
    """Stable exact JSON encoding: fractions are strings; no binary floats."""
    if type(value) is Fraction:
        return str(value)
    if type(value) is dict:
        if not all(type(key) is str for key in value):
            raise ValueError('JSON dictionaries need string keys')
        return {key: jsonable(item) for key, item in value.items()}
    if type(value) in (list, tuple):
        return [jsonable(item) for item in value]
    if value is None or type(value) in (str, bool, int):
        return value
    raise ValueError('unsupported exact JSON value')


def canonical_bytes(value):
    return (json.dumps(jsonable(value), sort_keys=True, separators=(',', ':'), ensure_ascii=True)+'\n').encode('ascii')


def _unique_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('duplicate JSON key: '+key)
        result[key] = value
    return result


def _reject_constant(value):
    raise ValueError('nonfinite JSON constant is forbidden: '+value)


def load_certificate(path):
    """Read a bounded strict-JSON certificate; never write an input file."""
    if type(path) is not str and not isinstance(path, Path):
        raise ValueError('certificate path must be a string or Path')
    with Path(path).open('rb') as stream:
        data = stream.read(2_000_001)
    if len(data) > 2_000_000:
        raise ValueError('certificate exceeds the two-megabyte size bound')
    return json.loads(data.decode('utf-8'), object_pairs_hook=_unique_keys, parse_constant=_reject_constant)


def run_checks():
    upper, certificate = check_upper_bound()
    certificate = jsonable(certificate)
    replay = verify_lattice_certificate(certificate)
    path = Path(__file__).with_name('lattice_certificate.json')
    supplied = load_certificate(path)
    require(supplied == certificate, 'bundled certificate differs from fresh deterministic reconstruction')
    require(verify_lattice_certificate(supplied) == replay, 'bundled certificate replay changed')
    return {'report': 293, 'schema_version': 1, 'status': 'passed',
            'arithmetic': 'Python standard library; integers, rational coefficients, no numerical optimizer',
            'scope': 'Universal integer-lattice and polynomial-identity certificates; analytic inequalities and global gluing are proved in the report',
            'certificate': {**replay, 'canonical_sha256': sha256(canonical_bytes(certificate)).hexdigest()},
            'upper_bound': upper, 'generic_branch_and_plane_equality': check_generic_branch(),
            'spike_lower_bound': check_spike_lower_bound()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.parse_args(argv)
    print(json.dumps(jsonable(run_checks()), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
