#!/usr/bin/env python3
"""Fixed exact diagnostics for Report285. These finite tests are not universal proofs.

Circle phases are rational classes modulo one. Cyclotomic arithmetic is in actual
Q[z]/Phi_n(z), not the formal group algebra. Inequalities are checked only when
an evaluated real quantity reduces to a rational number. No coefficientwise
ordering, numerical roots, tolerance, external dependencies, or random tests.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb, factorial, prod
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).absolute().parents[1]
MAX_BITS = 2048
MAX_WORK = 200000


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bounded(value, low, high, name):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(name + ' outside its bounded integer domain')
    return value


def rational(value):
    if type(value) not in (int, Q):
        raise ValueError('an exact integer or Fraction is required')
    value = Q(value)
    if abs(value.numerator).bit_length() > MAX_BITS or value.denominator.bit_length() > MAX_BITS:
        raise ValueError('rational bit budget exceeded')
    return value


def constants(d):
    bounded(d, 2, 30, 'd')
    q = 2**d
    C = Q(6**d - 2*q*q + q, 8)
    A = Q(q*(q-1)*(q-2), 24)
    B = 10*comb(q, 5) + comb(q, 6) if q >= 6 else 0
    K0 = Q(q*(q-1), 8)
    Kstar = K0 + A
    Hstar = B + C
    c = Q(q, 2)
    rho_squared = min(Q(1, 4), (Q(q, 16)/(Kstar+1))**2,
                      Q(q, 8)/(B+2*C+1))
    R = 12*Kstar*Kstar/c**5 + 24*Kstar*Hstar/c**6 + 8*Hstar/c**4
    return dict(d=d, q=q, C=C, A=A, B=B, K0=K0, Kstar=Kstar,
                Hstar=Hstar, rho_squared=rho_squared, R=R,
                eta=Q(1) if d == 2 else Q(1, 180*10**(d-3)),
                epsilon_entry=Q(1, 10**d), radius_lower_squared=Q(1, q**5),
                b_odd=Q(3**d-1, 2*q*q), b_even=Q(q*q-1, 3*q*q))


class Group:
    """Small direct product of cyclic groups; tuple enumeration fixes all signs."""
    __slots__ = ('moduli', 'points', 'n', 'add', 'sub', 'neg')

    def __init__(self, moduli):
        if type(moduli) not in (tuple, list) or not 1 <= len(moduli) <= 3:
            raise ValueError('one to three cyclic moduli required')
        for modulus in moduli:
            bounded(modulus, 1, 32, 'cyclic modulus')
        if prod(moduli) > 32:
            raise ValueError('group order budget exceeded')
        self.moduli = tuple(moduli)
        self.points = tuple(product(*(range(m) for m in moduli)))
        self.n = len(self.points)
        index = {p: i for i, p in enumerate(self.points)}
        self.add = tuple(tuple(index[tuple((a+b) % m for a,b,m in zip(x,y,moduli))]
                               for y in self.points) for x in self.points)
        self.sub = tuple(tuple(index[tuple((a-b) % m for a,b,m in zip(x,y,moduli))]
                               for y in self.points) for x in self.points)
        self.neg = self.sub[0]


def group_input(group):
    if type(group) is not Group:
        raise ValueError('a bounded Group is required')
    return group


def phases(group, values):
    group_input(group)
    if type(values) not in (tuple, list) or len(values) != group.n:
        raise ValueError('one rational phase per group element required')
    return tuple(rational(v) % 1 for v in values)


def phase_derivative(group, values, h):
    values = phases(group, values)
    bounded(h, 0, group.n-1, 'increment index')
    return tuple((values[group.sub[x][h]]-values[x]) % 1 for x in range(group.n))


def phase_degree_at_most(group, values, degree):
    values = phases(group, values)
    bounded(degree, 0, 4, 'phase degree')
    if group.n**(degree+2) > MAX_WORK:
        raise ValueError('phase derivative work budget exceeded')
    level = {values}
    for _ in range(degree+1):
        level = {phase_derivative(group, f, h) for f in level for h in range(group.n)}
    return all(not any(f) for f in level)


def phase_rows(group, rows):
    group_input(group)
    if type(rows) not in (tuple, list) or len(rows) != group.n:
        raise ValueError('one derivative row per increment required')
    return tuple(phases(group, row) for row in rows)


def is_cocycle(group, rows):
    rows = phase_rows(group, rows)
    return all((rows[group.add[h][t]][x]-rows[t][group.sub[x][h]]-rows[h][x]) % 1 == 0
               for h,t,x in product(range(group.n), repeat=3))


def integrate_cocycle(group, rows):
    """Integrate T_h p / p using p(x)=q_{-x}(0); reject non-cocycles."""
    rows = phase_rows(group, rows)
    if not is_cocycle(group, rows):
        raise ValueError('exact translation cocycle required')
    answer = tuple(rows[group.neg[x]][0] for x in range(group.n))
    require(all(phase_derivative(group, answer, h) == rows[h] for h in range(group.n)),
            'backward-translation integration identity')
    return answer


def correct_small_cocycle(group, rows):
    """Correct constant lifted defects with +b(h), not -b(h).

    The <=1/6 guard is the exact real-lift domain in the proof. This routine
    checks the premises; it does not find the approximate derivative phases.
    """
    rows = phase_rows(group, rows)
    lifted = []
    for h in range(group.n):
        row = []
        for t in range(group.n):
            defect = tuple((rows[group.add[h][t]][x]-rows[t][group.sub[x][h]]-rows[h][x]) % 1
                           for x in range(group.n))
            if len(set(defect)) != 1:
                raise ValueError('cocycle defects must be constant in x')
            value = (defect[0]+Q(1,2)) % 1-Q(1,2)
            if abs(value) > Q(1,6):
                raise ValueError('principal cocycle lift exceeds 1/6')
            row.append(value)
        lifted.append(tuple(row))
    lifted = tuple(lifted)
    for h,t,u in product(range(group.n), repeat=3):
        require(lifted[h][t]+lifted[group.add[h][t]][u]
                -lifted[h][group.add[t][u]]-lifted[t][u] == 0,
                'small principal lifts satisfy the real cocycle identity')
    b = tuple(sum(row, Q(0))/group.n for row in lifted)
    require(all(lifted[h][t] == b[h]+b[t]-b[group.add[h][t]]
                for h,t in product(range(group.n), repeat=2)), 'averaged real coboundary')
    corrected = tuple(tuple((a+b[h]) % 1 for a in rows[h]) for h in range(group.n))
    return dict(lift=lifted, b=b, corrected=corrected,
                integrated=integrate_cocycle(group, corrected))


# Monic cyclotomic polynomials, coefficients in ascending order.
PHI = {2:(1,1), 3:(1,1,1), 4:(1,0,1), 5:(1,1,1,1,1),
       6:(1,-1,1), 8:(1,0,0,0,1), 12:(1,0,-1,0,1),
       24:(1,0,0,0,-1,0,0,0,1)}


class Cyclo:
    """Exact cyclotomic field elements; intentionally no ordering operation."""
    __slots__ = ('n', 'a')

    def __init__(self, n, coefficients=()):
        if type(n) is not int or n not in PHI:
            raise ValueError('unsupported cyclotomic conductor')
        if type(coefficients) not in (tuple, list) or len(coefficients) > 48:
            raise ValueError('bounded exact coefficient sequence required')
        a = [rational(c) for c in coefficients]
        p = PHI[n]; degree = len(p)-1
        for j in range(len(a)-1, degree-1, -1):
            value = a[j]
            for i in range(degree):
                if p[i]:
                    a[j-degree+i] -= value*p[i]
        a = a[:degree] + [Q(0)]*max(0, degree-len(a))
        self.n = n
        self.a = tuple(rational(c) for c in a)

    def coerce(self, other):
        if type(other) in (int, Q):
            return Cyclo(self.n, (other,))
        if type(other) is not Cyclo or other.n != self.n:
            raise ValueError('same conductor or exact scalar required')
        return other

    def __add__(self, other):
        other = self.coerce(other)
        return Cyclo(self.n, tuple(a+b for a,b in zip(self.a, other.a)))

    __radd__ = __add__

    def __neg__(self):
        return Cyclo(self.n, tuple(-a for a in self.a))

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        a = [Q(0)]*(2*len(self.a)-1)
        for i,x in enumerate(self.a):
            if x:
                for j,y in enumerate(other.a):
                    if y:
                        a[i+j] += x*y
        return Cyclo(self.n, a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = rational(other)
        if not other:
            raise ValueError('nonzero exact scalar required')
        return Cyclo(self.n, tuple(a/other for a in self.a))

    def __eq__(self, other):
        if type(other) in (int, Q):
            other = Cyclo(self.n, (other,))
        return type(other) is Cyclo and self.n == other.n and self.a == other.a

    def conjugate(self):
        return sum((c*root(self.n, -j) for j,c in enumerate(self.a) if c), Cyclo(self.n))

    def norm_square(self):
        return self*self.conjugate()

    def rational_real(self):
        if any(self.a[1:]):
            raise ValueError('evaluated quantity is not rational; no formal positivity inference')
        return self.a[0]

    def serialized(self):
        return [str(a) for a in self.a]


def root(n, exponent):
    if type(n) is not int or n not in PHI:
        raise ValueError('unsupported cyclotomic conductor')
    bounded(exponent, -1000000, 1000000, 'root exponent')
    return Cyclo(n, [0]*(exponent % n)+[1])


def evaluated_phases(group, values, conductor):
    values = phases(group, values)
    if type(conductor) is not int or conductor not in PHI:
        raise ValueError('unsupported cyclotomic conductor')
    if any((v*conductor).denominator != 1 for v in values):
        raise ValueError('phase denominator does not divide conductor')
    return tuple(root(conductor, int(v*conductor)) for v in values)


def values_input(group, values):
    group_input(group)
    if (type(values) not in (tuple, list) or len(values) != group.n
            or any(type(v) is not Cyclo for v in values)):
        raise ValueError('one cyclotomic value per group element required')
    if len({v.n for v in values}) != 1:
        raise ValueError('values must have a common conductor')
    return tuple(values)


def cube_budget(group, d, polynomial=False):
    group_input(group)
    bounded(d, 1, 4, 'cube order')
    if type(polynomial) is not bool:
        raise ValueError('polynomial flag must be bool')
    if group.n**(d+1)*2**(d*(2 if polynomial else 1)) > MAX_WORK:
        raise ValueError('cube work budget exceeded')


def cube_indices(group, d):
    cube_budget(group, d)
    vertices = tuple(product((0,1), repeat=d))
    for x in range(group.n):
        for increments in product(range(group.n), repeat=d):
            indices = []
            for omega in vertices:
                y = x
                for bit,h in zip(omega, increments):
                    if bit:
                        y = group.sub[y][h]
                indices.append((y, sum(omega) % 2))
            yield tuple(indices)


def cube_average(group, values, d):
    values = values_input(group, values)
    cube_budget(group, d)
    total = Cyclo(values[0].n)
    for cube in cube_indices(group, d):
        term = Cyclo(values[0].n, (1,))
        for x,parity in cube:
            term *= values[x].conjugate() if parity else values[x]
        total += term
    return total/group.n**(d+1)


def derivative_values(group, values, h):
    values = values_input(group, values)
    bounded(h, 0, group.n-1, 'increment index')
    return tuple(values[group.sub[x][h]]*values[x].conjugate() for x in range(group.n))


def mean(values):
    if (type(values) not in (tuple, list) or not 1 <= len(values) <= 32
            or any(type(v) is not Cyclo for v in values)
            or len({v.n for v in values}) != 1):
        raise ValueError('nonempty bounded common-conductor values required')
    return sum(values, Cyclo(values[0].n))/len(values)


def fourier(group, values):
    values = values_input(group, values)
    n = values[0].n
    if any(n % m for m in group.moduli):
        raise ValueError('character denominators must divide conductor')
    return tuple(sum((values[j]*root(n, -sum(a*b*(n//m) for a,b,m
                         in zip(frequency,x,group.moduli)))
                     for j,x in enumerate(group.points)), Cyclo(n))/group.n
                 for frequency in group.points)


def cube_coefficients(group, values, d):
    """Exact coefficients of U_d(m+t(F-m)), retaining real t conjugation."""
    values = values_input(group, values)
    cube_budget(group, d, polynomial=True)
    m = mean(values).rational_real()
    r = tuple(v-m for v in values)
    zero = Cyclo(values[0].n)
    total = [zero]*(2**d+1)
    for cube in cube_indices(group, d):
        coefficients = [Cyclo(values[0].n, (1,))]
        for x,parity in cube:
            residual = r[x].conjugate() if parity else r[x]
            new = [zero]*(len(coefficients)+1)
            for j,coefficient in enumerate(coefficients):
                new[j] += coefficient*m
                new[j+1] += coefficient*residual
            coefficients = new
        total = [a+b for a,b in zip(total, coefficients)]
    return tuple(a/group.n**(d+1) for a in total)


def convex_certificate(group, values, d):
    values = values_input(group, values)
    bounded(d, 2, 4, 'convex cube order')
    cube_budget(group, d, polynomial=True)
    m = mean(values).rational_real()
    norms = tuple(z.norm_square().rational_real() for z in values)
    if not Q(1,2) <= m <= 1 or any(not 0 <= a <= 1 for a in norms):
        raise ValueError('unit disk values with real mean at least 1/2 required')
    v = sum(((z-m).norm_square().rational_real() for z in values), Q(0))/group.n
    a = 1-sum(norms, Q(0))/group.n
    coefficients = tuple(z.rational_real() for z in cube_coefficients(group, values, d))
    q = 2**d
    require(coefficients[0] == m**q and not any(coefficients[1:4]),
            'centered Taylor coefficients through degree three')
    require(sum(coefficients, Q(0)) == cube_average(group, values, d).rational_real(),
            'Taylor polynomial agrees with independently evaluated cube')
    fifth = coefficients[5] if q >= 5 else Q(0)
    tail = sum(coefficients[6:], Q(0))
    choose6 = comb(q,6) if q >= 6 else 0
    choose5 = comb(q,5) if q >= 5 else 0
    require(abs(fifth) <= 10*choose5*(v+a)*v*v, 'fifth real cancellation')
    require(abs(tail) <= choose6*v**3, 'convex sixth-order remainder')
    for t in (Q(0), Q(1,2), Q(1)):
        derivative = sum((coefficients[j]*Q(factorial(j),factorial(j-6))*t**(j-6)
                          for j in range(6,q+1)), Q(0))
        require(abs(derivative) <= factorial(6)*choose6*v**3,
                'sixth derivative bound at fixed rational interpolation samples')
        require(all(((1-t)*m+t*z).norm_square().rational_real() <= 1 for z in values),
                'interpolated values stay in the disk')
    integral = sum((coefficients[j]*Q(factorial(j), factorial(j-6)*factorial(5))
                    *Q(factorial(j-6)*factorial(5), factorial(j))
                    for j in range(6,q+1)), Q(0))
    require(integral == tail, 'integral Taylor normalization at t=0')
    remainder = fifth+tail
    require(abs(remainder) <= constants(d)['B']*(v+a)*v*v, 'improved centered expansion')
    return dict(d=d, group=list(group.moduli), m=m, v=v, a=a,
                coefficients=coefficients, fifth=fifth, tail=tail, remainder=remainder)


def check_constants():
    rows = []
    for d in range(2,31):
        row = constants(d); q = row['q']; C = row['C']; A = row['A']; B = row['B']
        K = row['Kstar']; H = row['Hstar']; eta = row['eta']; entry = row['epsilon_entry']
        require(0 <= C <= A <= comb(q,4), 'circuit count bounds')
        require(K == Q(q*(q*q-1),24), 'even quadratic coefficient identity')
        require(row['K0']+C/2 == Q(q*(3**d-1),16), 'odd quadratic coefficient identity')
        require(8*(row['K0']+C/2)/q**3 == row['b_odd'], 'odd b coefficient')
        require(8*K/q**3 == row['b_even'], 'even b coefficient')
        require(K+1 <= Q(q**3,12), 'sharp elementary K radius bound')
        require(B+2*C+1 <= Q(4381,184320)*q**6 < Q(q**6,40), 'sixth-order radius bound')
        require(H < Q(q**6,40), 'cubic constant bound')
        require(row['rho_squared'] >= Q(1,q**5), 'radius at least q^(-5/2), squared')
        require(row['R'] < 3*q**3, 'simple cubic coefficient')
        require(entry <= eta/2, 'global entry threshold admissible')
        if d >= 3:
            require(entry/(eta/2) == Q(9,25), 'entry to induction threshold ratio')
            require(10*eta <= constants(d-1)['eta'], 'induction threshold recurrence')
            require(180*eta <= Q(1,4**(d-3)) < Q(2,4**(d-3)), 'strict separation margin')
        if d >= 4:
            require(36 <= Q(25,8)**d and (6*entry)**2 <= Q(1,q**5), 'high-degree local entry')
        else:
            expected = Q(1,14 if d == 2 else 44)
            require(row['rho_squared'] == expected**2 and 6*entry <= expected,
                    'low-degree entry uses the exact radius')
            require((6*entry)**2 > Q(1,q**5), 'low-degree exception cannot use generic radius')
        rows.append(row)
    require(Q(4,5)*Q(5,2) == 2, 'restricted-average normalization')
    return rows


def _determinant3(rows):
    a,b,c = rows
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])


def check_cube_geometry():
    rows = []
    for d in range(2,6):
        vertices = tuple(product((0,1), repeat=d))
        triples = 0
        for triple in combinations(vertices,3):
            matrix = tuple((1,)+v for v in triple)
            require(any(abs(_determinant3(tuple(tuple(row[j] for j in columns) for row in matrix))) == 1
                        for columns in combinations(range(d+1),3)), 'unimodular triple minor')
            triples += 1
        ordinary = xor = 0
        for a,b,c,e in combinations(vertices,4):
            xor += all((x+y+z+w) % 2 == 0 for x,y,z,w in zip(a,b,c,e))
            ordinary += any(all(x+y == z+w for x,y,z,w in zip(u,v,s,t))
                            for u,v,s,t in ((a,b,c,e),(a,c,b,e),(a,e,b,c)))
        expected = constants(d)
        require(ordinary == expected['C'] and xor == expected['A'], 'quartic circuit census')
        rows.append(dict(d=d, triples=triples, ordinary=ordinary, xor_zero=xor))
    laws = []
    for moduli in ((2,), (3,), (4,), (2,2), (2,3)):
        group = Group(moduli); d = 3
        triples = tuple(combinations(range(8),3))
        counts = [dict() for _ in triples]
        for cube in cube_indices(group,d):
            for counts_row,triple in zip(counts,triples):
                key = tuple(cube[i][0] for i in triple)
                counts_row[key] = counts_row.get(key,0)+1
        require(all(len(row) == group.n**3 and set(row.values()) == {group.n} for row in counts),
                'all three-vertex joint laws, including even and mixed groups')
        laws.append(dict(group=list(moduli), triples=len(triples), outputs_each=group.n**3,
                         multiplicity=group.n))
    return dict(unimodular_and_circuit_census=rows, exact_joint_laws=laws)


def check_cocycles():
    examples = (((2,),2,4), ((2,),3,8), ((4,),2,8), ((2,2),2,4), ((2,3),2,12), ((2,4),2,8))
    rows = []
    for moduli,degree,conductor in examples:
        group = Group(moduli)
        if moduli == (2,):
            phase = tuple(Q(x[0],2**degree) for x in group.points)
        elif moduli == (4,):
            phase = tuple(Q(x[0]**2,8) for x in group.points)
        elif moduli == (2,2):
            phase = tuple(Q(x[0],4)+Q(x[0]*x[1],2) for x in group.points)
        elif moduli == (2,3):
            phase = tuple(Q(x[0],4)+Q(x[1]**2,3) for x in group.points)
        else:
            phase = tuple(Q(x[0]*x[1],2)+Q(x[1]**2,8) for x in group.points)
        phase = phases(group, phase)
        require(phase_degree_at_most(group,phase,degree), 'polynomial phase degree')
        require(not phase_degree_at_most(group,phase,degree-1), 'phase has the stated exact degree')
        exact = tuple(phase_derivative(group,phase,h) for h in range(group.n))
        require(integrate_cocycle(group,exact) == phase, 'exact cocycle integration')
        theta = tuple(Q(h+1,48*group.n) for h in range(group.n))
        approximate = tuple(tuple((a+theta[h]) % 1 for a in exact[h]) for h in range(group.n))
        corrected = correct_small_cocycle(group,approximate)
        require(corrected['b'] == tuple(-t for t in theta), 'averaged correction sign')
        require(corrected['corrected'] == exact and corrected['integrated'] == phase,
                'small-cocycle correction and integration')
        wrong = tuple(tuple((a-corrected['b'][h]) % 1 for a in approximate[h]) for h in range(group.n))
        require(not is_cocycle(group,wrong), 'wrong correction sign is detected')
        actual = evaluated_phases(group,phase,conductor)
        require(all(z.norm_square() == 1 for z in actual), 'phases are actual unit cyclotomic values')
        rows.append(dict(group=list(moduli), exact_degree=degree, conductor=conductor,
                         phase=phase, maximum_lift=max(abs(c) for row in corrected['lift'] for c in row),
                         wrong_sign_rejected=True))
    return rows


def check_good_set():
    rows = []
    for moduli in ((20,), (4,5)):
        group = Group(moduli)
        for special in (0,7,19):
            defects = tuple(Q(1,200) if h == special else Q(h%3,100000) for h in range(group.n))
            delta = sum(defects,Q(0))/group.n
            good = tuple(h for h in range(group.n) if defects[h] <= 10*delta)
            require(10*len(good) >= 9*group.n, 'good-set density')
            witnesses = []
            for h in range(group.n):
                if h in good:
                    continue
                pairs = tuple((a,group.sub[h][a]) for a in good if group.sub[h][a] in good)
                restricted = sum((defects[a]+defects[b] for a,b in pairs),Q(0))/len(pairs)
                require(5*len(pairs) >= 4*group.n and restricted <= Q(5,2)*delta,
                        'restricted good-set average')
                pair = min(pairs, key=lambda pair: defects[pair[0]]+defects[pair[1]])
                bound = 4*(defects[pair[0]]+defects[pair[1]])
                require(bound <= 10*delta < defects[h], 'extension fidelity loss')
                witnesses.append(dict(h=h, pair=list(pair), error_bound=bound))
            rows.append(dict(group=list(moduli), delta=delta, good_count=len(good), witnesses=witnesses))
    return rows


def check_fourier_and_stability():
    cases = []
    for moduli,conductor in (((2,),4),((3,),3),((4,),4),((2,2),4)):
        group = Group(moduli)
        values = tuple(root(conductor,(j*j+j) % conductor) for j in range(group.n))
        energies = tuple(z.norm_square().rational_real() for z in fourier(group,values))
        q2 = cube_average(group,values,2).rational_real()
        require(sum(energies,Q(0)) == 1, 'unit Parseval')
        require(sum((e*e for e in energies),Q(0)) == q2 <= max(energies), 'base fidelity')
        cases.append(dict(group=list(moduli), Q2=q2, maximum_fidelity=max(energies)))
    near = []
    for degree in (1,2,3):
        group = Group((2,)); k = degree+1; conductor = 4 if degree == 1 else 2**degree
        phase = (Q(0),Q(1,2**degree))
        target = evaluated_phases(group,phase,conductor)
        N = 1000
        real = Q(N*N-1,N*N+1); imag = Q(2*N,N*N+1)
        i = root(conductor,conductor//4)
        unit = (target[0]*(real+imag*i),target[1]*(real-imag*i))
        amplitude = Q(999999,1000000)
        values = tuple(amplitude*z for z in unit)
        qk = cube_average(group,unit,k).rational_real()
        fidelity = mean(tuple(z*p.conjugate() for z,p in zip(unit,target))).norm_square().rational_real()
        require(fidelity >= qk, 'unit near-polynomial fidelity witness')
        epsilon = 1-cube_average(group,values,k).rational_real()
        distance = sum(((z-p).norm_square().rational_real() for z,p in zip(values,target)),Q(0))/group.n
        coefficient = constants(k)
        require(0 <= epsilon <= coefficient['epsilon_entry'], 'near example meets main threshold')
        bound = Q(2,2**k)*epsilon+coefficient['b_even']*epsilon**2+3*(2**k)**3*epsilon**3
        require(distance <= bound, 'main phase-distance inequality on exact witnesses')
        recursive = sum((cube_average(group,derivative_values(group,unit,h),k-1).rational_real()
                         for h in range(group.n)),Q(0))/group.n
        require(recursive == qk, 'Gowers derivative recursion with backward sign')
        near.append(dict(group=[2], degree=degree, Qk=qk, fidelity=fidelity,
                         epsilon=epsilon, distance=distance, main_bound=bound))
    return dict(parseval_cases=cases, exact_near_extremizers=near)


def check_polar():
    rows = []
    for moduli in ((3,), (2,2), (2,3)):
        group = Group(moduli)
        amplitudes = tuple((Q(0),Q(1,2),Q(1))[j%3] for j in range(group.n))
        unit = tuple(Cyclo(4,(1,)) if not a else root(4,j) for j,a in enumerate(amplitudes))
        values = tuple(a*z for a,z in zip(amplitudes,unit))
        for j,(a,z,f) in enumerate(zip(amplitudes,unit,values)):
            target = root(4,2*j+1)
            actual = (f-target).norm_square().rational_real()
            unit_distance = (z-target).norm_square().rational_real()
            require(actual == a*unit_distance+(1-a)**2 <= unit_distance+1-a,
                    'pointwise polar distance identity including zero amplitudes')
        rho = tuple(Cyclo(4,(a,)) for a in amplitudes)
        for k in (2,3):
            qf = cube_average(group,values,k).rational_real()
            qv = cube_average(group,unit,k).rational_real()
            qrho = cube_average(group,rho,k).rational_real()
            epsilon = 1-qf
            require(0 <= qf <= qrho <= 1 and 0 <= qv <= 1, 'actual real cube positivity')
            require(abs(qv-qf) <= 1-qrho <= epsilon and 1-qv <= 2*epsilon,
                    'dimension-free polar defect including zeros')
            amplitude_loss = 1-sum((a*a for a in amplitudes),Q(0))/group.n
            require(amplitude_loss <= epsilon, 'pairwise amplitude deficit')
            require(qf <= (sum(amplitudes,Q(0))/group.n)**2, 'two-vertex amplitude bound')
            rows.append(dict(group=list(moduli), k=k, zero_count=amplitudes.count(Q(0)),
                             Qf=qf, Qv=qv, Qrho=qrho, epsilon=epsilon, amplitude_loss=amplitude_loss))
    return rows


def check_convex():
    i = root(4,1)
    cases = ((Group((2,)), (Q(3,5)+Q(4,5)*i,Q(3,5)-Q(4,5)*i), (2,3,4)),
             (Group((3,)), (Cyclo(4,(1,)),Q(3,5)+Q(4,5)*i,Q(3,5)-Q(4,5)*i), (2,3)),
             (Group((2,2)), (Cyclo(4,(1,)),Q(4,5)+Q(3,5)*i,Q(4,5)-Q(3,5)*i,Cyclo(4)), (2,3)))
    rows = [convex_certificate(group,values,d) for group,values,degrees in cases for d in degrees]
    require(any(row['tail'] for row in rows), 'nonzero sixth-order remainder tested')
    require(any(row['fifth'] for row in rows), 'nonzero fifth-order cancellation tested')
    require(any(row['a'] for row in rows), 'nonunit disk input tested')
    return rows


def check_fifth_conjugations():
    group = Group((3,)); i = root(4,1)
    values = (Cyclo(4,(1,)), Q(3,5)+Q(4,5)*i, Q(3,5)-Q(4,5)*i)
    m = mean(values).rational_real()
    residual = tuple(z-m for z in values)
    v = sum((z.norm_square().rational_real() for z in residual),Q(0))/group.n
    vertices = (0,1,2,4,7)
    totals = [Cyclo(4) for _ in range(32)]
    conjugations = tuple(product((0,1),repeat=5))
    for cube in cube_indices(group,3):
        for j,bits in enumerate(conjugations):
            term = Cyclo(4,(1,))
            for vertex,bit in zip(vertices,bits):
                value = residual[cube[vertex][0]]
                term *= value.conjugate() if bit else value
            totals[j] += term
    real_parts = tuple(((z+z.conjugate())/(2*group.n**4)).rational_real() for z in totals)
    bound = 5*v**3/m
    require(all(abs(value) <= bound for value in real_parts), 'fifth moment with every conjugation choice')
    require(any(real_parts), 'fifth-moment witness is nonzero')
    return dict(group=[3],d=3,vertices=list(vertices),conjugation_choices=32,
                maximum_absolute_real=max(abs(value) for value in real_parts),bound=bound)


def check_sources():
    expected = [
        dict(name='source55_article.tex', kind='archive_member', bytes=60317,
             repository='VladimirReshetnikov/ProveIt',
             repository_path='docs/incoming/gowers_endpoint_stability.zip',
             commit='f8bc5e2ec281fcee02c0fc5ef717a775ee7e4442',
             sha256='6ec4106b68121b6d190dd2b37ab1a27a216981bf5442b68c3cbe00c0cde24128',
             archive_member='gowers_endpoint_stability/article.tex', archive_bytes=348065,
             archive_git_blob_sha1='9a478ac4f39121017eacec0213d5059351cb6ab2',
             archive_sha256='022c17045d35e85e155048831e1bec7c2912e4e8aa007099aca9c19c5102d17d'),
        dict(name='source55_audit.md', kind='git_blob', bytes=5894,
             repository='VladimirReshetnikov/ProveIt',
             repository_path='Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/55-endpoint-stability-SOURCE_AUDIT.md',
             commit='e40138bd546c7445f12b7ceb59dafb7885848eaa',
             sha256='efe06b0abb6619a35cc9bfff3ffe3ba5fbbd07c472dd6a1a2eb2bbc7fcb31952',
             git_blob_sha1='60fd39f876da6e7692f1a656832757b518add802')]
    for row in expected:
        row['url'] = 'https://github.com/'+row['repository']+'/blob/'+row['commit']+'/'+row['repository_path']
    data = (ROOT/'provenance/source_manifest.json').read_bytes()
    require(len(data) <= 16384, 'source manifest size')
    manifest = json.loads(data)
    require(manifest == expected, 'pinned source identity and manifest metadata')
    for row in expected:
        data = (ROOT/'provenance/sources'/row['name']).read_bytes()
        require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'],
                'pinned source snapshot bytes')
        if row['kind'] == 'git_blob':
            require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == row['git_blob_sha1'],
                    'pinned raw audit git blob')
        else:
            require(all(label in data for label in (b'\\label{q:entry}', b'\\label{thm:local}', b'\\label{lem:fifth}')),
                    'prior local theorem and entry-question labels')
    return dict(snapshots=2, exact_snapshot_sha256=True, raw_audit_git_blob_verified=True,
                archive_identity_pinned_in_manifest=True,
                boundary='The archive itself is not bundled or rehashed offline; its extracted member is pinned and rehashed.')


def serialized(value):
    if type(value) is Q:
        return str(value)
    if type(value) is dict:
        return {k:serialized(v) for k,v in value.items()}
    if type(value) in (tuple,list):
        return [serialized(v) for v in value]
    if type(value) in (str,int,bool) or value is None:
        return value
    raise ValueError('unsupported JSON diagnostic value')


def run_all():
    return serialized(dict(status='PASS', report=285,
        scope='Fixed finite exact diagnostics only. Universal proofs are in article.tex; no formal positivity inference.',
        constants=check_constants(), cube_geometry=check_cube_geometry(),
        cocycle_integration=check_cocycles(), good_set=check_good_set(),
        fourier_and_stability=check_fourier_and_stability(), polar=check_polar(), convex=check_convex(),
        fifth_conjugations=check_fifth_conjugations(), sources=check_sources()))


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if type(argv) not in (tuple,list) or argv:
        raise SystemExit('No command-line parameters are accepted; workloads are fixed and bounded.')
    print(json.dumps(run_all(),indent=2,sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
