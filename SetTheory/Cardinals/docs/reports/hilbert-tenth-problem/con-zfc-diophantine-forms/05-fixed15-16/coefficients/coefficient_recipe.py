"""Exact finite coefficient recipe for the normalized K215 window system.

The default run writes a compact *definition* of the fixed integers. It does
not expand the astronomically long binary integers R, B, DC, MC, or MF.
`materialize_for_windows` is a literal finite integer algorithm for the same
recipe; `materialize_k215` specifies its full input with no free parameter.
"""
from collections import defaultdict
from itertools import product
from pathlib import Path
import json
from fixed_machine import Machine, allowed_windows, count_windows, tile_alphabet, require

HERE = Path(__file__).resolve().parent


def five_ceiling(n):
    v = 1
    while v < n:
        v *= 5
    return v


def geometry(k, a):
    # A is the clause radix; R is the later, much larger native-cell radix.
    ell = 4*((max(2,(k+1).bit_length())+3)//4)
    A = 1 << ell
    J0 = 9*a+4
    m0 = 2*ell+30*a+8
    padding = max(0,(k+9*a+5-(m0+1)+1)//2)
    J = J0+padding
    m = m0+2*padding
    K = m+1
    dummy_count = K-k-9*a-4
    require(dummy_count >= 1, 'at least one ignored native dummy')
    dummy0 = k+12*a
    M = dummy0+dummy_count+3*a
    anchors = [M,3*M,9*M,27*M]
    E = anchors[-1]
    H = E+24*M+3*a+1
    T1 = H+2*E+a+1
    T2 = T1+2*E+1
    g = T2+E+1
    L = five_ceiling(g+E+1)
    # Each nonzero coefficient c_e <= 14*A^J and there are ncoeff of them.
    # mu < A^(J+1). This deliberately generous exact bound avoids expanding
    # a number with approximately k/2 radix-A digits merely to size R.
    ncoeff = k+9*a+4
    guard = 128*(K+2)*ncoeff+16
    b = five_ceiling(ell*(J+2)+guard.bit_length())
    d = b*L
    require(A > k+1 and ell % 4 == 0, 'clause radix bound and congruence')
    require(L > g+E and b >= ell*(J+2)+guard.bit_length(), 'native radix and separation')
    return dict(k=k,a=a,ell=ell,A=A,J0=J0,padding=padding,J=J,m=m,K=K,
                dummy_count=dummy_count,dummy0=dummy0,M=M,anchors=anchors,
                E=E,H=H,T1=T1,T2=T2,g=g,L=L,b=b,d=d,guard=guard,
                twice_cell_bits=2*d,inner_bits=b,marker_exponent=2*d+b)


def payload_position(g, r, c, s):
    return g['k']+3*g['a']+(2-r)*3*g['a']+(2-c)*g['a']+s


def materialize_for_windows(windows,a):
    """Exact integer compiler; intentionally impractical for the full K215 set.

    All exponentiations here are of fixed integers while *constructing the
    coefficients*, never exponentiation of Diophantine unknowns.
    """
    windows = tuple(tuple(w) for w in windows)
    k = len(windows)
    require(k >= 2 and len(set(windows)) == k, 'two distinct marked windows')
    require(all(len(w) == 9 and all(0 <= s < a for s in w) for w in windows), 'window type')
    g = geometry(k,a)
    A = g['A']
    coeff = {i:1 for i in range(k)}
    for r,c,s in product(range(3),range(3),range(a)):
        j = 1+(3*r+c)*a+s
        value = A**j
        coeff[payload_position(g,r,c,s)] = value
        for i,w in enumerate(windows):
            if w[3*r+c] == s:
                coeff[i] += value
    for j,e in enumerate(g['anchors'],9*a+1):
        value = A**j
        coeff[e] = value
        for i in range(k):
            coeff[i] += value
    mu = A-2+sum(A**j for j in range(1,g['J']+1))
    payloads = [payload_position(g,r,c,s) for r,c,s in product(range(3),range(3),range(a))]
    positions = list(range(k))+payloads+list(range(g['dummy0'],g['dummy0']+g['dummy_count']))+g['anchors']
    DCpoly = defaultdict(int)
    for e in (3*a,g['H']+a,8*g['M'],24*g['M']):
        DCpoly[e] += 1
    for e,value in coeff.items():
        DCpoly[g['T1']-e] += value
        DCpoly[g['T2']-e] += value
    dcmod = sum(value*pow(2,e,5) for e,value in DCpoly.items())%5
    epsilon = int((2*dcmod-pow(2,g['H'],5))%5 == 0)
    if epsilon:
        DCpoly[g['g']] += 1
    MFpoly = defaultdict(int,{g['T1']:mu,g['T2']:mu})
    for r,c,s in product(range(2),range(3),range(a)):
        MFpoly[payload_position(g,r,c,s)] += 1
    for r,c,s in product(range(3),range(2),range(a)):
        MFpoly[g['H']+payload_position(g,r,c,s)] += 1
    for e in g['anchors'][2:]:
        MFpoly[e] += 1
    MFpoly[0] += 4
    require(len(set(positions)) == len(positions) == g['K'], 'native-position cardinality')
    require(g['m'] == 2*mu.bit_count()+12*a+2, 'mask population')
    # Actual source bounds. These are not assumptions on Diophantine variables.
    R,B = 1 << g['b'], 1 << g['d']
    require(R >= max(4*(g['K']+2)*(2*sum(coeff.values())+6)+8,2*mu+4,16), 'radix margin')
    DC = sum(v*R**e for e,v in DCpoly.items())
    DR = R**g['H']
    MC = B-1-sum(R**e for e in positions if e != 1)-2*R**g['dummy0']
    MF = sum(v*R**e for e,v in MFpoly.items())
    require(0 < MC < B-1 and 0 < MF < B-1 and MC%2 == 0 and MF%8 == 4, 'mask range')
    require(MC.bit_count()+MF.bit_count() == g['d'], 'modified mask population')
    require((2*DC-DR)%5 != 0, 'five-adic unit')
    return dict(Bm1=B-1,Kconstant=DC+B*DR,twice_cell_bits=2*g['d'],inner_bits=g['b'],
                MC=MC,MF=MF+B-1,W0=R*B*B,W0plus2d=R*B*B+2*g['d'],
                geometry=g,high_correction=epsilon)


def materialize_k215():
    """A terminating, wholly specified coefficient algorithm, not run in this packet."""
    machine = Machine()
    return materialize_for_windows(allowed_windows(machine),len(tile_alphabet(machine)))


def specification():
    machine = Machine()
    a = len(tile_alphabet(machine))
    k,crosses = count_windows(machine)
    g = geometry(k,a)
    # For this actual alphabet the expensive high-term choice is known exactly.
    # A=1 (mod5), selector coefficients=14 (mod5), other coefficients=1.
    # Selector and payload ranges have lengths divisible by4; anchor exponents
    # are M,3M,9M,27M with M=1(mod4), hence their weighted sums vanish mod5.
    require(k%4 == a%4 == 0 and g['dummy_count'] == 1 and g['M']%4 == 1, 'modular simplification premises')
    require(g['H']%4 == 0, 'DR residue')
    dcmod = sum(pow(2,e,5) for e in (3*a,g['H']+a,8*g['M'],24*g['M']))%5
    require(dcmod == 4 and (2*dcmod-1)%5 == 2, 'exact optional-term exclusion')
    return dict(geometry=g,admissible_crosses=crosses,native_sha256=machine.native_sha256,
                high_correction=0,DC_mod5=4,DR_mod5=1,unit_mod5=2,
                definitions={
                    'A':'2^ell', 'R':'2^b', 'B':'2^d',
                    'windows':'W_0=Start, W_1=End, then all other local_valid windows in lexicographic tile-index order',
                    'p(r,c,s)':'k+3a+(2-r)3a+(2-c)a+s; r,c=0,1,2; s=0,...,a-1',
                    'j(r,c,s)':'1+(3r+c)a+s',
                    'c_i':'1 + sum_(r,c) A^(1+(3r+c)a+W_i[3r+c]) + sum_(l=1..4) A^(9a+l); 0<=i<k',
                    'c_p(r,c,s)':'A^j(r,c,s)',
                    'c_anchor_l':'A^(9a+l); anchor_l=(1,3,9,27)_l*M',
                    'c_else':'0',
                    'mu':'A-2 + sum_(j=1..J) A^j',
                    'E_native':'{0,...,k-1} union {p(r,c,s)} union {dummy0} union {M,3M,9M,27M}',
                    'DC':'R^(3a)+R^(H+a)+R^(8M)+R^(24M)+sum_e c_e*(R^(T1-e)+R^(T2-e))',
                    'DR':'R^H',
                    'MC':'B-1-sum_(e in E_native,e!=1) R^e-2*R^dummy0',
                    'MF_native':'mu*(R^T1+R^T2)+sum_(r=0..1,c=0..2,s) R^p(r,c,s)+sum_(r=0..2,c=0..1,s) R^(H+p(r,c,s))+R^(9M)+R^(27M)+4',
                    'Bm1':'B-1', 'Kconstant':'DC+B*DR', 'MF':'MF_native+B-1',
                    'twice_cell_bits':'2d', 'inner_bits':'b', 'W0':'R*B^2=2^(2d+b)',
                    'W0plus2d':'R*B^2+2d'},
                coefficients_expanded=False,
                note='Fixed finite sums and fixed integer exponents define exact coefficients. Only geometry and congruences are materialized. No proof-search/halting oracle enters the definition.')


if __name__ == '__main__':
    result = specification()
    (HERE/'coefficient_specification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result['geometry'],indent=2))
