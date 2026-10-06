#!/usr/bin/env python3
"""Exact rational premises for a global nonvanishing denominator lemma.
The analytic proof, including the explicit product lower bound, is in
report122.pdf, Section 5. No floating-point calculation is used here.
"""
if not __debug__:
 raise RuntimeError("Auxiliary producer scripts require ordinary Python; run the active-guard companion with python3 checks/verify.py")
from fractions import Fraction as Q
Z=Q(149,1000); B=Q(4,3); w=Z*B
rho=Q(4,27)
phi_increment=w/(1-w)**2
L=Z*(1+w)/(1-w)**3
K=(1+w)/((1-Z)**2*(2-B))
assert rho<Z<Q(3,20)
assert phi_increment<B-1
assert 0<L<Q(7,20)
assert 0<K<Q(5,2)
assert K*L<Q(7,8)<1
assert K*L/(1-L)<Q(4,3)
assert 8*Q(4,3)==Q(32,3)<11
assert (Q(5,2)*Q(7,20))/(1-Q(7,20))==Q(35,26)
assert 8*Q(35,26)==Q(140,13)<11
c0_lower=(2-Z)/(1+Z)
p_lower=c0_lower/Q(3**11)
assert c0_lower>1 and p_lower>Q(9,10**6)
# At z=0, c_0=2; c_j=1 and d_j=0 for j>=1, by the
# difference divisibility established in the lemma. Thus P(0)=2>0.
print('PASS: global lower-orbit disk, contraction and nonvanishing premises')
for name,val in [('Z',Z),('B',B),('phi_increment',phi_increment),('L',L),('K',K),('K*L',K*L),('K*L/(1-L)',K*L/(1-L)),('c0_lower',c0_lower),('P_modulus_lower',p_lower)]:
    print(f'{name} = {val}')
print('Uniform |P(z)| > 9/10^6 for |z| <= 149/1000; P(0)=2.')
