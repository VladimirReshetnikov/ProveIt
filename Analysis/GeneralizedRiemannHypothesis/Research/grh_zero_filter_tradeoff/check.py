#!/usr/bin/env python3
"""Reproducible numerical checks (not a rigorous zero certificate).
Requires mpmath. Run: python check.py > checks.json
"""
import json
import mpmath as m
m.mp.dps = 45

def txt(x):
    return m.nstr(x, 22)

y=m.findroot(lambda x:x*m.cot(x)-m.mpf('0.5'), (1,1.3))
k=m.pi/(4*y)
c0=-m.log(m.sin(1))
assert abs(y*m.cot(y)-m.mpf('0.5')) < m.mpf('1e-40')
# Direct integration and interpolation on one separated symmetric color.
delta=m.mpf('1.5')
A=m.pi**2/(2*y*delta)
a=m.pi/(2*A)
gamma=[m.mpf(s) for s in ('-8.1','-5.4','-3.2','-1.5','1.5','3.2','5.4','8.1')]
def f(x):
    if abs(abs(x)-a)<m.mpf('1e-40'):
        return m.pi/4
    return a*a*m.cos(A*x)/(a*a-x*x)
def g(t): return a/2*m.cos(a*t)
for x in [m.mpf('0'),a,m.mpf('0.7'),m.mpf('2.5')]:
    assert abs(m.quad(lambda t:g(t)*m.cos(x*t),[-A,A])-f(x)) < m.mpf('1e-39')
M=m.matrix([[f(v-w) for w in gamma] for v in gamma]); b=m.matrix([f(v) for v in gamma]); coeff=m.lu_solve(M,-b)
cnorm=sum(abs(v) for v in coeff)
res=max(abs(v) for v in M*coeff+b)
assert cnorm<=1 and res<m.mpf('1e-39')
Z=1+sum(coeff[i]*f(gamma[i]) for i in range(len(gamma)))
assert Z>0
# On a different symmetric multiset with repeated ordinates, use elementary
# two-point measures to build a known exact filter, then multiply by the
# stopband extremizer. Compare lower bounds against its actual support.
freqs=[m.mpf('1.5'),m.mpf('1.5'),m.mpf('1.75'),m.mpf('2.75'),m.mpf('3.4'),m.mpf('4.7')]
B=m.mpf(5); L=m.mpf(12)
h=m.acosh(m.exp(L))/B
H=sum(m.pi/(2*v) for v in freqs)+h
J=m.pi/B*sum(m.log(B/v) for v in freqs)
S=2/B*sum(m.acosh(B/v) for v in freqs)
assert H>=S+L/B and H>=J
# Verify exact-stopband transform via the even-switch Dyson expansion on a
# real frequency. Matrix identity yields the same series as in the proof.
for z in [m.mpf(0),m.mpf(3),B,m.mpf(8)]:
    mat=m.matrix([[1j*z,B],[B,-1j*z]])
    E=m.expm(h*mat)
    tr=(E[0,0]+E[1,1])/(2*m.cosh(B*h))
    val=m.cosh(h*m.sqrt(B*B-z*z))/m.cosh(B*h)
    assert abs(tr-val)<m.mpf('1e-38')
    if z>=B: assert abs(val)<=m.exp(-L)*(1+m.mpf('1e-38'))
# Illustrate finite zeta lower bounds; mpmath values are not certified here.
zeros=[];n=1
while True:
    v=m.im(m.zetazero(n));n+=1
    if v>100:break
    zeros.append(v)
rows=[]
for B in map(m.mpf,[25,50,100]):
    vs=[z for z in zeros if z<=B]
    j=m.pi/B*sum(m.log(B/z) for z in vs)
    s=2/B*sum(m.acosh(B/z) for z in vs)
    asy=(m.log(B/(4*m.pi))-1)/2
    rows.append(dict(B=txt(B),positive_zeros=len(vs),circular_lower=txt(j),slit_lower=txt(s),slit_with_article_attenuation=txt(s+c0*m.log(B)),slit_asymptotic=txt(asy)))
print(json.dumps(dict(status='all numerical assertions passed; not a rigorous proof checker',y_star=txt(y),kappa=txt(k),c0=txt(c0),kappa_plus_c0=txt(k+c0),cosine_window=dict(delta=txt(delta),A=txt(A),l1_coefficients=txt(cnorm),normalizer=txt(Z),max_residual=txt(res)),clustered_example=dict(frequencies=[txt(v) for v in freqs],actual_constructed_H=txt(H),circular_lower=txt(J),slit_lower=txt(S),joint_lower=txt(S+L/5)),zeta_examples=rows),indent=2))
