"""Small public-interface example. Run: python code/demo.py"""
from holonomic import Holonomic, HF, Guarded, X

E = Holonomic([X, -1], [1])            # E(t) = sum t^n/n!
Eminus = Holonomic([X, 1], [1])       # E(-t)
G = Holonomic([X, -(X+1)], [1])       # 1/(1-t)
A = Holonomic([X, -(X+1)**2], [1])    # sum n! t^n; formal, not analytic

UE = Guarded(0, {1: HF.of(E)})
UEminus = Guarded(0, {1: HF.of(Eminus)})
U2 = Guarded(0, {2: HF.of(1)})
print('(U*E(t))*(U*E(-t)) == U^2:', (UE*UEminus).equal(U2))
print('First seven factorial-series coefficients:', [A.coefficient(n) for n in range(7)])
tail = Guarded(0, {1: HF.of(G-E)})
print('Leading term of U*(G-E):', tail.leading)
print('Interpretation: ((k,m),c) means c * omega^(k*omega+m).')
print('The tail is positive:', tail.sign == 1)
