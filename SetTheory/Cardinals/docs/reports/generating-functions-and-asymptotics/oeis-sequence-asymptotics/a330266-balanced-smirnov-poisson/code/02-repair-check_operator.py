"""Independent finite operator check. No high-cumulant assumption."""
import sympy as s
k,v,z,M=s.symbols('k v z M')
lam=k-1
L=3
a=[s.prod(k-j for j in range(m))*s.prod(k-1-j for j in range(m))/s.factorial(m) for m in range(L+2)]
# Formal log via recurrence j*a_j=sum_{i=1}^j i*b_i*a_{j-i}
b=[s.Integer(0)]
for j in range(1,L+2):
    b.append(s.factor(a[j]-sum(i*b[i]*a[j-i] for i in range(1,j))/j))
c=[s.Integer(0)]+[s.factor(b[j+1]*v**(j+1)/k) for j in range(1,L+1)]
f=[s.Integer(1)]
for j in range(1,L+1):
    f.append(s.expand(sum(i*c[i]*f[j-i] for i in range(1,j+1))/j))
H=[1,M*(M-1)/2,M*(M-1)*(3*M*M+M-2)/24,M*M*(M-1)**2*(M+1)*(M+2)/48]
def operator(h,p):
    h=s.Poly(h,M)
    powers=[p]
    for _ in range(h.degree()):
        powers.append(s.expand(v*s.diff(powers[-1],v)+lam*v*powers[-1]))
    return s.expand(sum(coef*powers[monom[0]] for monom,coef in h.terms()))
P=[s.factor(sum(operator(H[r],f[j-r]) for r in range(j+1))) for j in range(L+1)]
q=[s.Integer(0)]
for j in range(1,L+1):
    q.append(s.factor(P[j]-sum(i*q[i]*P[j-i] for i in range(1,j))/j))
expected=[0,-lam**2*v**2/2,lam**2*v**2*(2*(k-2)*v-3)/6,-lam**2*v**2*((k*k-6*k+7)*v*v-4*(k-2)*v+2)/4]
for j in range(1,L+1):
    assert s.expand(q[j]-expected[j])==0
    print(f'P_{j} = {P[j]}')
    print(f'log coefficient N^-{j} = {q[j]}')
    print(f'probability coefficient N^-{j} = {s.factor(P[j].subs(v,-1))}')
# Ratio in n, with t=1/n
p1,p2,p3=[s.factor(q[j].subs(v,-1)/k**j) for j in range(1,4)]
assert s.simplify(-p1-lam**2/(2*k))==0
assert s.simplify(p1-2*p2-lam**2*(k-2)/(6*k*k))==0
print('All third-order log-PGF, probability, and ratio coefficients match.')
