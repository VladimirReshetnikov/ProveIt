from fractions import Fraction as F
from math import factorial
N = 31

def mul(a, b):
    c = [F(0)] * (N + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b[:N + 1 - i]):
            c[i + j] += x * y
    return c

q = [F(0)] * (N + 1)
for j in range(N // 2 + 1):
    q[2*j] = F(1, 4**j * factorial(2*j + 1))
B = [F(1)]
for k in range(1, N + 1):
    B.append(-sum((F(k)-F(i, 2))*q[i]*B[k-i]
                  for i in range(1, k+1)) / k)
T = [F(0), F(1, 4)] + [F(0)] * (N - 1)
for k in range(2, N + 1):
    T[k] = -sum(T[i]*T[k-1-i] for i in range(k)) / (4*k)
E = [F(1)]
for k in range(1, N + 1):
    E.append(-sum(i*T[i]*E[k-i] for i in range(1, k+1))/k)
A = mul(B, E)
v = [F(0)] + q[:N]
power = [F(1)] + [F(0)] * N
S = power.copy()
b = F(3, 16)
for j in range(1, N + 1):
    if j > 1:
        b *= F((2*j-3)*(2*j+1), 16*j)
    power = mul(power, v)
    for k in range(j, N + 1):
        S[k] -= b * power[k]
h = mul(A, S)
assert h[:4] == [1, F(-7, 16), F(43, 1536), F(-61, 8192)]
assert all(h[k] < 0 for k in range(3, N + 1))
print("Exact certificate: h_k < 0 for 3 <= k <= 31.")
