"""Enclose 2 Lambda_f'(1)/Lambda_f(1) for f=eta(z)eta(23z)."""
from mpmath import iv

iv.dps = 30
c = 2 * iv.pi / iv.sqrt(23)
steps = 64
end = 16
factors = 12
denominator = iv.mpf(0)
numerator = iv.mpf(0)
for j in range(steps, end * steps):
    t = iv.mpf([j, j + 1]) / steps
    q = iv.exp(-c * t)
    product = q
    for k in range(1, factors + 1):
        product *= (1 - q**k) * (1 - q**(23*k))
    # 1 - sum of omitted u_i <= product(1-u_i) <= 1.
    loss = q**(factors+1)/(1-q) + q**(23*(factors+1))/(1-q**23)
    product *= iv.mpf([1-loss.b, 1])
    denominator += product * (1 + 1/t) / steps
    numerator += product * iv.log(t) * (1 - 1/t) / steps
last = iv.exp(-c * end)
denominator += iv.mpf([0, (2 * last / c).b])
numerator += iv.mpf([0, (last * (end/c + 1/c**2)).b])
ratio = 2 * numerator / denominator
zeta_weight = 2 + iv.euler - iv.log(4 * iv.pi)
print("2 Lambda_f'(1)/Lambda_f(1)", ratio)
print("cubic logarithmic derivative invariant", zeta_weight + ratio)
assert ratio > iv.mpf("0.32") and ratio < iv.mpf("0.36")
