"""Exact-rational reference algorithms for Dirichlet/Kronecker in iPRA.

No floating point or trigonometry is used. Real names are external callables
name(k) with |name(k)-x| <= 2**(-k). This interface is NOT a claim that arbitrary
PR program codes have a universal primitive-recursive evaluator.

Kronecker searches require the mathematical certificate stated in the paper.
All searches have explicit finite bounds; the deliberately coarse bounds are
proof bounds, not practical complexity claims. Python is a reference, not a
kernel-checked iPRA derivation.
"""
from fractions import Fraction as F
from math import isqrt, lcm
from typing import Callable, Iterable

Name = Callable[[int], F]


def precision(denominator: int) -> int:
    if denominator < 1:
        raise ValueError("positive denominator required")
    return denominator.bit_length()


def nearest_integer(x: F) -> int:
    a = x.numerator // x.denominator
    return a if x - a <= F(1, 2) else a + 1


def rho(x: F) -> F:
    return abs(x - nearest_integer(x))


def rational_name(x: F) -> Name:
    x = F(x)
    return lambda k: x


def sqrt_name(n: int) -> Name:
    if n < 0:
        raise ValueError("nonnegative radicand required")
    def name(k: int) -> F:
        return F(isqrt(n << (2*k)), 1 << k)
    return name


def dirichlet_rational(x: F, N: int) -> dict:
    """Sharp rational theorem: q<=N, |q*x-p|<=1/(N+1)."""
    if N < 1:
        raise ValueError("N must be positive")
    x = F(x)
    floors = [(k*x).numerator // (k*x).denominator for k in range(N+1)]
    residues = [k*x-floors[k] for k in range(N+1)]
    order = sorted(range(N+1), key=lambda k: (residues[k], k))
    for j in range(N+1):
        u, v = order[j], order[(j+1) % (N+1)]
        wrap = int(j == N)
        gap = residues[v]-residues[u]+wrap
        if gap <= F(1, N+1):
            q0, p0 = v-u, floors[v]-floors[u]-wrap
            sign = 1 if q0 > 0 else -1
            q, p = sign*q0, sign*p0
            assert 1 <= q <= N and abs(q*x-p) == gap
            return dict(p=p, q=q, gap=gap, indices=[u, v], wrap=wrap)
    raise AssertionError("finite circular-gap invariant failed")


def dirichlet_scalar(name: Name, N: int) -> dict:
    k = precision(2*N*N*(N+1))
    x, eta = F(name(k)), F(1, 1 << k)
    ans = dirichlet_rational(x, N)
    upper = abs(ans['q']*x-ans['p'])+ans['q']*eta
    assert upper < F(1, N)
    return dict(**ans, N=N, sample=x, precision=k, input_error=eta,
                linear_error_bound=upper)


def simultaneous_parameters(d: int, N: int) -> dict:
    if min(d, N) < 1:
        raise ValueError("positive d,N required")
    X, g = F(2*N+1, 2), F(1, N*(2*N+1))
    H = 4*d*N*(2*N+1)
    threshold = 1/X+g/4
    k = next(k for k in range(1, H+1) if F(k, H)**d >= threshold)
    R, S = F(k, H), F(k+1, H)
    M = 16*N*d*(N+1)
    A, B = int(M*X), (M*R).numerator // (M*R).denominator
    count, colors = A*B**d, M**(d+1)
    assert k < H and N*S**d < 1 and count > colors and B >= 1
    return dict(d=d, N=N, H=H, k=k, R=R, S=S, M=M,
                grid_a_count=A, grid_b_count=B, grid_count=count,
                residue_colors=colors)


def dirichlet_simultaneous(names: list[Name], N: int) -> dict:
    """Full arbitrary-N theorem; the grid proof justifies a shorter search.

    It suffices to scan q<=N and round each rational q*r_i. No enormous
    auxiliary grid is materialized. Its exact counting inequality is recorded.
    """
    par = simultaneous_parameters(len(names), N)
    k = precision(N*par['H'])
    eta = F(1, 1 << k)
    xs = [F(name(k)) for name in names]
    for q in range(1, N+1):
        ps = [nearest_integer(q*x) for x in xs]
        errors = [abs(q*x-p) for x, p in zip(xs, ps)]
        if all(e < par['R'] for e in errors):
            upper = [e+q*eta for e in errors]
            assert all(e < par['S'] for e in upper)
            assert all(N*e**len(names) < 1 for e in upper)
            return dict(**par, q=q, p=ps, samples=xs, precision=k,
                        input_error=eta, linear_error_bounds=upper)
    raise AssertionError("finite simultaneous theorem violated")


def unbounded_denominator(name: Name, B: int) -> dict:
    if B < 0:
        raise ValueError("B must be nonnegative")
    N = (B+1)**3
    base = dirichlet_scalar(name, N)
    multiplier = B//base['q']+1
    q, p = multiplier*base['q'], multiplier*base['p']
    upper = multiplier*base['linear_error_bound']
    assert B < q <= N and q*upper < 1
    return dict(B=B, N=N, p=p, q=q, multiplier=multiplier,
                linear_error_bound=upper, base=base)


def kronecker_parameters(d: int, s: int, C: int) -> dict:
    if d < 1 or s < 2 or C < 1:
        raise ValueError("d>=1, s>=2, C>=1 required")
    t = 2*s
    r = 4*3**d*(d+1)**(d+1)*t**(2*d+2)
    A = (2*r+1)**d
    N = 32*C*A
    return dict(d=d, s=s, C=C, t=t, r=r, A=A, N=N)


def integer_box(radius: int, dimension: int) -> Iterable[tuple[int, ...]]:
    if dimension == 0:
        yield ()
    else:
        for x in range(-radius, radius+1):
            for tail in integer_box(radius, dimension-1):
                yield (x,)+tail


def expanding_box(N: int, dimension: int) -> Iterable[tuple[int, ...]]:
    """Each q with |q_i|<N exactly once, small coefficients first."""
    for radius in range(N):
        for q in integer_box(radius, dimension):
            if max(map(abs, q), default=0) == radius:
                yield q


def kronecker_search(matrix: list[list[Name]], target: list[Name],
                     s: int, C: int) -> dict:
    """Conditional bounded search; requires the paper's K(r,C) hypothesis."""
    d, m = len(target), len(matrix)
    if m < 1 or any(len(row) != d for row in matrix):
        raise ValueError("nonempty rectangular matrix required")
    par = kronecker_parameters(d, s, C)
    N = par['N']
    k = precision(8*s*(m*(N-1)+1))
    eta = F(1, 1 << k)
    a = [[F(name(k)) for name in row] for row in matrix]
    b = [F(name(k)) for name in target]
    for examined, q in enumerate(expanding_box(N, m), 1):
        residual = [sum(q[i]*a[i][j] for i in range(m))-b[j] for j in range(d)]
        p = [nearest_integer(x) for x in residual]
        err = [abs(x-y) for x, y in zip(residual, p)]
        if all(e < F(3, 4*s) for e in err):
            input_effect = (sum(map(abs, q))+1)*eta
            upper = [e+input_effect for e in err]
            assert all(e < F(7, 8*s) for e in upper)
            return dict(**par, m=m, q=list(q), p=p, examined=examined,
                        precision=k, input_error=eta, samples_a=a, samples_b=b,
                        linear_error_bounds=upper)
    raise ValueError("no witness; supplied modulus/real-name hypotheses are invalid")


def kronecker_positive(name: Name, target: Name, s: int,
                       separation: Callable[[int], int], B: int = 0) -> dict:
    """One-generator density, assuming rho(h*alpha)>=1/separation(H).

    The separation hypothesis is for 0<|h|<=H. The theorem guarantees a
    positive q>B. A shift argument gives q<=B+2*N-1.
    """
    if B < 0:
        raise ValueError("B must be nonnegative")
    r = kronecker_parameters(1, s, 1)['r']
    par = kronecker_parameters(1, s, separation(r))
    Q = B+2*par['N']-1
    k = precision(8*s*(Q+1))
    eta = F(1, 1 << k)
    a, b = F(name(k)), F(target(k))
    for q in range(B+1, Q+1):
        residual = q*a-b
        p = nearest_integer(residual)
        if abs(residual-p) < F(3, 4*s):
            upper = abs(residual-p)+(q+1)*eta
            assert upper < F(7, 8*s)
            return dict(**par, B=B, upper_q_bound=Q, q=q, p=p,
                        examined=q-B, precision=k, input_error=eta,
                        sample_a=a, sample_b=b, linear_error_bound=upper)
    raise ValueError("separation/real-name hypotheses are invalid")


def rational_compatibility(matrix: list[list[F]], target: list[F]) -> dict:
    """Check full exact compatibility for rational inputs using residue classes.

    If it passes, C=D is valid at every height. If it fails, h is an exact
    obstructing integer relation. This is not a real-number zero test.
    """
    d, m = len(target), len(matrix)
    if d < 1 or m < 1 or any(len(row) != d for row in matrix):
        raise ValueError("nonempty rectangular matrix required")
    vals = [F(v) for row in matrix for v in row]+[F(v) for v in target]
    D = lcm(*(v.denominator for v in vals))
    def residues(dim):
        if dim == 0:
            yield ()
        else:
            for a in range(D):
                for tail in residues(dim-1):
                    yield (a,)+tail
    for h in residues(d):
        gen = [rho(sum(h[j]*matrix[i][j] for j in range(d))) for i in range(m)]
        beta = rho(sum(h[j]*target[j] for j in range(d)))
        if max(gen) == 0 and beta != 0:
            return dict(compatible=False, denominator=D, h=list(h),
                        generator_residues=gen, target_residue=beta)
    return dict(compatible=True, denominator=D, C=D, checked=D**d)


def interval_compatibility(matrix: list[list[F]], target: list[F],
                           H: int, C: int, delta: F) -> dict:
    """Finite interval checker; practical only for modest H and dimension."""
    d, m = len(target), len(matrix)
    if min(d, m, H, C) < 1 or delta < 0:
        raise ValueError("invalid certificate parameters")
    if delta > F(1, 64*d*H*(C+1)):
        raise ValueError("input error exceeds the displayed certificate bound")
    e = d*H*delta
    for checked, h in enumerate(integer_box(H, d), 1):
        U = rho(sum(h[j]*target[j] for j in range(d)))+e
        L = max(max(F(0), rho(sum(h[j]*matrix[i][j] for j in range(d)))-e)
                for i in range(m))
        if U > F(1, 8)+C*L:
            return dict(valid=False, h=list(h), U=U, L=L, e=e, checked=checked)
    return dict(valid=True, H=H, C=C, e=e, checked=(2*H+1)**d)


def jsonable(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {k: jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x
