"""Exact arithmetic check for the moving-centre residue example.

Coordinates and integrand samples use integer numerators. Each interval,
mesh decision and final comparison uses rational arithmetic. Decimal output
is for readability. Run with Python 3.9+; no third-party dependency.
"""
from fractions import Fraction as Q
from math import isqrt


def centre_numerators(bits):
    return isqrt(2 << (2 * bits)), isqrt(3 << (2 * bits))


def integrand_scaled(x, y, den, scale):
    """Floor both coordinates of scale *((1+i)/u + 1/u^2), u=(x+iy)/den."""
    modulus = x*x + y*y
    assert modulus > 0
    sq = modulus*modulus
    re = den*(x+y)*modulus + den*den*(x*x-y*y)
    im = den*(x-y)*modulus - 2*den*den*x*y
    return (scale*re)//sq, (scale*im)//sq


def contour_sum(bits=20, mesh=1 << 14, sample_bits=24):
    """Positive square with half-side two and centre A_6."""
    den = 8 << bits
    scale = 1 << sample_bits
    assert bits >= 6 and (4*den) % (2*mesh) == 0
    b = centre_numerators(6)
    a = centre_numerators(bits)
    bx, by = ((b[j] << (bits-6)) - a[j] for j in range(2))
    # The upper bound uses the exact square-root floor error of A_6.
    assert Q(abs(bx)+abs(by), den) <= Q(1,32)
    vertices = [(bx+u*den, by+v*den)
                for u, v in [(-2,-2), (2,-2), (2,2), (-2,2), (-2,-2)]]
    real_sum = imag_sum = 0
    h = (4*den)//mesh
    for (sx,sy),(ex,ey) in zip(vertices, vertices[1:]):
        dx, dy = (ex-sx)//mesh, (ey-sy)//mesh
        for k in range(mesh):
            x = sx + k*dx + dx//2
            y = sy + k*dy + dy//2
            assert 32*max(abs(x),abs(y)) >= 63*den
            re, im = integrand_scaled(x, y, den, scale)
            real_sum += re*dx - im*dy
            imag_sum += re*dy + im*dx
    val = (Q(real_sum,scale*den), Q(imag_sum,scale*den))
    # 24-Lipschitz integrand, perimeter 16, max midpoint distance h/2,
    # pole localization error < 1/(4*2^bits), 2-coordinate rounding.
    error = 16*(24*Q(h,2*den) + 24*Q(1,4 << bits) + Q(2,scale))
    return val, error


def twice_pi_interval(n=256):
    """Right and left Riemann sums of 8/(1+x^2) on [0,1]."""
    lower = sum((Q(8*n, n*n+i*i) for i in range(1,n+1)), Q(0))
    upper = lower + Q(4,n)
    return lower, upper


def main():
    (re, im), error = contour_sum()
    lo, hi = twice_pi_interval()
    mid = (lo+hi)/2
    assert abs(re+mid) + abs(im-mid) <= error + (hi-lo)
    assert error < Q(47,1000)
    print("Contour panels: 65536")
    print(f"Quadrature centre: ({re}, {im})")
    print(f"Taxicab error upper bound: {error} = {float(error):.9f}")
    print(f"2*pi interval (decimal display): [{float(lo):.8f}, {float(hi):.8f}]")
    print("Exact residue comparison: passed")


if __name__ == "__main__":
    main()
