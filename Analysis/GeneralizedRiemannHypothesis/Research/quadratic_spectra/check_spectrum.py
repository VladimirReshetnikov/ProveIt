#!/usr/bin/env python3
"""Compare the two sides of the interval pairing for the quadratic character mod 3.

Requires Python 3 and mpmath. This is a numerical demonstration. Mesh bracketing
and the numerical argument check do not constitute an interval proof of the
completeness or enclosures of the zeros. Optional --ordinates writes a CSV.
"""
import argparse
import csv
import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ordinates", metavar="PATH", help="write the positive zeros to CSV")
    args = parser.parse_args()
    mp.mp.dps = 28
    q, n, cutoff = 3, 2, 100
    h = mp.mpf(3) / 8
    r = mp.log(n)
    char = [0, 1, -1]

    def theta(t):
        return mp.im(mp.loggamma((mp.mpf("1.5") + 1j*t)/2)) + t*mp.log(q/mp.pi)/2

    def hardy(t):
        value = mp.exp(1j*theta(t)) * mp.dirichlet(mp.mpf("0.5") + 1j*t, char)
        if abs(mp.im(value)) > mp.mpf("1e-21"):
            raise ArithmeticError("Hardy function lost real symmetry")
        return mp.re(value)

    positives = []
    at_left = hardy(0)
    for k in range(1, 4*cutoff + 1):
        left, right = mp.mpf(k-1)/4, mp.mpf(k)/4
        at_right = hardy(right)
        if mp.sign(at_left) != mp.sign(at_right):
            zero = mp.findroot(hardy, (left, right), solver="anderson")
            if not (left <= zero <= right and abs(hardy(zero)) < mp.mpf("1e-20")):
                raise ArithmeticError("root refinement failed")
            positives.append(zero)
        at_left = at_right

    # Along Re(s)=2 the Euler product logarithm matches the principal
    # argument (|L-1| <= zeta(2)-1 < 1). Continue it back to Re(s)=1/2.
    # This is an independent numerical count, with finite sampling.
    argument, previous = mp.mpf(0), mp.mpc(1)
    for i in range(129):
        sigma = 2 - mp.mpf(3)*i/256
        current = mp.dirichlet(sigma + 1j*cutoff, char)
        argument += mp.arg(current/previous)
        previous = current
    count = (theta(cutoff) + argument)/mp.pi
    if abs(count-len(positives)) > mp.mpf("1e-20"):
        raise ArithmeticError("sign changes and numerical argument count disagree")

    if args.ordinates:
        with open(args.ordinates, "w", newline="") as output:
            writer = csv.writer(output)
            writer.writerow(["index", "positive_ordinate"])
            for k, t in enumerate(positives, 1):
                writer.writerow([k, mp.nstr(t, 21)])

    def kernel(u):
        return mp.exp(-mp.mpf("1.5")*u) / (-mp.expm1(-2*u))

    gamma_integral = mp.quad(lambda u: (h - abs(u-r))*kernel(u), [r-h,r,r+h])
    prime_mass = h*mp.log(2)/mp.sqrt(2)
    full = prime_mass - gamma_integral
    # All roots occur in symmetric pairs. The central value is nonzero
    # (alternating paired Dirichlet series at 1/2 has positive terms).
    partial = 2*mp.fsum(4*(mp.sin(t*h/2)/t)**2*mp.cos(t*r) for t in positives)
    bound = 4*(mp.log(q*cutoff/(2*mp.pi))+1)/(mp.pi*cutoff)
    bound += 4*(2*(mp.mpf("0.298")*mp.log(q*cutoff)+mp.mpf("4.358"))+mp.mpf("0.149"))/cutoff**2
    estimate = -(partial+gamma_integral)*mp.sqrt(n)/(h*mp.log(n))
    for name, val in [
        ("Cutoff",cutoff), ("Positive ordinates from sign scan",len(positives)),
        ("Positive-zero count from numerical argument",count),
        ("First positive ordinate",positives[0]), ("Last positive ordinate",positives[-1]),
        ("h",h), ("Gamma integral",gamma_integral), ("Positive prime contribution",prime_mass),
        ("Full pairing from arithmetic",full), ("Partial sum from ordinates",partial),
        ("Absolute difference",abs(partial-full)), ("Analytic tail upper bound",bound),
        ("Character estimate using partial sum",estimate),
        ("Rounded character estimate",int(mp.nint(estimate))),
    ]:
        print(f"{name}: {mp.nstr(val, 16)}")
    assert abs(partial-full) <= bound < prime_mass/2 and mp.nint(estimate) == -1


if __name__ == "__main__":
    main()
