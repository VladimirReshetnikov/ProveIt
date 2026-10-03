"""Independent endpoint constants using U recurrence and implicit critical jets.

No galled-tree triangle, numerical root differentiation, or external files are
used. Refactored from the independent audit's check_constants.py and
check_all_orders_independent.py (2 October 2026). The formulas are documented
in the accompanying mathematical report. Results are non-interval numerics.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp
from triangle import wedderburn_etherington


def compute_constants(truncation=220, precision=110):
    if truncation < 20 or precision < 40:
        raise ValueError("Use truncation >= 20 and precision >= 40")
    with mp.workdps(precision):
        coefficients = list(map(mp.mpf, wedderburn_etherington(truncation)[::-1]))

        def U(x):
            return mp.polyval(coefficients, x)

        def H0(w):
            return U(w*w)/w

        def V(w):
            h = H0(w)
            return ((h*h + H0(w*w))/2 + w*h**3)/(1-w*h)

        def W(w):
            h, v, nested = H0(w), V(w), H0(w*w)
            return (h*v + w*(v*v + 6*h*h*v + 3*h**4 + V(w*w) + nested*nested)/2)/(1-w*h)

        R = mp.findroot(lambda x: 2*x+U(x*x)-1, (mp.mpf('.40'), mp.mpf('.41')))
        r, y = mp.sqrt(R), 1/mp.sqrt(R)

        def Phi(w, e, z):
            # Nested parameter is e^2: coefficients through e^4 suffice.
            nested = H0(w*w) + e*e*V(w*w) + e**4*W(w*w)
            return w+e*(z*z+nested)/2+w*(z*z/(1-e*z)**2+nested/(1-e*e*nested))/2

        def Phiy(w, e, z):
            return e*z + w*z/(1-e*z)**3

        fw = mp.diff(lambda w: Phi(w, 0, y), r)
        rc, yc = [r], [y]
        jet_residuals = []
        for order in range(1, 5):
            def rp(e):
                return sum(c*e**k for k, c in enumerate(rc))

            def yp(e):
                return sum(c*e**k for k, c in enumerate(yc))

            f = mp.diff(lambda e: Phi(rp(e), e, yp(e))-yp(e), mp.mpf(0), order)/mp.factorial(order)
            g = mp.diff(lambda e: Phiy(rp(e), e, yp(e))-1, mp.mpf(0), order)/mp.factorial(order)
            # The linearized critical system has matrix ((fw,0),(y,r)).
            radial = -f/fw
            height = (-g-y*radial)/r
            rc.append(radial)
            yc.append(height)
            jet_residuals.append(max(abs(f+fw*radial), abs(g+y*radial+r*height)))

        def radius_jet(e):
            return sum(c*e**k for k, c in enumerate(rc))

        p = [mp.diff(lambda e: mp.log(r/radius_jet(e)), mp.mpf(0), j)/mp.factorial(j)
             for j in range(1, 5)]
        a, b, c, p4 = p

        def amplitude(e):
            w = sum(rc[k]*e**k for k in range(3))
            z = sum(yc[k]*e**k for k in range(3))
            pw = mp.diff(lambda value: Phi(value, e, z), w)
            pyy = mp.diff(lambda value: Phiy(w, e, value), z)
            return mp.sqrt(2*w*pw/pyy)/(2*mp.sqrt(mp.pi))

        h0 = amplitude(mp.mpf(0))
        alpha1 = mp.diff(amplitude, mp.mpf(0))/h0
        alpha2 = mp.diff(amplitude, mp.mpf(0), 2)/(2*h0)

        def Q(w):
            return 1-2*w*w-U(w**4)

        q1 = -r*mp.diff(Q, r)
        q2 = r*r*mp.diff(Q, r, 2)/2
        c1 = -mp.sqrt(q1)/r
        c3 = c1*(1+q2/(2*q1))
        h1 = c1*mp.mpf(3)/8/mp.gamma(-mp.mpf('.5')) + c3/mp.gamma(-mp.mpf('1.5'))
        kappa = h1/h0
        beta = b/a**2
        A = alpha1/a-beta
        B = c/a**3-2*beta**2
        C22 = alpha2/a**2-3*alpha1*beta/a-3*c/a**3+mp.mpf(11)/2*beta**2
        C24 = p4/a**4+alpha1*c/a**4-2*alpha1*beta**2/a-7*c*beta/a**3+mp.mpf(26)/3*beta**3
        values = dict(R=R, r0=r, a=a, b=b, c=c, p4=p4, beta=beta, h0=h0,
                      alpha1=alpha1, alpha2=alpha2, A=A, B=B, kappa=kappa,
                      C22=C22, C24=C24, C26=B*B/2)
        return {
            "method": "independent U recurrence; four implicit critical Taylor jets",
            "truncation": truncation,
            "working_decimal_precision": precision,
            "numerical_status": "non-interval; extra stored digits are not accuracy certificates",
            "constants": {key: mp.nstr(value, min(100, precision-10)) for key, value in values.items()},
            "radius_taylor_coefficients": [mp.nstr(value, min(100, precision-10)) for value in rc],
            "height_taylor_coefficients": [mp.nstr(value, min(100, precision-10)) for value in yc],
            "linear_system_max_absolute_residual": mp.nstr(max(jet_residuals), 8),
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--truncation", type=int, default=220)
    parser.add_argument("--precision", type=int, default=110)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(compute_constants(args.truncation, args.precision), indent=2)+"\n"
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
