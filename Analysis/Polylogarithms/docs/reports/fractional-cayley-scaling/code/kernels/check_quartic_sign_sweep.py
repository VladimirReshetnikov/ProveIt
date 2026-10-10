#!/usr/bin/env python3
"""Finite-coefficient sweep along the local threshold; diagnostics only."""
import json
from pathlib import Path
import mpmath as mp


def main():
    mp.mp.dps = 100
    rows = []
    for b_text in [".001", ".01", ".05", ".1", ".25", ".5", ".75",
                   ".9", ".95", ".99", ".999"]:
        b = mp.mpf(b_text)
        A = 1+mp.power(2, -b)
        B = A+mp.power(3, -b)
        C = B+mp.power(4, -b)
        G = lambda a: (C+A**3*mp.power(mp.mpf(20)/27, a)
                       -2*A*B*mp.power(mp.mpf(5)/6, a))
        a = mp.findroot(G, (1, 2))
        p = {}
        h = mp.mpf(0)
        for n in range(1, 8):
            p[n] = h*mp.power(n, -a)
            h += mp.power(n, -b)
        mu = p[3]/(2*p[2])
        numerator = 4*p[3]*mu**2-4*p[4]*mu+p[5]
        K = -numerator/(2*p[2])
        Q = (p[7]-6*p[6]*mu+12*p[5]*mu**2-8*p[4]*mu**3)/(2*p[2])
        dmu = mu*(mp.log(2)-mp.log(3))
        dnum = (4*(-mp.log(3)*p[3]*mu**2+2*p[3]*mu*dmu)
                -4*(-mp.log(4)*p[4]*mu+p[4]*dmu)-mp.log(5)*p[5])
        dK = -dnum/(2*p[2])+mp.log(2)*K
        assert 1 < a < 2 and abs(K) < mp.mpf("1e-90")
        rows.append({"b": b_text, "a_star": mp.nstr(a, 50),
                     "Q_at_a_star": mp.nstr(Q, 45),
                     "dK_da_at_a_star": mp.nstr(dK, 45),
                     "Q_sign": int(mp.sign(Q)),
                     "dK_da_sign": int(mp.sign(dK)),
                     "absolute_K_residual": mp.nstr(abs(K), 8)})
    data = {"status": "Floating-point diagnostics, not interval certificates or an all-b proof.",
            "arithmetic": "mpmath at 100 decimal digits",
            "method": "Only p_n=H_(n-1)^(b)/n^a for n<=7 and closed finite coefficient formulas; no disk roots.",
            "all_Q_negative": all(r["Q_sign"] < 0 for r in rows),
            "all_K_derivatives_negative": all(r["dK_da_sign"] < 0 for r in rows),
            "rows": rows}
    # Independently check the small positive value near b=1 with a different
    # root solver and the expanded homogeneous expression for Q.
    with mp.workdps(200):
        b = mp.mpf(".999")
        A = 1+2**(-b)
        B = A+3**(-b)
        C = B+4**(-b)
        def G200(a):
            return C+A**3*(mp.mpf(20)/27)**a-2*A*B*(mp.mpf(5)/6)**a
        lo, hi = mp.mpf(1), mp.mpf(2)
        for _ in range(680):
            a = (lo+hi)/2
            if G200(a) > 0:
                hi = a
            else:
                lo = a
        a = (lo+hi)/2
        p = {n: mp.fsum(mp.power(k, -b) for k in range(1, n))*mp.power(n, -a)
             for n in range(2, 8)}
        Q = (p[7]*p[2]**3-3*p[6]*p[3]*p[2]**2
             +3*p[5]*p[3]**2*p[2]-p[4]*p[3]**3)/(2*p[2]**4)
        q_saved = mp.mpf(rows[-1]["Q_at_a_star"])
        relative_difference = abs(Q-q_saved)/abs(Q)
        assert relative_difference < mp.mpf("1e-44")
        data["independent_check"] = {
            "arithmetic": "mpmath at 200 decimal digits; not an interval certificate",
            "method": "680 bisections of G in (1,2); expanded homogeneous formula for Q",
            "b": ".999", "a_star": mp.nstr(a, 90),
            "Q_at_a_star": mp.nstr(Q, 90),
            "relative_difference_from_45_digit_sweep_value": mp.nstr(relative_difference, 12)}
    data["interpretation"] = (
        "Q is positive at b=.999, contrary to the proposed all-b negativity. "
        "All other requested samples have negative Q. This is diagnostic "
        "evidence for a quartic-sign transition, not a certified transition theorem.")
    path = Path(__file__).resolve().parents[2] / "data" / "kernels" / "quartic_sign_sweep.json"
    path.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"output": str(path), "rows": len(rows),
                      "all_Q_negative": data["all_Q_negative"],
                      "all_K_derivatives_negative": data["all_K_derivatives_negative"],
                      "max_absolute_K_residual": max(float(r["absolute_K_residual"]) for r in rows)}))
    for row in rows:
        print(row["b"], row["a_star"], row["Q_at_a_star"], row["dK_da_at_a_star"])


if __name__ == "__main__":
    main()
