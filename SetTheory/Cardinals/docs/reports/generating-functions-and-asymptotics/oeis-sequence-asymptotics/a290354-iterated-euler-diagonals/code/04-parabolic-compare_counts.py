"""Compare exact integer counts with independently inverted density values.

Every displayed decimal is exploratory. The small finite differences are
diagnostics of normalization, not certified bounds for limiting constants.
"""

import argparse
import json
from pathlib import Path

import mpmath as mp

from verify_exact import bell_depths, stirling_table


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--density", type=Path, required=True)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    mp.mp.dps = 60
    density = json.loads(args.density.read_text(encoding="utf-8"))
    hs = {row["t"]: mp.mpf(row["h"]) for row in density["rows"]}
    s = stirling_table(320)
    counts = bell_depths(160, 320, s)
    rows = []
    for beta, key in [(mp.mpf("0.5"), "0.5"), (mp.mpf(1), "1.0"),
                      (mp.mpf(2), "2.0")]:
        expected = beta * 2**(beta / 3) * hs[key]
        for n in [40, 80, 160]:
            m = int(n / beta)
            logscale = (mp.loggamma(n) - n*mp.log(2) + n*mp.log(m)
                        - beta*mp.log(m)/3)
            estimate = mp.exp(mp.log(counts[m][n]) - logscale)
            rows.append({"beta": str(beta), "n": n, "m": m,
                         "I_from_counts": mp.nstr(estimate, 15),
                         "I_from_density": mp.nstr(expected, 15),
                         "ratio": mp.nstr(estimate/expected, 12)})

    z = [0, 1]
    for n in range(2, 321):
        z.append(sum(s[n][j] * z[j] for j in range(1, n)))
    L = mp.log(2)
    hL = hs["0.69314718055994530942"]
    C = mp.power(2*L, L/3) * hL / 2
    c1 = L/6
    c2 = -L*(16*L**2+45*L-90)/3240
    c3 = L**2*(10*L**2-81*L-270)/6480
    c4 = L*(1792*L**5+32400*L**4+2358405*L**3
             -1281420*L**2-8108100*L-408240)/146966400
    chains = []
    for n in [40, 80, 160, 320]:
        logscale = 2*mp.loggamma(n+1)-n*mp.log(2*L)-(1+L/3)*mp.log(n)
        norm = mp.exp(mp.log(z[n])-logscale)
        corrected = norm/(1+c1/n+c2/n**2+c3/n**3+c4/n**4)
        chains.append({"n": n, "raw_constant": mp.nstr(norm, 16),
                       "four_term_corrected": mp.nstr(corrected, 16),
                       "C_from_density": mp.nstr(C, 16),
                       "corrected_minus_C": mp.nstr(corrected-C, 10)})
    result = {"status": "exploratory finite-count comparisons",
              "density_source": args.density.name, "bell": rows,
              "chains": chains}
    out = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(out, encoding="utf-8")
    print(out, end="")


if __name__ == "__main__":
    main()
