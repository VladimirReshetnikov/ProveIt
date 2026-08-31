"""Stage 8b: fine data for the zoom figure of the two narrow profile features.

Emits pgfplots coordinate lists for P_17(y) on the two windows
[1.10, 1.19] and [1.38, 1.48] at spacing 2^-11, plus the exact feature
points y = 8/7 and 10/7.  These are the excursions that a step-0.025
mantissa grid (first audit) cannot resolve.
"""

import json
import os
import numpy as np

from stage8_profile import cell_masses, profile_at

N_LEVEL = 17


def main():
    mass, _ = cell_masses(N_LEVEL)
    A1n = mass.sum()
    Fb = np.concatenate([[0.0], np.cumsum(mass)]) / A1n

    def prof_boundary(y):
        idx = int(round((y - 1.0) * (1 << N_LEVEL)))
        return (1.0 + Fb[idx]) / y

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "feature_zoom.txt"), "w") as f:
        for lbl, lo, hi in (("lower", 1.10, 1.19), ("upper", 1.38, 1.48)):
            f.write(f"%% window {lbl}: P_{N_LEVEL} at spacing 2^-11\n")
            y = lo
            step = 2.0 ** (-11)
            pts = []
            while y <= hi + 1e-12:
                yy = round(y * (1 << N_LEVEL)) / float(1 << N_LEVEL)
                pts.append((yy, prof_boundary(yy)))
                y += step
            for i in range(0, len(pts), 4):
                f.write(" ".join(f"({a:.6f},{b:.7f})" for a, b in pts[i:i + 4])
                        + "\n")
            f.write("\n")
        f.write("%% exact features\n")
        for y, lbl in ((8.0 / 7.0, "8/7"), (10.0 / 7.0, "10/7")):
            v = profile_at(N_LEVEL, y, mass, A1n)
            f.write(f"%% P_{N_LEVEL}({lbl}) = {v:.10f}\n")
    print("feature_zoom.txt written.")


if __name__ == "__main__":
    main()
