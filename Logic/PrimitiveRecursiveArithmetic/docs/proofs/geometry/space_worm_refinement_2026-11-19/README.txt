Universal convex covers of unit space curves
19 November 2026

Read report.pdf. The full source is report.tex together with sections/ and figures/.
The problem allows arbitrary endpoints, including smooth open curves, and proper rigid motions.

Certified interval    0.018975 < V_3 < 0.052956040
Volume of cover       about 0.05295603908
Independent ball test 0.01897 < V_3

Compared with the first archive, the lower endpoint increases by 1.29%,
the upper endpoint decreases by 2.42%, and the interval narrows by 4.37%.
Compared with the second archive's preprint-dependent interval, the
interval narrows by 17.33%. The comparison on page 1 uses both archives. The strongest lower
bound calls on published inspection and planar width constructions and a
2026 spatial width theorem. The additional polygon in this package can
replace the inspection construction for the slightly weaker 0.01897.
The upper bound calls on Ghomi's alternating support theorem and Keller's
planar-cover theorem. The included programs verify the new estimates;
the original authors' formal proof builds were not replayed.

Rebuild from this directory with a standard TeX Live installation
    latexmk -pdf report.tex

The following checks use Python 3.8+ and only the standard library
    python3 code/verify_spike.py
    python3 code/check_inspection.py
    python3 code/lower_certificate.py
    python3 code/exact_series.py

The last command evaluates the first discrete minimum in the exact series.
The individual rational lower and upper factors at a selected order are
printed by python3 code/exact_series.py --factors 1024. They need the
corresponding discrete minimum to give a numerical interval. The general
enumerator is provided under --order N. Orders above one are prohibitive
for this direct implementation.

The diagram is included as a vector PDF. To regenerate it with NumPy,
SciPy, and Matplotlib installed, run
    python3 code/draw_construction.py figures/construction.pdf
    python3 code/draw_lower.py figures/lower_geometry.pdf
