# Optional numerical diagnostics

Run `python3 numerics/diagonal_diagnostics.py` from the report root. Python and
SciPy are needed (the recorded run used Python 3.12.14 and SciPy 1.17.0).
This is not part of the exact checker replay and it does not install packages.

The dynamic program constructs every row through n=3000 with exact Python
integers while retaining only two preceding rows. It then evaluates integer
logarithms, factorial logarithms, the Airy zero, and asymptotic corrections in
ordinary floating point. The text output is an actual captured run; its final
elapsed time is machine dependent. Exact integer arrays are not archived.

Raw and depth-1 through depth-4 corrected ratios are printed. They are numerical
diagnostics only. No interval arithmetic or analytic tail enclosure is supplied,
and no digits of the limiting amplitude or inverse index are certified.
