# Authored verification code

All mandatory modules use the Python standard library only. Run with Python
3.10+ and -I -S -B. All guards use explicit exceptions, never removable assert
statements. None of these modules contacts the network or changes input data.

- tower.py: exact n! coefficients of finite continued exponentials, the
  stabilized triangular truncation, and exact-height differences. Positive
  integer or Fraction shifts; degree and height 0..200
- prufer.py: independently decodes every Pruefer string on labels 0..n,
  roots the resulting tree at 0, and sums nonroot depth products by height;
  also sums products of depth+1 for shift two. Exhaustive domain n=0..7
- profiles.py: independent sum over positive compositions of n using
  n! times product (i*d_(i-1))**d_i/d_i!, with d_0=1. Domain n=0..14;
  mandatory verification uses n=0..12
- check_exact.py: validates fixed schemas and pinned fixture digests,
  recomputes all coefficients and height cells through n=48, checks 15
  official A096537 terms and nine A096542 rows, compares independent
  Pruefer trees through n=7 and profiles through n=12, and prints a
  deterministic exact receipt. --output accepts only a fresh external file
- diagnose_mpmath.py: optional, lazy mpmath import; finite critical/tilted
  tower ratios and characteristic-function illustrations. Its status is
  DIAGNOSTIC_ONLY. It provides no certified intervals, digits, error bounds,
  effective onset, or proof of convergence. It is never imported or executed
  by mandatory checks/builds

The two coefficient recurrences in tower.py share the defining identity and
are not claimed independent. Independence is supplied by the separate tree
and profile enumerators. n counts nonroot vertices: the single-vertex root
object is n=0. The 280392-tree exhaustive count covers n=1..7; including n=0
adds one object. The 28 strictly positive-height cells are h=1..n for n=1..7;
36 cells are checked when height-zero entries and n=0 are included.
