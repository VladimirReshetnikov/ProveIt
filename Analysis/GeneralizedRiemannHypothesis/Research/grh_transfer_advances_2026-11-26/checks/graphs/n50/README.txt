EXACT OPTIMUM FOR INDEPENDENT EDGE SIGNINGS OF C_50(1,2)
======================================================

Prepared 2026-11-26. This is a new finite resolution of the incompatible-length
problem left open by the incoming report
grh_transfers_cycle_signings_and_lubin_tate.zip. It was not found in the TeX
contents of the 46 incoming archives at ProveIt revision
5cc267af75a635199ac5d93a7d49cbce521daefc. Worldwide publication priority is
unverified. No Lean formalization is claimed.

RESULT
------
Minimum radius: strictly between 2.811568906156 and 2.811568906157.
Exact algebraic value: sqrt of largest real root of Q, whose descending
coefficients are in root_isolation.json.

All minimizers: Hamilton-cycle holonomy +1, and triangle signs a rotation of
B repeated six times followed by (-,+), or the global negative of this word,
where B=(-,-,+,-,+,+,-,+). There are exactly 100 labeled switching classes.
Every other switching class has radius >= 7029/2500 = 2.8116.
The alternating-family optimum is >2.814.

REPRODUCTION
------------
Both scripts require only ordinary Python 3.10+ and its standard library.
Run with assertions enabled (do not pass -O):

python3 certify_n50.py
python3 verify_n50_independent.py

The first exhaustively enumerates admissible path prefixes using exact
rational Schur complements, checks every cyclic window, tests whole matrices
by fraction-free Sylvester criteria, and derives characteristic polynomials
from exact traces and Newton identities.

The second independently reconstructs every path determinant by a signed
permutation dynamic program; compares every survivor, not just counts; and
certifies the spectral interval with exact fraction-free inertia counts.
It also checks the resulting determinants against the characteristic
polynomial at the two rational endpoints.

The proof of completeness is in n50_result.tex. Every 48 consecutive vertices
induce a path, so any whole matrix with norm below 2.8116 must have all its
46-triangle windows in the enumerated list. Only two cyclic rotation classes
survive and only positive holonomy passes the full matrix tests. Thus this
is an exhaustive proof over all 2^51 labeled switching classes, using local
rejection to avoid enumerating them individually.

FILES
-----
certify_n50.py                 Main verifier; writes certificate_n50.json
verify_n50_independent.py      Independent verifier; writes root_isolation.json
certificate_n50.json          Prefix counts/words, full minors, exact charpolys
root_isolation.json           Polynomial coefficients and inertia certificates
n50_exact.log                 Successful main run
n50_independent.log           Successful independent run
n50_result.tex                Drop-in theorem, proof, coefficient table

No claim or proof depends on a factorization or irreducibility computation.

The inherited input is the local-compression/Schur-complement strategy from
the earlier cycle report. The new content here is the exact n=50 window
classification, positive-holonomy minimizers, algebraic radius and certified
strict improvement over alternation.
