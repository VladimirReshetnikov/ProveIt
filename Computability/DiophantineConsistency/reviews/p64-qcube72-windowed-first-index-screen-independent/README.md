# Independent bounded windowed first-index screen

**PASS for the stated finite noncompact domain.** The independent `check.py`
enumerates the same six million triples with a different loop order and uses
the equivalent canceled filter `(H/gcd(H,U)) | (2^R−X)`. It reproduces all
four projection survivors, verifies exact main Pell norms and positive
integral free carriers, and uses a binary search in the strictly increasing
first Pell coefficient to exclude `Yk<c<(Y+1)k` for every `1≤j≤R`. It
matches the pinned author result. This is an external finite computation;
no Lean command was run.

The domain fixes `q=3`, `beta=2`, `J=1`, `F=alpha=1`, ranks 43 and 47,
`1≤s≤300`, `1≤w≤10000`, and assumes `m=R`. The mask pairs `(0,1)` and
`(1,2)` respectively yield these ranks and satisfy the port inequalities
and `R+1<q⁴`. Transport-invalid tuples are allowed, so the screened family
is a superset with respect to that constraint. The free-carrier projection
is a necessary condition, not a sufficient characterization of full zeros.
The strict scale inequality is necessary and sufficient for positive
`eta,zeta` once the other core coordinates are fixed.

This does not prove the missing first-index congruence, check the strong or
auxiliary residuals, rule out indices above `R`, cover the compact44 ports,
or establish any general existence or nonexistence result.

Run:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-windowed-first-index-screen-independent/check.py
```
