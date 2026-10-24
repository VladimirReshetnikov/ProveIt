# Wave11 unrestricted-integer review

The new algebraic reductions in the joint-guards and centered-Pell packets
appear sound under their explicitly inherited native/Pell calibration.
All requested integer-only finite replays passed in separate scratch copies.
No Lean command was run, and no incoming archive or extracted arrival tree
was changed. This is an ordinary-mathematical and finite-certificate review,
not an internal-ZFC derivation.

The arrival pins are:

* `ZFC_Diophantine_Joint_Guards_2026-10-24.zip`:
  `291af5f4266ba5e0759273282ef4c6c5941f0bd2c3813e0481b721b08605b159`.
* `con-zfc-centered-pell-norms.zip`:
  `6b176f4e5db4b8a4ec7a7357f3ab3f8356cc811ad7fe65b0ac748c1047812fcd`.

Their complete endpoint declarations and replay commands are recorded in
`PROPOSAL_REVIEW_WAVE11_INTEGER.json`.

| Packet/family | Integer variables | Exact degree | Live binary operations |
|---|---:|---:|---:|
| Joint direct or affine quartic | 37 | 4 | No supplied shared-DAG count reviewed |
| Joint sextic | 31 | 6 | No supplied shared-DAG count reviewed |
| Centered sextic | 31 | 6 | 144 |
| Joint octic | 25 | 8 | 127 |
| Centered octic | 26 | 8 | 131 |
| Centered degree-ten form | 24 | 10 | 135 |
| Joint V-elimination form | 23 | 12 | 121 |
| Centered degree-twelve form | 23 | 12 | 122 |
| Centered strong-ordinate elimination | 22 | 14 | 123 |
| Joint strong-ordinate elimination | 22 | 16 | 118 |
| Joint projection | 21 | 20 | 115 |
| Joint projection | 20 | 32 | 112 |
| Joint projection | 19 | 88 | 109 |

Every row above ranges over **all integers**. Each equation is a sum of the
squares of its declared residuals. Named arithmetic registers are polynomial
abbreviations, not extra unknowns. The integer results must not be conflated
with the packages' separate positive11/positive12 endpoints. Gate counts
charge each live binary addition, subtraction and multiplication, including
squares and scalar products; fixed leaves and reuse are free.

On these delivered metrics, the joint25/8/127 form dominates the centered
26/8/131 form, and joint23/12/121 beats centered23/12/122. The centered
22/14/123 and joint22/16/118 forms are a degree/cost tradeoff. The 24/10 and
19/88 endpoints are useful opposite ends of the remaining tradeoffs.
These are comparisons of supplied evaluators, not optimality theorems.

The mathematical compatibility point in the joint family is substantive.
The determinant guard first restores common nonzero signs for arbitrary
signed zeros; it does not assume q positive. The signed Pell recovery then
proves X has the form `sign(c)*2^R`, before the residue condition X=2 mod3
selects its positive orientation. Completeness uses the **same canonical
source34 witnesses** for both determinant bounds and residue restrictions.
The retained top-digit and rank-tuning argument addresses this compatibility;
the claim is not a bijection on every old source assignment.

The two-sign guard is valid on the entire integer domain. For positive x,y,
put N=x+y-1; a nearest integer square has squared error strictly below N,
which is at most xy. For two negative inputs the subtracted square exceeds
xy. The positive-value polynomial `1+p^2+q^2+r(r+1)` represents every positive
integer by the three-square theorem applied to 4n-3. Thus merging two positive
quantities costs four private integer coordinates instead of six, without
silently restricting any retained coordinate to be nonnegative.

After that guard replacement, the joint projections are ordinary integral
monic substitutions. The auxiliary replacement is justified by the explicit
row identity involving the retained strong norm. Full restoration maps,
deleted-row identities, variable closure, nonzero specialized leading
coefficients, and literal shared circuits all passed independent exact
checks. The high-degree checks use validated algebraic cuts and exact
homogeneous components; they do not mistake a syntactic degree upper bound
or modular sampling for exact degree.

The centered package adds two useful independent mechanisms. Its 24/10 form
replaces the main norm N by M, where

```
M = Y*N + (X+2b)*(E-X*Y).
```

On the retained source rows, `Y=(2v+1)q^3` is nonzero: the odd factor cannot
vanish, and `q=beta*J+1` cannot vanish for the actual integer beta>1.
This establishes the reverse implication, which would fail for an arbitrary
equation multiplied by an unconstrained scale. The root shear
`y_old=f*o+y` is an invertible integer coordinate change.

Its 22/14 form first uses the strong-norm row operation to remove I from the
auxiliary row, then applies that shear, then eliminates I monically.
The new auxiliary row is

```
(f*o+y)^2 - Delta*(f^2-1)*(c+y)*(2*f*o+y-c) - 1.
```

It is the unique residual of degree seven. Its leading form
`-2*a^2*f^3*o*(c+y)` gives the nonzero degree-fourteen square
`4*a^4*f^6*o^2*(c+y)^2`. The exact checker verifies the complete leading
homogeneous form, rather than just the absence of syntactic cancellation.

Both integer families use the coherent source34 tuple
`mixed-parity-unrounded-1064921`, with the already shifted MF and the specific
determinant scales `2^1113` and `2^666104`. The six complete fixed integers
occupy 615883 raw bytes; the largest input has 1065043 bits. The finite rebuild
authenticated their exact bytes. Neither these proofs nor their bit bounds
license substituting the compact54 tuple or the new BFS-renamed tuple into
the source34 determinant. A fresh leading-digit/calibration proof would be
needed. Conversely, large expanded numerals alone do not prevent a compact
arithmetic definition: these archives simply do not yet give a complete
one-page constant recipe comparable to the compact54 page.

The joint review authenticated 300 sealed files and all eight retained input
archives, ran 22 relevant integer stages, and reproduced 24 declared artifacts
byte for byte. The centered review authenticated 125 sealed files, ran six
normal/optimized integer stages, and reproduced all 12 polynomial/circuit
packets byte for byte. Python 3.12.13 with SymPy 1.14.0 was used. The original
positive endpoints and optional original-archive root replays were outside
this integer-only run. Full stage records and stdout hashes are in the JSON
receipt; logs remain under `/tmp/proofs62ff-wave11-integer-review/`.

The recommended reusable pieces are the exact joint-sign guard, the monic
restoration maps, the nonzero-scale norm identity, and the centered auxiliary
identity. Subsequent research completed the suggested composition:
[joint22-centered](candidates/joint22-centered/README.md) has22 unrestricted
integer unknowns, exact degree14 and119 operations. Its y variable occurs
only in one auxiliary row, so one added live gate suffices. The new proof
checks every row in both directions and the complete leading form. This is
separate research, not an additional delivered endpoint in the replay counts.

The final Con(ZFC) interpretation still depends on the named unbounded Pell,
native tableau/compiler and K215/refutation-calibration arguments. The
retained status documents acknowledge the missing full native calibration
and encoded object-ZFC proof. Nothing in these finite passes closes those
obligations or proves the equations independently unsolvable.
