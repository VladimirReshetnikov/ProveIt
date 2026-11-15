# Three-residue formula encoding with an atom-operand tag

New constructors:

- I(A,B)=3 p(A,B)
- U(a,B)=3 p(B,a)+2
- M(a,b)=3 p(a,2b)+1
- E(a,b)=3 p(a,2b+1)+1

The second Cantor component of an atom carries the M/E parity tag. This is
not the already rejected constant equality-offset scheme and is not the
previous mixed3/6 atom encoding.

`recoding.tex` proves iPRA refutation equivalence with the original C4
calculus using inverse PR permutations on *both* formula codes and variable
labels. This handles the diagonal binder and property-as-binder gate exactly.
The permutations are nonmonotone, so restricted rho leaves are expanded via
the existing finite unrestricted `rho8All` template rather than assuming
preservation of u<=D.

`python3 recoding.py` regenerates `recoding_checks.json`. The checks are
finite exact arithmetic consistency checks; the universal induction proof
is in the LaTeX text. No concrete machine state count is asserted here.

The inherited `reference/RestrictedImplication.lean` was copied unchanged
from `references/q_exchange/RestrictedImplication.lean` in the AX11H written
calibration archive of SHA-256
93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075.
Its contents originate in the James Y. Chang / ProveIt PA196 construction;
all original repository attribution and applicable licenses remain applicable.
No new kernel compilation of that source is claimed by this packet.

## Independently checked rho proof templates

Run `python3 check_rho_generic_template.py` to verify the expanded formal
proof in `rho_generic_template.json.gz`. Its 68,268 primitive rows prove
the unrestricted rho formula for four formal variables. Every leaf guard
is checked as syntactic subtree inclusion; this proves the guard for any
interpretation in which implication dominates each argument. The checker
does not import the source proof parser or assume its correctness.

Run `python3 check_rho_guard_certificate.py` for the additional concrete
instance D=3, A=0, H=0, u=7 at coefficient three. Its 60,636 primitive
rows all pass the restricted leaf guard, while its final formula has
u>D. This checks the exact difficulty created by the nonmonotone recoding.

The two certificate generators are respectively
`python3 build_rho_guard_certificate.py --symbolic` and
`python3 build_rho_guard_certificate.py`. The builder adapts the proof
parsing scaffold of the inherited ProveIt `expand_basis.py`; attribution
is retained in the source header, with licenses under `reference/`.

## Further research only: tagged two

`tagged2_check.py` and its JSON result cover the alternative encoding at
the end of the LaTeX fragment. This encoding has exact constructor and
seed recoding identities but no validated physical implementation in this packet; the separate
compiler-pricing prototype fails a source contract. No state saving is asserted.
