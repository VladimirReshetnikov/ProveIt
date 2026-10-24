# Ten positive unknowns, degree816,123 operations

This separate candidate is exactly the polynomial of the frozen
124-operation `ten-positive-scaled-norm` parent, with **one multiplication
saved**. It has **10 strictly positive unknowns**, exact degree **816**,
and **123 live binary operations**:73 multiplications,30 additions and
20 subtractions. The whole original compact44 fixed tuple is unchanged.
The parent's proof and all eight original source files are retained.

The complete literal equation is `equation.json`. Its ten unknowns are

```
j,F,alpha,i,T,w,Y,n,eta,zeta > 0.
```

All abbreviations in the parent proof are implemented by the literal
binary circuit. The output N=0 is the single equation. Every variable,
fixed port and gate is live. Full coefficient payloads and their exact
bindings are under `coefficients/`; MF is already shifted exactly once.
There is no unspecified numerical constant.

## The exact saving

The parent computes the register `4Am1=4*Am1` early to obtain H'. Later,
for the transport majorant, it computes

```
Am1I=Am1*I;  4Am1I=4*Am1I.
```

Use the already available value instead:

```
4Am1I=4Am1*I.
```

The equality `4*(Am1*I)=(4*Am1)*I` holds in every commutative ring.
The deleted `Am1I` intermediate had no other use. Every other retained
gate, including the whole centered sixteen-fold norm tail, is unchanged.
Induction in circuit order therefore proves equal values at every
retained register, and in particular at the final N, for every integer
input and every integer port value. This is a pointwise polynomial
identity, not just an existence equivalence or a choice of witnesses.

`PREFIX_REMAP.json` gives every old/new gate index and name, the unique
deleted gate, the changed product and its restoration. The checker
requires complete coverage, so a missing or silently changed prefix
cannot pass. It separately checks that the earlier scalar product has
the advertised definition and that the removed gate has no other use.

## Correctness and exact degree

The original ordinary positive-zero/refutation proof, with its explicitly
inherited package61 source/calibration and Pell lemmas, transfers without
any change of hypotheses, constants or domain. It is retained as
`source/parent/PROOF.md`; the independent peer review and complete normal
and optimized parent receipts are under `source/peer/`. Both full parent
runs passed the actual fixed-port bounds, as well as all symbolic,
kernel, descent and degree audits. The original parent was never edited.

The identity transfers the reviewed degree upper bound816 and its
nonzero leading form omega0^8 at the actual beta>0. `check.py` also
independently verifies the actual28-gate tail as the495-term universal
sixteen-root norm. Its complete425-term centered expansion has unique
weight816 term omega^8. Two complete new-circuit lines at the actual
fixed tuple attain degree816 modulo large primes. The full syntactic
bound remains928. This provides both the unbounded degree argument and
additional literal controls; line tests alone are not the upper-bound
proof.

`PROVENANCE.json` pins all original files to commit
`8380e70262337360af048a88ebcd9c17b4c7808d`, the exact parent equation,
independent peer files and generator. `BUILD.json`, normal/-O `CHECK`
receipts, `VERIFICATION.json` and `MANIFEST.json` retain the finite
verification. The checker imports the independent sparse-ring oracle,
never the candidate's author builder, circuit module or verifier.
It also checks100 signed whole-circuit assignments at every retained
register and rejects a missing scalar factor in the local cut.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_scaled_shared.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-scaled-norm-shared/check.py
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_scaled_shared.py --check
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-scaled-norm-shared/check.py
```

This improves the parent's operation count at the same degree and domain.
It trades fewer unknowns against the canonical13-positive90-operation,
degree51 page. No canonical PDF or frozen parent has been replaced, and
no global optimality is claimed.

Lean formalization remains paused. The ordinary arithmetic equivalence
and finite certificates do not supply the outstanding encoded
internal-ZFC derivation or prove consistency/absence of zeros.
