# Basic conventional HA arithmetic: author receipt

Author: `circuit_reduction`. This is an author review and fresh leaf build,
not an independent peer review. All new source and driver text was read before
execution, and both final Lean files were reread before freeze. No accepted
source, shared object, umbrella, vendor file or Git state was edited.

## Frozen files and build

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/HABasicArithmetic.lean` | 225 | `7922744c26ffd0b307b019696197aaa3cdb5acd49ed173e158d6e3a29011e3a2` |
| `Lean/DiophantineConsistency/HABasicArithmeticChecks.lean` | 97 | `507febd4d89db8fbe287711ab46c314726cc6df226e181bee0344b6b3a9b129c` |
| `reviews/ha-basic-arithmetic-dependency-replay.json` | — | `b37b7d19eb26260cc521fc91d197795aea4fcfb40017dfc45bc489e9167fa761` |

Final source/object compatibility was rechecked at repository snapshot
`cbfdd02ce4dee136d1344e3d65cda6fcb6551700`. Seven custom prerequisites were
reused under the pinned PAHF/HA manifest: the five PAHF closure modules,
`HAProofs`, and `HADeduction`. The only new import is `HADeduction`.
No Foundation or native-equation closure was built or imported by this packet.
No prerequisite was freshly rebuilt; the two new leaves were freshly compiled.
The compiler/toolchain/package pins, all selected source/object hashes,
commands, logs and terminal exit codes are preserved in the JSON receipt.

Both sequential direct builds used `-M6000 -j1`, source-level
`Elab.async false`, and private overlay `/tmp/ha-basic-arithmetic-chrl44rk`.
Both final terminal exit codes are zero. The main's final log is empty.
All 19 focused axiom reports use only `propext` and/or `Quot.sound`.
There are no final warnings, custom axioms, `sorry`, `native_decide`,
`Classical.choice`, model semantics or classical PA proof conversion in the
new theorem dependencies.

Fresh main object:
`9ac98d23ef023abd264c329ecfdf3a628f94604157bfaf4419ace8c7be6b9bfd`.
Fresh checks object:
`156f0ccf5f17eaaf0f370ab17b2c15ff20562bb63d00e6b3771a5467048845f1`.

## What was proved

The equality library constructs actual `HA.Derives` trees for symmetry,
transitivity and congruence through an arbitrary one-hole term. The hole is
index zero and ambient terms are explicitly shifted. Finite relative-proof
versions preserve the actual axiom lists and include successor, both addition
positions and both multiplication positions.

Relative universal elimination is the existing HA elimination constructor.
Relative universal introduction requires the explicit condition
`Formula.Sentences B`, proves that the finite axiom list is invariant under
the eigenvariable shift, and uses the actual shifted-context HA rule.
`Relative.close` therefore does not generalize over an unshifted free theory
assumption. `Relative.open_rename` requires every free index of the formula to
be below its supplied closure count, and reopens every quantifier while
preserving all parameters. Its zero-closure case requires a sentence; its
successor case uses the actual PAHF instantiation/renaming identities.

`Arithmetic.axiom_body` opens an actual member of `Formula.Ax_s` after proving
the closure covers all free indices. It is instantiated with the six explicit
sealed axiom-membership theorems to obtain arbitrary-term `HA.Proves` results
for successor injectivity, successor nonzero, addition by zero and successor,
and multiplication by zero and successor. It does not assume that a translated
Foundation arithmetic formula is an HA axiom.

`Arithmetic.induction` opens the actual sealed `Ax_s_induction` instance and
combines its zero and universal-successor premises by HA conjunction and modus
ponens. `Arithmetic.zero_add_all` applies that object-language formula-induction
rule to `0+x=x`; it is not obtained from a metatheoretic induction argument or a
standard-model equality. `zero_add` specializes the resulting theorem to any
term. `add_one` proves `t + S 0 = S t` from actual addition axioms, equality
congruence and transitivity, supplying the previously missing arithmetic
identity needed when the Foundation syntax uses `t+1`.

## Focused checks and limitations

Checks include a repeated-hole nonlinear term context with an ambient free
variable, arbitrary-term arithmetic instances with several distinct free
parameters, and an induction formula containing another quantifier and a free
parameter. Exact zero substitution removes the induction slot and shifts the
parameter, whereas successor substitution preserves that parameter slot.
A complete HA induction proof for that nested formula is checked. Reopening a
two-variable closure under a nontrivial renaming retains the inner bound
variable and both free parameters. Zero closure, arbitrary reclosure counts,
and the six axiom interfaces are also exercised.

Existing `PASyntax` classical `BProv` proofs were read as a guide to their
binder bookkeeping. None is called: all proof constructors used here are the
intuitionistic `HA.Derives` rules or the already checked finite `HA.Relative`
combinators. Existing PAHF syntax identities and axiom membership/closedness
lemmas are reused. The metatheoretic inductions in the closure helpers are
structural proofs about finite syntax, separate from the actual object-language
induction used in `zero_add_all`.

This packet does not yet prove every Foundation PeanoMinus/order/equality
axiom, arbitrary translated induction preservation, or the final HA proof of
the current consistency equivalence. It provides concrete conventional HA
arithmetic proofs for the next adapter layer; it does not duplicate GG.
