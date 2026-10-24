# Exact inherited endpoint and the ordinary direct-source proof chain

This supplement makes the logical endpoint of the direct quartic proposals
reviewable without treating a source README as a new theorem. It accompanies
the unchanged archive `ConZFC_407_888_Quartics_2026-10-24.zip` and the new
`equal_sum589` and `even_index566` packets. All later repository files were
downloaded byte for byte at commit
`84e16e43092614bae262ca59651cb9d77e31a255`; their exact repository paths,
lengths, Git object digests and SHA256 hashes are in `REPOSITORY_PINS.json`.

## 1. The actual syntactic consistency predicate

The inherited file `calibration/Bridge.lean` defines

```lean
def ConZFC : Prop := ¬ BProv ZFCax_s [] Form.fBot
```

Thus the target is absence of a finite proof of contradiction from the
repository's actual ZFC axiom predicate. No bounded-consistency predicate,
selected finite fragment, termination bound or assumed model of ZFC is
substituted for this target.

`calibration/Code254.lean` defines `F : Nat := 1`.
`calibration/KCode222.lean` gives the entire inductive numerical calculus
`C222`, with truth, modus ponens, generalization, eight unconditional axiom
schemas and the guarded seed bundle. It also gives the exact arithmetic
constructors used by the direct source.

## 2. The unconditional calibration theorems

In namespace `SetTheory.BusyBeaver.ZFC.KEndpoint`, the supplied inherited
`calibration/KEndpoint.lean` proves:

```lean
theorem c222_iff_zf_refutation :
    KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  ⟨KUpper222.zf_refutation_of_c222, c222_of_zf_refutation⟩
```

In namespace `SetTheory.BusyBeaver.ZFC.ConstructibleChoice`, the supplied
inherited `calibration/ConstructibleChoice.lean` proves:

```lean
theorem zf_refutation_iff_zfc_refutation :
    BProv ZFax_s [] Form.fBot ↔ BProv ZFCax_s [] Form.fBot :=
  ⟨BProv_theory_mono (fun _ hb => Or.inl hb), choice_refutation_remove⟩
```

Their composition gives exactly

\[
 C_{222}(1)\ \longleftrightarrow\
 \operatorname{BProv}(\mathrm{ZFCax}_s,[],\bot).
\]

These two named theorems have no machine-specific premise. The later
machine endpoint section in `KEndpoint.lean` is not used by the direct
quartic construction. The Choice transport is the inherited constructible
universe proof of ZF/ZFC equiconsistency; it is not an additional
consistency assumption.

The five Lean files and `CALIBRATION_PINS.json` are exact copies of members
of the immutable 407/888 archive. That archive pins their original Git
sources at commit `08200eb10fde2db408c69dffd840d6920a569b1f`. The full paths
and hashes are in `ARCHIVE_MEMBER_PINS.json` and the inherited
`CALIBRATION_PINS.json`. The two commits have different roles: the earlier
one pins the logical source; the later one pins the archive and subsequent
arithmetic research.

**These are inherited Lean source theorems, not newly compiled proofs.**
This submission has not rebuilt their transitive Lean imports, nor does it
supply a new Lean theorem for either final quartic or a kernel-checked
internal ZFC derivation of the complete polynomial equivalence.

## 3. The direct arithmetic compiler in the immutable archive

The accompanying archive has SHA256
`59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`.
Paths in this paragraph are relative to its top-level directory
`ConZFC_407_888_Quartics/`.

* `upstream/code/direct_source.py` and
  `upstream/code/direct_source_factored.py` contain the literal arithmetic
  source and its factored axiom disjunction.
* `upstream/proofs/factored_source.md` justifies the branch factoring.
* `provenance/prior_projection_proof.md` proves branchwise removal of
  deterministic constructor and label coordinates; proof-tree padding;
  the exact large-base Horn balance criterion; and the sharpened bounded
  CRT encoding. Its rule table is precisely the C222 calculus above.
  Its finite Horn-balance proof explicitly permits cycles and repeated
  premises, using single-conclusion rules and nonnegative multiplicities.
* `proofs/radix_and_pell.md`, `upstream/proofs/shared_powers.md` and the
  inherited representation sources supply the arithmetic replacement of
  power, factorial, binomial, remainder and bounded-family interfaces.
* The archive's finite source and projection checkers bind these ordinary
  arguments to its explicit coefficient files.

`repository/PROPOSAL_REVIEW_DIRECT_C222_ROUND12.md` reviews the original
rule/source binding. `repository/PROPOSAL_REVIEW_QUARTICS407888.md`
reviews the subsequent complete arithmetic chain and records authentication
of all seven logical calibration pins against their original Git objects.
Those historical review receipts are inherited evidence, not a claim that
the current submission reexecuted all their historical checks.

## 4. The later radius and domain transformations

All paths in this section are beneath `repository/`, mirroring
`Computability/DiophantineConsistency/` in the pinned repository.

| Stage | Ordinary proof supplied here |
|---|---|
| Candidate-output factorial radius | `candidates/synchronized-factorial-radius/PROOF.md` |
| Projected low-digit source with both new radii | `candidates/projected-factorial-radius/PROOF.md` |
| Literal natural-to-integer sign conversion | `candidates/projected-radius-integers/PROOF.md` |
| Mixed-domain recovery and fresh comparison witnesses | `candidates/projected-radius-mixed/PROOF.md` |
| Two preliminary carrier/discriminant signs | `candidates/projected-radius-mixed-bounds/PROOF.md` |
| Five semantic-prefix signs | `research/guard-seed-consequences/README.md` |
| Two private sign normalizations | `research/guard-sign-orbits/README.md` |
| Fifteen main-root and six modulus signs | `research/main-root-and-modulus-signs/README.md` |
| Signed comparison base and its existential lift | `research/comparison-base-sign/README.md` |
| Local factorial recovery of index guards | `research/paired-index-guards/LOCAL_FACTORIAL.md` |
| Factorial-radius guard replacement | `research/factorial-radius-guard/PROOF.md` |
| Early power-output sign recovery | `research/factorial-radius-output-sign/PROOF.md` |
| Exact 75-predicate parent and source pins | `research/factorial-radius-output-sign-profile/README.md` and `SOURCE_PINS.json` |

These documents state existence equivalences at their exact domains. Some
steps change private witnesses: they are not claims that arbitrary signed
tuples were natural all along. In particular, the comparison-base lift is
performed only after its signed-index soundness proof. The natural
arithmetic source is interpreted only after the necessary sign and power
interfaces have been established in the specified order.

`SIGNED_INDEX_THEOREM.md` is copied exactly from
`con_zfc_batched_pell/proofs/SIGNED_INDEX_THEOREM.md` in the separate
`docs/incoming/ConZFC_Shared_Pell_1873.zip`. Both archive and member hashes
are recorded in `SIGNED_INDEX_PIN.json`. The ordinary signed-base extension
is then proved in the comparison-base document listed above. The accompanying
`repository/PROPOSAL_REVIEW_SHARED_PELL1873_SIGNED.md` records the earlier
review of the signed-index argument.

This supplement includes the ordinary proofs, exact pin files and immediate
logical sources. It does not reproduce every historical generator or every
historical finite certificate. Those remain at the exact pinned paths; the
complete immutable 407/888 packet is supplied separately. The new direct
packets do supply their own complete polynomial lists, projections and
independent finite checkers.

## 5. Where the new quartic arguments enter

The 589-variable packet starts from the literal 75-predicate source and
replaces seven pairs of nonnegativity predicates by product predicates
with independently retained nonnegative sums. Its proof first restores all
old signs at the same body tuple, then applies the inherited source theorem.
All final signed projections have explicit unique inverse polynomials.

The 566-variable packet goes further: it certifies every output square
at a doubled exponent, supplies a frame bounding those squares, corrects
the one derived pair to a two-step Pell addition, and deletes the now
redundant index predicates. `proofs/even_power_compiler.md` gives a fresh
ordinary soundness and completeness proof, including sign branches and
simultaneous finite-ring/CRT reconstruction of all private witnesses.
Its independent checker verifies the complete front-sign dependency,
all 21 power calls and 15 seed interfaces, all 60 body edits, and all
finite projections and coefficient expansions. It does not substitute
finite tests for the unbounded Pell and CRT arguments in that proof.

The resulting ordinary proof chain is

\[
\begin{aligned}
\exists\mathbf z\in\mathbb Z^{566}\;Q_{566}(\mathbf z)=0
&\ \longleftrightarrow\ \text{the literal direct arithmetic source has a certificate}\\
&\ \longleftrightarrow\ C_{222}(1)\\
&\ \longleftrightarrow\ \operatorname{BProv}(\mathrm{ZFCax}_s,[],\bot).
\end{aligned}
\]

Negating the existential gives the intended consistency equivalence.
The claim here is an ordinary mathematical proof by composition of the
supplied arguments and the exact inherited calibration. The new arithmetic
arguments use finite algebra, induction, elementary number theory and CRT,
and are suitable for formalization in ZFC. Their formalization status is
separate from the fully materialized polynomial and its independently
checked finite algebraic data.

The use of the name C222 does not introduce a hidden appeal to K215 or to
Jones' universal Diophantine polynomial. The directly encoded object is
the finite proof-rule calculus displayed in `KCode222.lean`.
