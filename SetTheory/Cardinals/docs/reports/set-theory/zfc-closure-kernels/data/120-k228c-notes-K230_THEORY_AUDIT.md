# K230: theory and endpoint audit

Inspected pin: `elliotglazer/k230-rocq` at
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

This is a source audit, not a claim that this agent locally rebuilt Rocq.
The repository records two clean builds of 216 sources and final declarations
closed under the global context. The exact machine SHA-256 independently
recomputed here is
`e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.

## Exact ordinary theory

For a formula phi(y,p,q) with an arbitrary finite parameter tuple q, write

    W_phi(p,C) := (exists y phi(y,p,q)) -> exists y (y in C and phi(y,p,q)).
    H_phi(C) := forall u in C,
      ((exists p phi(u,p,q)) and forall p (p subset u -> W_phi(p,C))).

The schema is the universal closure of

    forall a forall x exists C ((phi(x,a,q) -> x in C) and H_phi(C)).

H remains required even when the root's antecedent is false. `KPrimeOrd`
contains these instances plus the four equality axioms (reflexivity, symmetry,
transitivity, membership congruence). It has no raw set Extensionality,
Foundation or Choice axiom. `KPrimeOrdIR` additionally contains
`forall x not(x in x)`.

Exact definitions: `coq/settheory/KPrimeCore.v` (`emitted_closure`,
`kprime_core`), `KPrimeTheory.v` (`KPrimeOrd`, `KPrimeOrdIR`), and `KP0.v`
(`equality_axioms`, `irreflexivity`). Matrix closure is specified by
`closedf(forall_times n(kprime_core phi))`, not by a finite external list of
matrix instances.

## Why the compact schema retains set-theoretic strength

The false matrix forces an empty object through support, even though its root
implication is vacuous. The matrix `y=a` supplies a singleton. The matrix
`y=p and p subset a`, rooted at input a and output a, forces a into the hull;
the recursive request then supplies every raw subset of a, and support excludes
every other output. This proves raw Power Set. `KPRaw.v` proves the exact
singleton and raw power formulas in natural deduction.

The remaining lower proof is an interpretation. It builds tagged raw objects,
bounded comprehension and collection; it defines a bisimulation equivalence
and quotient membership; then it proves the translated extensional ZF axioms,
including Replacement and Infinity. The quotient power proof first bounds
canonical representatives and saturates by quotient equivalence. It does not
assume a raw power set of every collection of quotient codes.

The decisive declarations are:

- `KQuotZFTransfer.K0_ZFc_inconsistent` and
  `KPrimeOrd_ZFc_inconsistent`: any reference ZF-without-Foundation refutation
  translates to a compact-theory refutation.
- `KQuotZFC.KPrimeOrd_standardZFC_inconsistent`: composes this with the
  pinned reference's `ac_reg_relcon` transport for Foundation and Choice.
- `KUpperConsistency.KPrimeOrdIR_standardZFC_inconsistent`: the reverse
  finite-refutation transfer, interpreting the compact theory in L.
- `KUpperConsistency.KPrimeOrdIR_standardZFC_equiconsistent` and
  `KPrimeOrd_standardZFC_equiconsistent`: both exact biconditionals.

`StandardZFC` is defined literally as `(ZFc phi or phi=Foundation) or
phi=Choice` in `KQuotZFC.v`; it is not a theory with a model-existence axiom.
Finite axiom witnesses are collected by induction on finite lists, not by a
metatheoretic choice assumption. The upper proof supplies explicit finite
reflection/schema-instance lists.

An ordinary mathematical explanation of the upper direction is useful. In
ZFC choose a reflecting rank level V_alpha containing a,x,q and correct about
the required existential phi instances. Let
`C={u in V_alpha : exists p phi(u,p,q)}`. A subset of any member of V_alpha
again belongs to V_alpha; reflection supplies each required witness there,
and the support cut puts it in C. The actual formal proof uses the repository's
existing constructible-hierarchy reflection library instead of this shorthand.

## Exact numerical semantics and exceptional cases

The code constructors stay at base four:

    P(a,b)=tri(a+b)+b;
    Imp=4P; Mem=4P+1; All=4P+2; Eq=4P+3; F=1.

The emitted bundle is negative conjunction of the K core and both membership
and equality vacuity. It is gated to truth code 0 exactly when c=a or c=b.
The eight original logical schemas, theorem GEN and MP are retained.
See `KCode230.v`, `coq/logic/Codes230.v`, and `Thm230.v`.

The designated falsity code is the membership atom Mem(0,0). Irreflexivity is
therefore used in the bridge to genuine falsity. It is not safe to erase IR
or replace the decoder by an ordinary syntax decoder without this bridge.

`KDecoder230.v` deliberately decodes code 0 to a closed tautology. Its
implications to code 1 decode as primitive negation. `KDecodeFresh.v` proves
all positive code names are below the code, plus a separate closed-code-0
case. `KDecodeEncode.v` establishes the literal roundtrip on the fragment
excluding Mem(0,0), with double-negation padding making matrix codes greater
than 3 for the selected active names 1 and 3.

`KDecodeComplete.v` handles all enabled/disabled gate cases and both a=b and
a!=b. The coincident-role case in `KDecodeDegenerate.v` uses empty objects
and hosting, with object-level excluded middle; it is not silently excluded
from enumeration. `decoded_core_derivations_equivalent` compares the full
decoded and ordinary finite-proof predicates.

## Closed endpoint chain

The final proof in `coq/tm/Correct230.v` is explicit:

    TM blank halting
      <-> RM halting from ([],R0)                  [Sim230Main.tm230_rm]
      <-> enumerator halting from seed230         [Main230.prog230]
      <-> thm230 1                               [Seed230.seed230_iff_thm]
      <-> KPrimeOrdIR proves contradiction        [Bridge230]
      <-> StandardZFC proves contradiction        [KUpperConsistency].

The seed is `mkState 0 3 0 0 3 0`, not an assumed empty initial enumerator.
The bootstrap is checked at 408419 transitions. It reaches dispatcher 84 with
181 gap zeros and physical registers `[0,0,0,3,0,0,3,0,0]`, followed by 167
spare blocks of value 1. The finite register-program certificate is checked
in both directions by `ProgramBisim230.v`.

The exported statements are external Rocq theorems, and the repository
expressly does not supply an internally encoded PA proof. The finite syntax,
proof-translation and simulation arguments give the ordinary mathematical
route relevant to the user's ZFC-formalizability goal. An internal PA theorem
must not be claimed merely from the external result.

## Source audit and limitations

Removing nested comments and scanning all 99 files under `coq/` found no
`Axiom`, `Axioms`, `Admitted`, `admit`, `Parameter`, or `Parameters` token.
Two compatibility files bring the local build-source count to 101. Existing
`Hypothesis` declarations are section-local contracts in generic simulation
or bisimulation modules, subsequently instantiated by the final proof.

The reference utility `LibTactics.v` contains axioms and an unused admit tactic,
as documented upstream. Their presence in the loaded environment is distinct
from dependence of either final theorem. `AuditCorrect.v` runs `Print
Assumptions` on the two final declarations; `build.py` requires both reports
to say `Closed under the global context`, with no `Axioms:` report. Independent
kernel rechecking is available through `--coqchk`.

This audit found a complete source theorem chain and no placeholder in the
local proof. Actual local compilation/kernel success must be stated from the
root agent's toolchain evidence if it is performed. A new smaller table needs
its own source-preserving simulation or fold proof; the frozen 230-state
theorem does not prove an edited table by itself.

## Reproduction pin and citations

All paths above are relative to
`https://github.com/elliotglazer/k230-rocq/tree/3142e4dd980f0be12f4abb636c4ae2528afc17eb`.
The pinned reference is `jeff87654/busy-beaver` at
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`. The documented exact toolchain is
Rocq 9.1.0, rocq-stdlib 9.0.0, OCaml 4.14.2. Recorded clean builds are source
claims in `provenance.json`, distinguishable from a fresh independent run.
