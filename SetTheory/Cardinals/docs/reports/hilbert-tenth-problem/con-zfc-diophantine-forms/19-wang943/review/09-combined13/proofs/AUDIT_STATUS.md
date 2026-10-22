# Arithmetic/compiler/logical endpoint audit

Pinned repository: VladimirReshetnikov/ProveIt at
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

## Findings

No new gap was found in the mathematical interfaces needed from 06-blank67.
The proof must keep the following ordering and qualifications:

1. Cancel the unconditional positive Delta to obtain an integer unit product.
   Do not infer units directly from the literal product equal to Delta.
2. Weak transport proves C>=0 only. Its exceptional boundary C=0,F=2,z=1
   can satisfy the negative transport unit. Retain it until the first-index
   sign has been recovered.
3. The normalized strong norm gives f=chi_A(m), psi_A(m)=i*c^2, and directly
   p*c|m when c=psi_A(p). This is shorter than invoking the relaxed-rank lemma.
4. Restore positive auxiliary coordinates before using auxiliary step-down.
   Recover the exact main index p=R before removing the first-index wrap.
5. Prove X=2^R using the lower-ratio estimate under X>=q; only then infer
   q^3|X and invoke the symmetric half-binomial theorem.
6. In completeness, tune dummy bits in the actual packed rank, verify parity,
   population and range at that actual rank, then invoke the Pell converse.
   A merely congruent representative does not suffice.
7. Mask inequalities and populations are necessary but not sufficient
   compiler hypotheses. Exact supports, clean bands, anchors, local relation,
   prescribed selector ordering, canonical margin and dummy control matter.

06's weaker outer bound R<q^4-q^3+q^2-1 is sufficient in this order. 08
proves a sharper bound by treating C=0 separately, but no new bound is
needed for the neighborhood reductions. 06's raw K215 compiler avoids
08's extra normalized machine and gives simpler coefficient provenance.

## Checked machine endpoint

The current source `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`
states

    BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot

and its negation as `nonhalting_iff_zfc_consistency`. This is a theorem
about unbounded finitary syntactic proof existence. BProv means existence
of a finite list of background axioms plus a formal derivation; its B is
not a proof-length bound. ZFCax_s uses a standard selector formulation of
Choice. One may define Con(ZFC) with this presentation or use ordinary
finite proof translations to another standard presentation.

This agent read the endpoint and the independent audit notes; it did not
rebuild Lean or Rocq. A theorem checked in those systems must not itself
be presented as a translation into ZFC's own proof calculus. The statement
'ZFC proves the equivalence' relies on formalizability of the ordinary
calibration and compiler arguments. No consistency or soundness assumption
is added to those equivalence proofs.

## New complete coefficient reductions

`COEFFICIENT_REDUCTION_PROOF.md` provides a cross-neighborhood compiler
(d=5^36) and a four-site compiler (d=5^28), compared with 06's d=5^67.
Both preserve the four arithmetic ports and halting language, so they can
be combined with any correctly proved arithmetic elimination using that
interface. No expanded coefficients are claimed.

## Reproduction

The recommended combined command is `python3 verify_compiler.py` from the
archive root. The following component commands are run in `compiler/`,
with Python 3 and its standard library:

    python count_blank_alphabet.py --tm k215.tm --output cross_count_verification.json
    python cross_compiler_constants.py --output cross_constants.json
    python tshape_helical.py --tm k215.tm --output tshape_count_verification.json
    python tshape_compiler_constants.py --output tshape_constants.json

The first and third count by closed categories and independently compare
with the actual predicate for all left/right pairs in 13 center classes.
The last two layouts check every native basis contribution to every tested
field position on three sparse fixtures, plus full-rotation band/anchor
support tests and modulo-five identities. The four-site checker also
passes 32 padded accepting toy tableaux, 1144 windows and overlaps, and
9152 single-cell mutations comparing old and translated local languages.
These tests support the general proofs; they do not replace them, and they
exhibit no accepting K215 run or full Pell witness.

## Provenance

`blank_helical.py`, `count_blank_alphabet.py`, `verify_k215.py` in the
compiler directory are exact copies from the 06-blank67 code directory;
their pinned SHA256 values are checked by `verify_compiler.py`.
`k215.tm` is the exact repository table, SHA256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The two new sparse compiler scripts derive from 06's `compiler_constants.py`.
Retain the repository and Andrew James Wade MIT-0 notices when packaging.

Imported mathematical references, under Computability/HilbertTenthProblem/Papers:

- `1980/FIXED_RAW_UNIVERSAL_78_PROOF.md`: center clauses, four anchors,
  two clean bands, synchronization and occupancy propagation.
- `1980/FIXED_RAW_UNIVERSAL_76_PROOF.md`: Boolean five-adic dummy control.
- `research-wip/native-stream-queue/complete75_half_binomial_compiler.md`:
  shifted masks, exact population surplus and extra dummy bit carry bound.
- 06's `proofs/pell_lemma_audit.md`: exact retained Pell interfaces and
  noncircular order of the fixed-input specialization.
- 06's `proofs/blank_helical_proof.md`: original local relation, finite
  rectangle soundness, arbitrary cyclic shifts and all helical seams.

No global optimality or proof-assistant formalization is claimed.
