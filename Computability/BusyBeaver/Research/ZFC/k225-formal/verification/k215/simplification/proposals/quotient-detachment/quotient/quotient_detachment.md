# Quotient detachment: a tag-blind inference rule for the K215 code algebra

## Status and purpose

This note gives a new semantic inference theorem and its consistency-level consequence for the numerical calculus and command enumerator. Four accompanying Lean files kernel-check the theorem for the repository's actual `Code254` decoder and the full unconditional refutational equivalence of the enlarged `Q222` calculus with ZFC. The command-compiler transfer and exact quotient macro contracts have ordinary mathematical proofs; their changed source-to-tape endpoint has not been formally checked. This does **not** assert a 214-state binary realization. A literal source implementation and its physical allocation have separate costs. The result leaves every axiom and formula constructor unchanged.

The inspected code algebra is ProveIt's `Code254`: Cantor pairing

    P(a,b) = (a+b)(a+b+1)/2 + b,
    I(a,b) = 4P(a,b),
    M(a,b) = 4P(a,b)+1,
    Q(a,b) = 4P(a,b)+2,
    E(a,b) = 4P(a,b)+3.

Truth is 0, with the alias I(0,0)=0. Falsity is 1=M(0,0). Decoding interprets M as membership, Q(a,b) as universal quantification of the formula decoded from b by variable a, and E as equality. The proof uses the repository's proved semantic constructor laws; it does not require codes to have a separate well-formedness certificate.

## The semantic theorem

Let D contain two distinct elements, let R be an irreflexive binary relation on D, and interpret the native codes in this structure. Define

    Valid(n) iff for every assignment e : Nat -> D, Sat(e, dec(n)).

**Quotient-detachment theorem.** For every natural a,b,h,

    Valid(a) and Valid(h) and floor(h/4)=P(a,b) imply Valid(b).

Proof. Write h=4P(a,b)+r, where 0<=r<4, and distinguish the four residues.

1. r=0. The constructor identity gives h=I(a,b). Its semantic law gives Valid(a)->Valid(b), including the collapsed h=a=b=0 case.
2. r=1. Then h=M(a,b). A constant assignment gives R(d,d), contradicting irreflexivity. Thus Valid(h) is impossible.
3. r=2. Then h=Q(a,b). At an arbitrary assignment e, instantiate the universal quantifier with e(a). Updating e at a with its current value leaves e unchanged, proving Sat(e,dec(b)).
4. r=3. Then h=E(a,b). If a and b were different numerical variable indices, assign distinct domain elements to them. This contradicts Valid(h). Therefore a=b as natural numbers and the first premise is exactly Valid(b).

This proves the theorem for all raw natural codes. The equality case is about equality of **variable indices**, forced by validity under *all assignments*. It is not an unjustified inference from equality at a single assignment.

### Both semantic hypotheses matter

Two elements cannot be weakened to nonemptiness alone. In the one-element empty-membership model, a=0 and h=E(0,1)=11 are valid, floor(11/4)=P(0,1)=2, but b=1 is false. This is a concrete counterexample to the one-element version.

Validity cannot be replaced by truth at one assignment. In a two-element empty-membership model at a constant assignment, the same a=0,h=11,b=1 is a counterexample. Universally quantified assignments are part of the invariant.

## Enlarged numerical calculus

Let D be the accepted dominated numerical calculus. Form Dq by retaining truth, all its axiom instances and theorem-only generalization, and replacing ordinary numerical MP by

    from a and h, infer b whenever h div 4 = P(a,b).

Every original MP step is a Dq step: I(a,b) div 4=P(a,b). Hence every D refutation is a Dq refutation.

Conversely, the existing consistency-to-model direction provides, from Con(ZFC), an irreflexive model satisfying the native axiom bundles. Choose the model supplied by the ZFC interpretation; it has at least two elements. The unchanged axiom soundness proofs, theorem-only generalization, and the quotient-detachment theorem show inductively that every Dq derivation is valid under all assignments in that model. Code1 is self-membership and is false. Therefore Dq cannot derive 1 when ZFC is consistent.

Combining the two directions with the inherited D/ZFC calibration gives

    Dq derives 1 iff ZFC has a finite refutation.

This is a refutational calibration. We do not claim equality of the D and Dq theorem sets, and do not need it. Classical contraposition converts Con(ZFC)->Con(Dq) into Dq-inconsistent->ZFC-inconsistent. The argument can be expressed in ZFC using the existing completeness/model bridge. No Con(ZFC) assumption remains in the final equivalence.

### Kernel-checked calibration

The formal `Q222` relation starts with the original `C222` theorem set, and closes it under quotient detachment and theorem-only generalization. In particular no reconstruction of the seed-axiom derivation infrastructure is required.

* `QuotientDetachment.lean` proves the all-natural semantic theorem using the actual native-code constructor laws. It also checks the one-element and single-assignment counterexamples above.
* `Quotient222.lean` proves soundness of `Q222` in every irreflexive model with two distinct elements satisfying the existing seed bundles, and preservation of all original `C222` refutations.
* `QuotientCalibration.lean` uses `KUpper222.bundles_in_L`. The empty set and its successor are two distinct elements of the existing constructible interpretation. First-order completeness then turns a `Q222` refutation into a ZF refutation.
* `QuotientEquivalence.lean` embeds the existing lower-bound argument through `Q222.base`, then applies `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Its final theorem is exactly

      Q222 Code254.F ↔ BProv ZFCax_s [] Form.fBot.

The full import closure contains 110 modules, including these four new modules. The final self-contained bundle was rebuilt cleanly: all 110 modules were compiled from source, and no cached project `.olean` was reused. All 106 upstream sources match the Git blob IDs of pinned ProveIt commit `53269bcab1efc0f82d3022645bd7cf0c22d84959`. The final theorem's reported axioms are only `propext`, `Classical.choice`, and `Quot.sound`; neither `sorryAx` nor an added consistency axiom occurs. `bundle/verify_quotient.py` reproduces this clean build, checking every source hash first. Its build manifest records individual source hashes, exit codes and timings. The four new modules contain 244 lines including comments and blank lines.

## Exact replacement of the command interface

The existing MP command is

    let b=d+x;
    if h=4P(t,b) then (b,P(0,w),b,0) else (0,w,b,0).

Replace its guard only:

    let b=d+x;
    if h div 4=P(t,b) then (b,P(0,w),b,0) else (0,w,b,0).

The tuple is (top,stack,counter,cache). All command tags, field arities, stack effects, returned counters and cache cleanup are unchanged. In particular this is not the parameter-free destructor operation, which would remove the counter-loading interface used by the present AX compiler.

For soundness use the semantic invariant Valid(top), Valid(cache), and validity of every head of the numerical stack. Truth0 initializes it. DROP and NIP merely move valid formulas, successful quotient MP is justified above, unsuccessful MP inserts truth, and AX has the unchanged axiom/generalization soundness. The only alarm remains cache=1. Thus a halting run yields a Dq refutation, or directly contradicts the semantic invariant in a consistent ZFC model.

For completeness, the inherited strong block compiler continues to work without a changed command list. Its MP calls occur in only the following forms:

* genuine inference: h=4P(t,b), where the new guard succeeds exactly as before;
* discard/reset: h=0 and b=1, where P(t,1)>0 so both guards fail;
* positive counter loading J(u): t=h=0 and b=u>0, where P(0,u)>0 so both guards fail;
* J(0) is the empty block and makes no call.

Therefore every MP call used by a compiled derivation has exactly its old result. A structural induction on the inherited block compiler transfers its contracts. The AX reset prefix, cofinal candidate family, and strictly draining reader use the unchanged field arities, so their completeness proof transfers as well. The initial K215 seed has top/cache/stack zero and permits the semantic soundness invariant.

The result is an all-natural command-enumerator consistency equivalence. A binary table implementing it must still prove the exact quotient guard and normal-return cleanup, bind its entire source, and have a verified blank startup.

## Physical implementation cautions

1. Changing only a shared numerical equality routine globally is invalid: that routine also gates AX and other operations.
2. The new guard is h in [4P(t,b), 4P(t,b)+3], not h>=4P(t,b). The upper bound is essential.
3. A quotient scanner must return the exact promised cache/counter/scratch values. A destructive division remainder cannot be ignored if it is later reused.
4. Accepting more hypotheses may permit a smaller implementation, but it can also add source roles. The semantic theorem does not imply a state saving.
5. A failed finite allocation search is not a lower bound. The useful output of this note is a verified semantic freedom that exact source-equivalence searches would reject.

## Provenance

All constructors, native axiom families, dominated-rho8 recovery, original numerical-calculus/ZFC calibration, and the four-command compiler are inherited from Vladimir Reshetnikov's ProveIt project. The quotient-detachment argument, its sharp semantic counterexamples, the enlarged-calculus model adapter, the guard replacement, and the compiler-transfer audit are the new contribution of this note. The lower-bound proof in `QuotientEquivalence.lean` copies the existing six-line mathematical argument from `KEndpoint.c222_of_zf_refutation`, followed by the new embedding constructor; it imports `KLowerQHyp` directly to avoid unrelated machine simulation dependencies. The accompanying finite-model checker corroborates the semantic cases; the all-natural inference and refutational-equivalence proofs are kernel checked independently of that checker.
