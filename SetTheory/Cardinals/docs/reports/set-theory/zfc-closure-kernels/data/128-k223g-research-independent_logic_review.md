# Independent review of the merged equality/helper calibration

**Verdict:** the uniform native-calculus interderivation in
`merged_euclidean_helper_calibration.tex` is sound. I found no circular use
of deleted equality axioms, no illicit generalization of an assumption,
and no missing diagonal or zero-label case. The finite exported DAG also
passes a separate parser/checker that imports no generator code.

## The potentially circular step is valid

The new G row does not initially conclude an unquantified equality. This
makes ordinary reflexivity look unavailable until equality vacuity is
known. The proof escapes that cycle as follows. For arbitrary x let
z = κ(x,x), e = Eq(x,x), and d = Eq(z,x). The instance G(x,x,z), followed by
propositional contraction, yields the theorem d → Q_z e. Existential
monotonicity therefore gives ∃_z d → ∃_z Q_z e. Row ρ1(z,x) gives its
antecedent, and ρ6(z,e) gives e. Neither the old helper H nor old ρ7 is used.

G(a,b,a) and this reflexivity theorem now derive the exact deleted helper
H(a,b) = Eq(a,b) → Q_{κ(a,b)} Eq(a,b), including a = b. There is no freshness
condition on any of these syntactic derivations.

The next elimination step is also valid. Using ρ1(i,i), normal quantifier
distribution ρ2 and classical propositional logic, one derives seriality
Q_i A → ∃_i A. Applying it to Q_i A and then ρ6 yields the **two-quantifier**
principle Q_i Q_i A → A. Generalizing the closed H derivation and applying
ρ2 gives Q_i e → Q_i Q_i e for i = κ(a,b). This particular equality formula
therefore satisfies Q_i e → e. Composing with G recovers the literal old
ρ7. The proof never assumes a uniform one-quantifier elimination theorem.

The reverse derivation is the immediate propositional composition of old
ρ7 and old H. This proves equality of all native theorems, rather than
merely an interpreted equality result.

## Propositional closure does not introduce a hidden equality premise

The unchanged row ρ8 gives the implicational classical basis K, S, and
Peirce through the pinned `CD230.v` derivations. I checked the actual
`Comp_Prop230.v` proof of `thm_F`: K gives F → ∃_0 Q_0 A and retained ρ6
then gives F → A. The resulting Boolean-tautology bridge therefore needs
neither old ρ7, H, G, nor any set-theory axiom. Treating native F = 1 as the
false constant in TAUT leaves is justified by this bridge, even though
its decoded expression is Rel(0,0).

Here “closed derivation” means no open hypotheses. Its conclusion may
still contain free numeric variable labels; this does not prohibit theorem
generalization. No part of the reviewed proof generalizes an open hypothesis.

## The gated bundle supplies the full old helper family

The old bundle is ¬(K → (RV → ¬H)); the new bundle is ¬(K → ¬RV). The three
claimed projections/recombinations are Boolean tautologies. For each pair
(a,b), selecting c = max(a,b) + 1 satisfies the unchanged gate, so the old
bundle supplies H(a,b) for every pair. The selected gate parameter need
not equal G's third argument. Conversely, the new G family supplies H
for every pair, allowing reconstruction of each old gated bundle from
its corresponding new bundle. No K theorem or equality interpretation is
needed for these propositional extractions.

The source checker `check_g_emitter.py` verifies the independent logical
ρ7 slot is replaced by exact G, verifies the exact new bundle, compares the
entire changed primitive word, and matches the full guarded control-flow
graph against a reference composed from closed macros. Thus G is not
mistakenly restricted by the bundle's gate. The other seven logical slots,
the number of pushed formulas, the gate, and proof-enumeration control are
retained.

When adapting the old reset/cofinality text, both the changed G formula
and changed bundle must be mentioned. Both are implication codes, hence
multiples of four and different from target F = 1; the disabled bundle
remains 0. The old sentence saying that only the bundle's identity changes
would be inaccurate for this construction. The eight-slot DISCARD protocol
is unchanged.

## Internal theorem and proof status

The intended internal conclusion is

    ZFC ⊢ Nonhalt(M223, blank) ↔ Con(ZFC).

The derivation is a composition of explicitly different obligations:

1. The local fold certificate proves Halts(M223) ↔ Halts(parent226), in fact
   for every initial tape and head position from start state 0.
2. The quantified binary runtime proof, literal startup, and unchanged
   enumerator/reset/cofinality argument prove Halts(parent226) ↔ Thm_G(1).
3. The uniform closed derivations give Thm_G(n) ↔ Thm_224(n) for every
   native code n, by replacement of axiom leaves and induction on proofs.
4. The pinned K224 mathematical calibration proves
   Con(T_224) ↔ Con(ZFC), where Con(T_224) means ¬Thm_224(1).
5. Negating the halting equivalence gives the displayed theorem in ZFC.

These proof translations use finite syntax, computable κ and fresh gate
selection, and induction on finite derivations. They are formalizable in
ZFC and do not assume Con(ZFC), soundness of ZFC, or omega consistency.
They return to the exact previously calibrated native theory; they do not
need a new set-theory interpretation for G.

The new theorem remains a mathematical internal-provability theorem with
finite certificates and inherited formalized ingredients. It must not be
presented as an already completed new Rocq or Lean endpoint for M223.

## Independent finite replay

`review_logic.py` separately validates every exported proof node, including
topological MP and GEN references, exact axiom schemas, Boolean tautologies,
and the absence of old-theory leaves in forward derivations or G leaves in
reverse derivations. It rejects every unsupported rule; there is no open
hypothesis rule. Replay passed 315 nodes, 290 formulas, and 33 roots:
144 MP nodes, 22 GEN nodes, and 75 TAUT leaves. The input proof SHA-256 is
`622653bffd6b72e952344a8439d012c3bd6ee33917880830196bc175d89f03c5`.

Run:

    python3 review_logic.py merged_euclidean_helper_proofs.json --output logic_independent_review.json

The numerical instances include repeated labels, label zero, and large
labels. The finite replay supplements the uniform parameterized argument;
it is not used as a substitute for that argument.
