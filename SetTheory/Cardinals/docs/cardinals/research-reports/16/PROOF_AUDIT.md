# Proof and dependency audit

## Scope

Ambient theory: ZFC. Cardinalities and rank levels are ambient unless explicitly
marked otherwise. λ is an uncountable cardinal, not assumed regular. In every
embedding application its cofinality is shown to be ω.

OD_{V_λ} permits a single parameter p ∈ V_λ (equivalently finitely many such
parameters) and finitely many ordinal parameters. It does not permit arbitrary
parameters from V_{λ+1}.

## External inputs

1. Local Kunen inconsistency: no nontrivial elementary self-embedding of
   V_{δ+2} in ZFC. Used to normalize the critical sequence and to identify
   the fixed ordinals below λ.
2. The high-critical-point characterization of ultraexactingness
   (Aguilera–Bagaria–Goldberg–Lücke, Proposition 2.4). Used with reflection
   and a canonical least counterexample to handle low-rank parameters.
3. The existing ultraexacting/I0 equiconsistency and the suitable coding
   forcing (the same authors, Theorem 4.5 and Proposition 3.9). Used only
   in Section 8, not in the new local inconsistency proof.

## New argument

A fixed small subset A of λ has a fixed order type α < λ and a fixed canonical
increasing enumeration. Critical-sequence normalization gives α < crit(j),
so all values of the enumeration are fixed ordinals below crit(j). Such A
cannot be cofinal.

An ultraexacting witness contains its critical sequence c. Its range a is
mapped to its tail, so a and j(a) are finite-difference equivalent. A fixed
tail-invariant rule would therefore assign a fixed small cofinal set to a,
contradicting the previous paragraph.

For a small nonempty family B of cofinal ω-sets, the union is cofinal and has
cardinality at most |B| · ℵ₀ < λ. This estimate is valid even for singular λ.
Applying it to the fibre of a complete multisection gives the sharp result.

## Independent bookkeeping route

For j:(V_{λ+1},∈,T) → (V_{λ+1},∈,T), the fibre B is generally outside the
rank domain, so j(B) must not be used. Its union A ⊆ λ is inside the domain
and is definable there using the predicate T and the critical range a.
Elementarity and tail equivalence give j(A)=A directly. This yields the
critical-fibre theorem for arbitrary T, without any definability assumption.

## Points explicitly checked

- The given ordinal parameters are not assumed fixed. A least counterexample
  in a canonical OD_p well-order removes them before the embedding is chosen.
- X need not be transitive. Every object evaluated under j:X→V_θ is put in X
  by definability or elementarity.
- j(A)=A is not silently replaced with j``A=A.
- Smallness of a fibre yields smallness of its union because its members
  are countable, not because λ is regular.
- T and a finite-difference class have rank λ+1 and are not elements of
  V_{λ+1}; the local proof treats T as a predicate.
- No iteration of ultrapowers or direct-limit well-foundedness is used.
- Inner-model smallness is ambient. Choice is not assumed inside N.
- Proper-class statements use the standard class reading with set-sized
  restrictions; the local inconsistency is a set-sized assertion.
- The coding input asserts one suitable forcing, not preservation by all
  directed-closed forcing notions.

## Non-results

No inconsistency of ultraexactingness, I1, or I0 itself is claimed. No new
comparison of the consistency strengths of standard large-cardinal axioms
is claimed. The I0 equivalence in Section 8 is an attributed calibration.

No conclusion is drawn about a countable family of binary selectors on
[Q_λ]^2. Such selector functions choose classes, whereas representative
transversals choose a cofinal ω-set within each class. The small-union proof
applies to the latter objects.

The cover-exacting/strongly-compact problem and a lower-bound improvement for
the cover-exacting Prikry construction are not resolved by this continuation.

## Verification status

Detailed conventional proofs, cross-checked by the two routes above and an
additional surjectivity proof in Appendix A.3. No machine verification and
no independent referee review. Literature priority not established.
