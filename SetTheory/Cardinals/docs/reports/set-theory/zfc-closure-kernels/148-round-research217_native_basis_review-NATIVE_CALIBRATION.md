# Exact native calibration of the two-row H/PW basis

Date: 2026-10-20. Independent fixed-certificate replay, not a proof-assistant compilation or a source-size claim.

Let native I(a,b)=4P(a,b). Replace only unrestricted rho8 by

`H(p,q,r)=I(I(p,q),I(I(q,r),I(p,r)))`,

`PW(p,q,r)=I(I(I(p,q),p),I(r,p))`.

Retain all other rows, the complete gated seed/support bundle, raw truth, MP, and GEN.

## Independently replayed evidence

The literature lane supplied a fixed 12-line proof with two axiom schemas and ten CD conclusions. I did not run its search or checker. The newly authored `replay_h_pw.py` reads the data and checks each supplied explicit simultaneous substitution and each exact MP equality, without unification or enumeration. It confirms Peirce at line 10 and K at line 12. Receipt: `H_PW_NATIVE_REPLAY.json`.

The same lane extracted the finite [Metamath Tarski-Bernays proof](https://us.metamath.org/mpeuni/tarski-bernays-ax2.html). I checked that its imim1 is exactly H, and independently replayed all 97 data rows with `replay_hkp_s.py`: 4 K instances, 40 H instances, 5 Peirce instances, and 48 exact MPs. The final formula is S. Receipt: `H_K_P_S_NATIVE_REPLAY.json`. Neither checker executes received code or performs a formula search.

## Why these schematic proofs transfer to every native code

Interpret each free schematic parameter as an arbitrary natural number, and each implication node as the numeric function I. Structural equality of the major's antecedent and the minor becomes exact equality of the native numbers, so every recorded MP remains valid.

A use of a previous schema with a displayed substitution means applying its already-proved universally quantified numerical statement to those constructor terms. It is not an object-language theorem-substitution rule and not a renaming of decoded relation labels. Fresh proof-variable namespaces are only meta-level parameters. Additional zero aliases under I(0,0)=0 cannot invalidate an equality or an MP step. The positive replay does not rely on free-algebra injectivity in the native interpretation.

Thus the proof supplies native K, S, and Peirce uniformly for all natural parameters. It does not need truth0, equality, quantifier axioms, or any seed projection.

## Exact theorem equivalence with the original native calculus

In the original unrestricted-rho8 calculus, H is exactly pinned `CD230.v` lemma cd91, and PW is exactly cd18. Hence every new axiom has a finite old proof.

Conversely K/S justify the ordinary propositional deduction transformation, which uses only implication and MP. Given temporary assumptions h=(C→U)→A and k=A→C, assume C→U, obtain A and then C by MP, and discharge the last assumption. This gives (C→U)→C. Peirce at C,U yields C, and K yields B→C. Discharge k and h to obtain precisely unrestricted rho8:

`((C→U)→A)→((A→C)→(B→C))`.

No GEN occurs under any temporary assumption, so there is no hidden quantified deduction premise. The argument is uniform for all native natural codes. Replacing each rho8 leaf by this finite construction translates old proofs into new ones. The unchanged axioms, full seed, MP, GEN, and F=1 are preserved literally.

Therefore every native code is derivable in the new calculus iff it is derivable in the original calculus. In particular consistency calibration is preserved. No semantic completeness representation is needed.

## Implementation boundary

This result permits independent permutations of each three-input schema, such as emitting H(p,q,r) and PW(q,r,p), because each row is universally instantiated over all numeric triples. It does not imply a physical state count. The source lane must verify exact emitted stack order, unused or removed fourth-parser-field handling, modified source semantics, proof-search completeness, compilation, and blank startup independently.
