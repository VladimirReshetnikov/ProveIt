# Focused editorial corrections and qualifications

These proposals refer to snapshot `28357e8ca63dd78327db91d9be239d75e4462879`. They are not a claim that every chapter was audited. The corresponding discussion and derivations are in Section 10 of the accompanying article.

## 1. Separate Clausen weight parity from conjugation parity

**File:** `Analysis/Polylogarithms/docs/manuscript/chapters/02-cyclotomic.tex`  
**Location:** “The fundamental constants, by conductor,” source lines 193–200 at the pinned snapshot.

The phrase “Odd Clausen values use the odd character sector” is ambiguous and conflicts with the chapter's declared convention when “odd” means odd weight. That convention uses the sine/imaginary part for even-weight Clausen functions and the cosine/real part for odd-weight Clausen functions.

Replace that sentence with:

> Sine-series (conjugation-odd) components use the odd character sector. With the stated convention, odd-weight Clausen values are cosine components and therefore use even characters.

This correction clarifies terminology; it does not reject the subsequent weight-two Clausen formulas.

## 2. Do not turn an unsuccessful reduction search into nonreduction

**File:** `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`  
**Location:** “Family 2: antisymmetric reductions to the `(i,1)` algebra,” source lines 401–414.

The sentence currently says that at higher weight the antisymmetric parts “do not reduce against the `(i,1)` basis alone.” The immediately following discussion itself explains why numerical relation searches can miss reductions, so the unconditional wording is too strong unless a separately identified obstruction theorem proves the intended claim.

Suggested replacement for the concluding sentences of that subsection:

> Such reductions were found at weights 2–4 at the mixed points and at weight 3 at `(i,i)`. At higher weights, the reported searches did not find reductions against the specified `(i,1)` basket. This is a statement about those searches, not a proof of numerical nonreduction. Exact shuffle relations and a precisely declared formal quotient are needed to determine which directions survive the available relation vocabulary.

A formal quotient obstruction, where available, should be identified by its exact presentation. It still does not imply independence of the evaluated numerical periods.

## 3. Qualify integral certificate transport through Fourier coordinates

**File:** Chapter 2, the finite Fourier bridge and certificate-transport discussion.

The Fourier identities are valid. The additional integral qualification is:

> Fourier transport gives exact linear identities over the specified cyclotomic coefficient field. It is not automatically a unimodular equivalence of integral lattices: inverse Fourier matrices introduce group-order denominators. To transfer integral Smith factors, either specify an appropriate localization and track denominators, or use a certificate directly in the original point-symbol presentation.

This is not a correction to the analytic Fourier identity. It distinguishes field-linear equivalence from integral lattice equivalence. The determinant-one raw-row certificates in the new report address the latter issue directly.

## 4. Update the research-status paragraph without overextending the result

**File:** `Analysis/Polylogarithms/docs/manuscript/chapters/10-discovery.tex`  
**Location:** “Certificates, integral structure and arithmetic evaluation,” source lines 148–157.

The question about integral Smith forms and torsion can now be narrowed:

> For the complete weighted prime-distribution presentation, an explicit original-symbol unit minor gives an integral polynomial basis and arbitrary-ring base change. All nonzero unreflected Smith factors are one. The integral reflection quotients have explicitly determined scalar Smith torsion, and arbitrary one-variable integral jets have the minimum-valuation formula of the integral continuation. More general coefficient rings reduce to binary Koszul homology. These formal results do not determine the kernel of numerical period evaluation, and do not replace higher-depth functional-equation questions.

The original Gaussian `S_6` conjecture should retain its existing status. The new report supplies neither a proof of it nor a period-independence theorem. Existing proofs of `S_4` and the characteristic-zero rank formulas should retain their historical attribution.
