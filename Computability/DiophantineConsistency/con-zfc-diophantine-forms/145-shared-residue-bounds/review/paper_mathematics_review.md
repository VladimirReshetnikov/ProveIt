# Mathematical review of the research-paper draft

Reviewed: `output/ConZFC_Shared_Residue_Bounds_2026-10-25/report/paper.tex`,
25 October 2026, before final typesetting. This review covers mathematical
content, not PDF layout or the separate 76-shear coefficient audit.

## Result

No material mathematical inaccuracy was found in the reviewed draft.
The new residue-pool argument remains consistent with the earlier approved
source proof and exact artifact review. The two requested additions are
mathematically sound, with the clarifications below recommended.

## Added factorial fixed-point proof

The forward argument is correct. The retained rows with r,s>=0 are
precisely F-1<V/B<=F. With G=t! and

    V/B=G product_{i=1}^t (F^2+1)/(F^2+i),

the upper bound by G and integrality give F<=G. Monotonicity in F^2,
evaluation at F=1 and the elementary t>=16 estimate give F>t^2.
The product lower bound then yields

    V/B>G(1-1/(2F)),

and therefore G<2F^2/(2F-1)<=F+1, giving G<=F. There is no use of
F=t! in the preceding binomial-remainder bootstrap.

Recommended small explicit clarification in the converse: at F=G=t!,
state independently that t!>=2^(t-1)>t^2 for t>=16 before invoking
"the same product estimate." The estimate then gives
G-1/2<V/B<=G, and the stated integer r,s are nonnegative and correct.
This is a short omitted justification, not a substantive gap.

The coefficient lemma's alternate F=1 proof via Pascal's identity is
also valid: each coefficient on row t+1 is the sum of two distinct
adjacent row-t coefficients, bounded by that row's full sum 2^t.
Boundary coefficients are separately harmless.

## Internalization and well-foundedness language

I read the actual retained sources under `analysis/calibration_review_sources`:
`WellFoundedPartCore.lean`, `WFRelativization.lean`, `WFModelCore.lean`,
`KEndpoint.lean`, and `ConstructibleChoice.lean`.

The draft's distinction between internal and external well-foundedness
matches the definitions. `InternallyWellFounded` quantifies over represented
sets s with Sub mem s t, not arbitrary external subsets. `WF` is defined
by an explicit first-order formula. `WFRelativization.translate` is a
recursive formula translation whose quantifier guards are evaluated in the
ambient structure. `WFModelCore` explicitly handles translated Separation
and Replacement matrices. The draft therefore correctly avoids a
transitive-model assumption or the false assertion that every relevant
model has the external standard natural numbers.

The paper appropriately treats the full logical calibration as an imported
mathematical dependency and says that its full formal dependency closure
was not rebuilt here. This review supports the displayed definitions and
interfaces; it does not independently reprove every imported logical module.
The ordinary ZFC-provability claim is a composition with that identified,
uniformly internalizable calibration, not a claim that finite coefficient
checks prove consistency.

## Square-shell versus Cantor constructors

I read `certificate/inherited_proofs/SHELL_ENCODING_PROOF.md` in the
staged source packet and checked it against `shell_source.py`. The actual
low-height xx0 source uses

    I(x,y)=2((x+y)^2+x),       M=I+1,
    A(x,y)=2((x+y)^2+3x+4y+3), E=A+1.

The four images partition the nonnegative integers. The shell decoder
is correct, and arguments decrease strictly for every positive code.
The sole cycle I(0,0)=0 is explicitly handled by the fixed zero leaf.
Course-of-values recoding to the old Cantor constructors has an inverse,
fixes 0 and 1, and preserves constructor terms and disequality. It therefore
transports finite derivations in both directions. The nonzero-product
witness d is reconstructed after recoding rather than transformed through
the false identity f(d+1)=f(d)+1. The retained proof explicitly addresses
this issue.

The draft correctly declines to identify the two numerical presentations.
For greater self-containment, I recommended printing the four formulas above
and a short paragraph stating the constructor-preserving recoding theorem,
with its fixed 0/1 endpoints and freshly reconstructed guard witness.
This makes the bridge between the literal source and the imported Cantor
C222 endpoint explicit rather than leaving it only in the retained files.

## Scope

No PDF visual checks were performed in this review. The new shear sequence
and final height/support figures are being independently checked elsewhere.
The earlier review covers the unchanged 260/261-variable source reductions,
while this note covers the paper's mathematical exposition and added lemmas.
