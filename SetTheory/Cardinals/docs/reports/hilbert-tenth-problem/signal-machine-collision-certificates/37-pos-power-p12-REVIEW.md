# Separate mathematical and static-execution review

4 October 2026. This review records a separate proof-only domain check and the author's exact static verification. It is not external peer review, a proof-assistant certification, or a rerun of upstream code.

## Separate domain and ledger check

The review checked the 12-leaf candidate against the frozen 22-leaf proof and its 13-leaf elimination variant. It confirmed:

1. Six direct positive leaves and six natural adapters give twelve leaves, including the output
2. H_5 recovers positive integral alpha=A/d with alpha>w>=b
3. H_2 recovers integral u=U/(d q_alpha), with |u|>=alpha
4. beta=alpha+q_alpha u and q_alpha>=1 rule out negative u; its Pell norm rules out zero
5. Every restored x,s,v,t and parameter adapter meets the original positive domain
6. The reconstruction is bijective precisely onto the old strict-q_alpha subset
7. The progression q_alpha,k=q_alpha,0+4yk with k>=1 proves completeness, including exponent zero
8. The retained q_b,k=q_b,0+uk gives infinite full fibers
9. The corrected lean H_1=X^2-d^2-(A^2-d^2)y^2 has scaling H_1=d^2R_1; it does not carry an extra q_alpha^2 factor
10. The exact residual degrees are 4,10,10,1,6 at fixed base and 8,12,12,1,8 at variable base, with SOS degree 20 and 24
11. The native-gap/bounded composition has 29 positive witnesses and 18 residual slots, excluding its three external inputs

The review's initial degree list was for a candidate with the redundant q_alpha^2 factor on H_1. A subsequent explicit correction confirmed the lean formula and the degree lists above; the earlier list is superseded. No other mathematical correction was required.

The review ran no scripts or mathematical execution tools. The final proof also notes that alpha's integer-square argument was redundant in the 13-leaf predecessor, where retained u and its congruence already implied alpha=beta-u q_alpha, but that shortcut is absent after u is eliminated here.

## Static checker inspection and observed results

`static_algebra.py` was newly written for this packet and then read in full before its only execution. Its imports are restricted to pathlib, fractions, math, hashlib and json. It makes no network or subprocess calls and imports no code from any existing packet. It only writes within this new directory; the original directory is read for byte comparisons and hashing.

It performs sparse integer polynomial addition, multiplication, expansion and evaluation; exact Fraction reconstruction; finite Pell recurrence arithmetic for the declared fixture list (b,C)=(2,1),(3,1),(4,1),(5,1),(2,2); and finite interpolation from hand-declared acceptance sets. This is static algebra and fixture evaluation, not execution of a counter program or physical dynamics.

The observed successful receipt records:

- Five expanded module instances: b=2,3,4,5 and b=B+1; all declared variables live
- Five exact generic polynomial identities comparing the new formula to the old 13-leaf residuals
- Twenty complete positive fixture assignments, each evaluated in both fixed-base and variable-base forms, with all fifteen reconstructed old residuals zero
- Five exact polynomial identities for the entire b=2,C=1 family in its free parameter k
- Six complete composed expansions from literal acceptance sets at T=0,1,3, all with 29 witnesses, 32 total variables, and 18 residual slots
- Composed degrees 20 at T=0,1 and 60 for the two selected T=3 tables, matching max(20,compiler degree)
- Full original-directory before/after inventories equal byte for byte

The expanded base-two polynomial has 12,858 nonzero monomials; the positive-variable-base polynomial has 61,641. Both exact coefficient-one degree certificates are verified after every adapter shift. Detailed receipts and all serialized evidence are hashed in the manifest.

These finite checks supplement the proof. They do not independently establish all-exponent exponentiation or the all-input theorem, which rests on the displayed reconstruction, progression, composition proof, and explicitly pinned constructive Pell dependency.
