# Audit of the 225-variable parent and its logical calibration

Prepared 25 October 2026 as an independent task within the AI-assisted research session. This is a mathematical and artifact audit, not external human peer review.

## Conclusion and exact scope

The parent polynomial is the literal `equation/equation.json` in **ConZFC_Pooled_Powers_2026-10-25.zip**, with SHA-256

`fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56`.

It is a sum of 162 quadratic residual squares in 225 unrestricted integer variables. Its complete collected expansion has degree four, 7,867 monomials and coefficient height 128,446. The inspected ordinary mathematical argument identifies existence of an integer zero with refutability in the square-shell numerical calculus C222; constructor recoding identifies this with the original C222. Two named inherited theorems then identify C222 refutability with ZF and ZFC refutability.

I found no mathematical defect in the new pooled-power lemma, its signed/unit-base recovery order, the strict-horizon change, the linear beta-base construction, or the inherited rounded-factorial bootstrap as used by this parent. The source equations and all 20 generated stage JSON files were rebuilt and independently checked in both ordinary and optimized Python. The immediate 245-variable parent also passed a fresh rebuild and independent audit.

The review does not replace the entire historical arithmetic development or the Lean import closure with a new proof. The supplied ordinary proofs remain the mathematical dependencies. No new Lean/Rocq build or encoded object-language ZFC derivation was produced in this audit.

## 1. Authenticated source recovery

The comparison tree is ProveIt commit `953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`. Source 158 was placed by `2a18823cc165de50e7a10675a8f0c74c384aa94a` from arrival `536c08e7913e59bd42e8fca66e89944c920884ad`.

The placed tree intentionally omits byte-identical inherited copies, following the repository's placement procedure. Their absence is not an absence from the original release. To obtain an independently runnable closure, the original archive was downloaded from its pinned public GitHub path and authenticated by its Git blob identifier:

- Git blob: `32234a5b596a62e6a19fa136175a9024cb3eed9b`.
- Archive size: 1,278,389 bytes.
- Archive SHA-256: `0e0efbc168fcaac562042778ffcd5bf40f6f74a711ee33915c0ea0750aa10c55`.

The separate Joint Norm and Shared Residue Bounds source archives were also authenticated against the SHA-256 identities in the parent source ledger. Their archived copies restored all ten specifically listed retained proof files, each matching its recorded SHA-256, and the four square-shell supplement files. The original 225-variable archive already includes this restored closure and is the preferred portable source dependency.

The inherited 145-package calibration audit and its fourteen selected Lean files were extracted separately from the authenticated Shared Residue Bounds archive. These are useful for assessing ordinary formalizability inside ZFC; they are not a complete Lean project.

## 2. Fresh finite replays

The scripts were inspected before execution. The main verifier performs exact integer sparse-polynomial arithmetic and optional reconstruction through the included local construction scripts. Its checks do not rely on Python `assert`, and remain active under `-O`.

Fresh commands run from the unmodified original parent archive were:

```text
python3 -B verify.py --rebuild --receipt POOLED225_FRESH_REPLAY.json
python3 -O -B verify.py --rebuild --receipt POOLED225_FRESH_OPTIMIZED_REPLAY.json
python3 -B inherited/joint_norm245/code/verify.py --rebuild --receipt JOINT245_FRESH_REPLAY.json
python3 -B code/check_all_frame_atoms.py equation/equation.json
```

Both 225-variable replays passed with:

- six exact stage equations, culminating in the pinned 225-variable equation;
- all 20 generated JSON files reproduced byte for byte;
- 175 forward and 178 reverse private-wire polynomial identities;
- fourteen invertible Pell-coordinate changes;
- the exact 36-atom square frame and the two power groups of sizes eleven and three;
- complete quartic expansions at every stage and all declared coordinates occurring.

The separate actual-final-equation frame audit checked all seventeen retained power requests, not only the fourteen pooled ones. It verified that each actual base, index and output is an affine atom whose square is strictly below W.

The 245-variable immediate-parent replay passed the source reconstruction, eighteen Horn factorizations, 202 integral monic projections, integer translation, complete quartic collection, all 88 pinned inherited files, six corrupted-artifact controls, and reproduction of sixteen generated JSON files. These are fresh checks; older receipts included inside the archive remain historical receipts.

## 3. The pooled-power argument

For one nonzero base n, let the already oriented Pell pairs be `(X_i,Y_i)` at signed index k_i and center A, with materialized `Z_i=A Y_i`. Set

```text
T = 2 A n - n^2 - 1,
H = sum Y_i (m_i-X_i),
S = sum ((m_i-X_i+Z_i)^2-Y_i^2).
```

The two new quadratic rows are

```text
K - 2H - (2A-n)L = 0,
S - nK + L = 0.
```

They imply `S-2nH=TL`. Using only the existing multiplication rows `Z_i=A Y_i`, the identity

```text
sum (m_i-X_i+(A-n)Y_i)^2 = S-2nH-T sum Y_i^2
```

shows that T divides a sum of squared power-congruence errors. The final frame is stronger than the coarse bound `|atom|<W`: it gives `W=2+sum atom^2`, with `W>=258`, and the unchanged Pell frame gives `|A|>W^W`.

Put `b=floor(sqrt(W-1))`. Each actual `|n|,|m_i|,|k_i|` is at most b. Multiplying the Pell congruences by `n^b` clears negative indices, because `gcd(n,T)=1`. Therefore T divides the nonnegative integer

```text
E = sum (m_i n^b - n^(b+k_i))^2.
```

For at most fifteen requests,

```text
0 <= E <= 4r b^(4b) < W^(2b+1) <= W^W < |T|.
```

The strict inequalities follow from `4r<=60<W`, `b^2<W`, `2b+1<=W`, and `|T|>=2|A|-W>W^W`. Thus E=0. At a nonunit base all indices are nonnegative and every output is the true integer power. At the unit bases the appropriate signed-index unit outputs are recovered, without incorrectly asserting an index sign. The converse chooses integral K,L from the true congruences.

This reasoning is valid for either sign of A and n. The square-root bound and variable powers occur only in the proof; the literal equation has only fixed integer coefficients and quadratic residuals.

## 4. Recovery order and cofinal completeness

The initial three singleton power requests are retained. The normalized factorial error first gives `M!=0`, `B!=0` and `|FB-V|<|B|/2`, where the retained numerator request gives `V=(F^2+1)^t`. Elementary inequalities then yield `|B|>=2`, `|F|<|B|`, and `V<|B|^2`. The odd multiplier `H=1+2 sum a_i` is nonzero before any representative sign is known.

The singleton requests at B and BH give `x>=0` and `q=(BH)^x`. The q-group may be used at q=1: if x=0, its exact unit output gives M=1, contradicting B dividing M and `|B|>=2`. Hence x is positive and q is nonunit. Its retained denominator ratio yields `x>=t`, so `|q|>=2^t`. Only now is the q+1 group used to recover nonnegative representatives. This avoids a circular appeal to their signs.

The factorial digit is recovered in a signed radix by the half-width normalized remainder bound. The `F=0` case is treated separately, because the usual binomial coefficient bound is false there. The recovered binomial output and the elementary nearest-integer factorial lemma then force `F=t!`. For this parent only t>=16 is required; no unreviewed stronger small-t claim is needed.

The strict local ranges are obtained by choosing the existential horizon `t=16+z^2` larger than every local schema parameter, derived label and actual proof length before constructing any numerical witness. The derived label on global CRT representatives is not required to be below t. Tightened binomial lower indices eliminate a redundant t+1 request.

The new beta base is `y=V-1`. For a finite proof tree padded to t rows, every pending multiset has at most t factors and every factor `1+jF` is strictly below `F^2+1`. Hence every actual state is less than V. Moreover F divides y, so the t+1 beta moduli are pairwise coprime. This supplies cofinal completeness without claiming that arbitrary old witness tuples survive unchanged.

## 5. Square-shell syntax versus the older Cantor syntax

The literal arithmetic circuit uses

```text
I(x,y)=2((x+y)^2+x),        M(x,y)=I(x,y)+1,
A(x,y)=2((x+y)^2+3x+4y+3), E(x,y)=A(x,y)+1.
```

It must not be read using the older Cantor polynomial printed in the inherited `calculus.tex`. The supplied `SHELL_ENCODING_PROOF.md` proves that the four constructors partition the natural numbers, have descending arguments away from the distinguished zero, and admit mutually inverse recursive constructor-preserving translations between the two coding schemes. The translations fix truth 0 and falsity 1.

The guarded bundle's numerical disequality witness is reconstructed after recoding as `abs((f(c)-f(a))*(f(c)-f(b)))-1`. It is not transported by an invalid claim that f preserves addition or multiplication. Every finite numerical derivation therefore transports in both directions. This particular recoding is a finite recursive syntactic construction and is provable in ZFC.

## 6. Why the full calibration is provable in ZFC

The exact inherited interfaces are:

```text
KEndpoint.c222_iff_zf_refutation :
  KCode222.C222 Code254.F <-> BProv ZFax_s [] Form.fBot

ConstructibleChoice.zf_refutation_iff_zfc_refutation :
  BProv ZFax_s [] Form.fBot <-> BProv ZFCax_s [] Form.fBot
```

These are unconditional equivalences in the inspected sources. Their hypotheses do not assume Con(ZFC), an omega-standard model or a transitive set model of ZF.

The mathematical proof of the lower C222 direction uses first-order completeness for a definable set of named formulas, the full seed property, a tagged model and quotient, and a first-order definable internally well-founded part. The definition `InternallyWellFounded mem t` quantifies over represented sets s in the structure's domain. It does not require external well-foundedness of the membership relation. The associated formulas and their satisfaction equivalences are present in `WellFoundedPartCore.lean`, with uniform relativization in `WFRelativization.lean` and the ZF schema verification in `WFModelCore.lean`.

The upper C222 direction and the ZF-to-ZFC Choice transport use the constructible submodel of an arbitrary set model of ZF, followed by soundness and completeness. Satisfaction for a set structure and recursive formula translations are definable in ZFC. The theory used by completeness is a set of finite formula codes. Quotient formation, the indicated definable substructure, and the internal constructible-model construction are all ordinary ZFC constructions.

Consequently the ordinary proof is suitable for the statement that ZFC proves the insolubility equivalence. This is stronger than a claim only about externally standard integers, but it is not a claim that an encoded object-ZFC derivation has been generated.

One wording correction is essential: the *whole* calibration should not be described as merely a primitive-recursive transformation of finite refutations. Its supplied proof explicitly uses semantic completeness and model constructions. A primitive-recursive proof translator would be an additional implementation result. The finite recoding and arithmetic transformations do not by themselves establish such a translator for the semantic calibration.

## 7. Recommended use in the new report

Prove the new integer zero-set equivalence to this exact 225-variable parent by explicit integral maps and exact algebra. Then state the consistency corollary by composition with the ordinary parent arithmetic proof, the square-shell recoding, and the two named logical calibration theorems. Cite the parent archive and source identities. Distinguish the freshly replayed finite identities from the inherited, un-recompiled Lean development.

The resulting claim does not require a new assumption about consistency. It gives an equation whose unsolvability is ZFC-provably equivalent to Con(ZFC); it does not establish either side separately. The source review supplies no basis for a worldwide priority or global simplicity claim.
