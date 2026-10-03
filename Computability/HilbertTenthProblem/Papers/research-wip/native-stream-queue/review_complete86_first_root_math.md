# Independent positive-zero challenge of the complete first-root reduction

**PASS.** The new coordinate is sound for the entire positive integer zero set of the existing complete asymmetric parent, with no additional Pell/sign lemma or source restriction. The normalized polynomial has **86=48M+38A**, nineteen positive witnesses and exact degree179; the ordinary-strong variant has87=47M+40A and exact degree135. This review focuses on the positive-domain proof and the actual source identity; the separate [complete-source audit](review_complete86_first_root_source.md) independently checks the full degree expansions and circuit.

The reviewed author source is `complete86_factored_first_root.py`, SHA-256 `29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f`; its receipt is `2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e`. The accompanying checker reads but does not execute that module. It separately authenticates the asymmetric parent source and receipt and reconstructs both complete child source lists from those literal parents.

## The decisive argument

The actual parent defines

    q=(B−1)J+1,  X=wq,  Y=sq³,
    k=eta+zeta,  L=XY²k=w*s²*q^7*k.

The actual source registers are `R10b=k` and `first_root_base=L`. On every supplied positive tuple, before any polynomial equation, q≥B≥16, w,s≥1 and k≥2. In particular L is a positive integer and Lk>1. This argument uses only the unchanged admissible fixed compiler radix and coordinate domain, not a conclusion about the exponent, masks, Pell ranks or unit signs.

The first factor changes from

    Nold(g)=g²+L(2g−k)

to

    Nnew(T)=T²−L(L+k).

The first-gap coordinate g is private: its only old direct consumers are its square and doubling. L and the other seven factors have no dependence on g. Therefore the triangular substitutions

    T=L+g,       g=T−L

are mutually inverse integer polynomial coordinate maps, keeping all eighteen other witness coordinates and the ordinary input unchanged. Exact expansion gives `Nnew(L+g)=Nold(g)` and `Nold(T−L)=Nnew(T)`. Consequently the complete eight-factor product-minus-one polynomials agree under the same substitutions on every integer, rational or real assignment. They are not equal at the same supplied coordinate tuple.

Now suppose a complete new **integer** tuple is a zero. Its eight integer factors multiply to1, so each factor is+1 or−1. In particular

    T²−L²=Lk+epsilon,   epsilon∈{−1,1}.

Since Lk>1, the right side is strictly positive. The supplied T is positive and L is positive, so T>L and the restored integer g=T−L is strictly positive. Every other coordinate is retained positive. The full polynomial identity thus produces a complete positive parent zero. The entire established parent compiler theorem, including all ordinary-input, strong-rank, ratio, sign and mask conditions, can now be applied without circularity.

Conversely, every complete positive parent zero has positive T=L+g, and the full identity produces a complete new zero. These maps are inverse on the **full supplied positive zero sets**, not merely on accepted input projections or canonical native witnesses. The forward map even preserves the whole positive orthant, but the inverse need not: the receipt includes a complete positive off-zero assignment with restored g=−536870911. No positive-orthant bijection is asserted.

There is no hidden arithmetic instruction computing T=L+g inside the new polynomial: T replaces the old quantified coordinate. Both directions are proof maps between coordinate systems. The L computation is retained and charged in both literal schedules.

## Paid source and degree

Including L, the old first factor takes six gates: three multiplications and three additions/subtractions. The new factor takes five: L, T², L+k, L(L+k), and the final subtraction, with three multiplications and two additions/subtractions. Thus the saving is one addition. Every other literal source row, every factor and the entire product-minus-one finalizer remain paid. The checker reconstructs the complete expected source, checks the private root consumers, and compares all eight factor DAGs plus the output after the independently proved first-factor cut: eighteen full expression identities across the two modes.

L has exact degree11 and leading form

    Ltop=w*s²*((B−1)J)^7*(eta+zeta).

The new factor's highest form is `−Ltop²`, degree22. Its supplied T² has degree2 and Lk degree12, so cancellation at degree22 is impossible. All other factor degrees/leading forms are unchanged from the authenticated parent. They give

    normalized:22,18,32,56,7,3,34,7, summing179;
    ordinary:22,18,32,24,7,3,22,7, summing135.

Their product has the sum of those exact degrees because the coefficient polynomial ring is an integral domain and each displayed leading form is nonzero on every admissible fixed compiler slice. In particular B−1 is nonzero and the inherited transport leading form includes the nonzero ordinary-input coefficient−2d. This review establishes the new factor's degree directly and uses the existing proof of the seven unchanged factors; it does not present a finite numerical degree specialization as the uniform degree theorem.

## Hypothesis challenges and bounded evidence

The local conditions are essential. If L=k=T=1, then Nnew=−1 but the inverse gives g=0: the strict Lk>1 margin cannot simply be dropped. If the new root may be signed, L=3,k=2,T=−4 gives Nnew=1 and g=−7. Both are scalar boundary examples outside the actual source domain, not full compiler counterexamples. Over rationals or reals a product equal to1 need not have individual unit factors, so the full natural/positive zero proof cannot be inferred from the polynomial identity alone on those domains.

The checker independently proves both local identities and the entire abstract product-minus-one identity by exact sparse coefficients. It reads and reconstructs both full literal schedules, the exact L producers and both paid ledgers. A bounded local unit census tests65024 radicals across 1≤L≤256, 2≤k≤128 and both signs; every integral positive root restores positive g. Both unit signs occur in that general census. These are local arithmetic checks, not materialized full universal Pell zeros or substitutes for the general inequality proof.

Reproduce with the standard library:

    python review_complete86_first_root_math.py \
      --source complete86_factored_first_root.py \
      --receipt complete86_factored_first_root.json \
      --root /path/to/native-stream-queue \
      --expect review_complete86_first_root_math.json

No historical module is imported, no parent source is changed, and no unrelated author suite is rerun. The only newly generalized theorem is the proved private-coordinate change; all universal program/input hypotheses are exactly those of the selected complete parent. No unrestricted optimality or proof-assistant verification is claimed.

Final companion proofread: the complete author note with SHA-256 `9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b` was read after source freeze. Its `tau_root` interface, unconditional positivity-before-Pell order, fixed-program universality statement, exact179/135 degrees and separate75-comparison limitation agree with this review. No correction was requested. The author Python/JSON pins and this review's executable receipt remain unchanged.
