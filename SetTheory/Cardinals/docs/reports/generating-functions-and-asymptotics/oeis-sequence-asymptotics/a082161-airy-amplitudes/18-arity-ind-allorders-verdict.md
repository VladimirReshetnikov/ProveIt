# Independent verdict: relaxed fixed-k all-finite-orders expansion

Date: 2026-10-02.

**Approved for every fixed integer k≥3 and every fixed finite expansion order.** The exact relaxed-tree sequence initialized by d_(0,0)=1 has the displayed Poincaré expansion in powers of n^−1/3, with one common strictly positive leading amplitude C_k and remainder O_(k,M)(n^−(M+1)/3) after M terms. No logarithmic powers are needed.

Reviewed proof: `all-orders-proof.md`, SHA-256 `7a67a0230c49f4d463fd24c31c94ca04aee32b3a8d1f9382917a6c460804dee0`.

Detailed audit: `independent-all-orders-audit/analytic-audit.md`, SHA-256 `48fda38a24b91965f070f36083ec09ac07124b7a5fad38a82fe6a261fbcbce52`.

The approval uses the precisely scoped leading analytic theorem already audited for the unchanged `fixed-arity-proof.md`, SHA-256 `9be0c0aaf02b6918a8015c6d059664851d393e9ea8e75ac4a31e082c34434ee2`. Positivity inherits that theorem's use of the published lower Theta bound for this exact recurrence and initialization.

The polynomial–Airy recursion and exact bottom condition work to every finite order. Finite Taylor matching gives an arbitrarily small norm defect. The inherited stable gap and central zero-limit bootstrap transfer this defect to the exact solution with the explicitly accounted endpoint loss. Normalizing every scalar ansatz to leading coefficient one keeps C_k unchanged at every order.

Both explicit corrections were independently reproduced symbolically in q=k−1, with B=(2/q)^(1/3), λ=a_1/B:

c_(k,1)=k^−1/3 λ²(3q²+27q+23)/(45q),

c_(k,2)=k^−2/3[h_1²/2+λ(4q³+321q²+429q+126)/(270q)],
h_1=λ²(3q²+27q+23)/(45q).

The independent exact-rational script uses direct undetermined-coefficient systems and checks both recurrence components through ε⁵. It imports no producer code. Its source and output hashes are recorded in the detailed audit.

No uniform-in-k result, convergence of the infinite formal series, numerical amplitude evaluation, compacted-tree result, signed-delay theorem, or DFA amplitude/ratio is included in this approval. The q=1 algebraic specialization is not an audited extension of the analytic theorem to k=2.
