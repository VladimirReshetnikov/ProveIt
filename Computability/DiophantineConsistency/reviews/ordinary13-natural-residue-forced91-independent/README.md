# Independent review: compact-port AQ13 mixed natural graph

This is an external review of the 13-natural-input, 91-operation candidate and its four forced-positive input arguments. Run `python3 -I -S -B check.py` from any directory and compare with `result.json`; the author's checker and receipt also reproduce. No Lean build, staging, provider authentication or internal iPRA endpoint was performed.

The child graph is exactly the 82-row positive parent with nine inputs shifted and `J`, `X`, `f`, `y` left natural; all 91 child rows, inputs and ports are live. The checker pins the exact graph wiring of the four square residuals and each formula used below. The mixed-shift polynomial identity is pointwise for arbitrary integer ports. The zero-existence equivalence additionally requires the first two ports beta and K0 represented by nonnegative model naturals; the other two ports may be arbitrary signed values locally.

In an ordered IΣ₁ model, the nine shifted inputs are positive. Thus `q=1+J*beta≥1`, `Y=q³*s>0`, `c=eta+Y*(eta+zeta)≥3`, `I=i*c²≥2`, and `Delta=(Y*(X+1))²+3+4*Y*(X+1)>0`. The four arguments below are simultaneous and require no other unshifted input to be positive:

- If `J=0`, the first residual forces `Z²=0`, while `Bt=(1−F−alpha)*(X+K0)−F<0` and `Z=−Bt>0`.
- If `f=0`, then `Q=−Delta<0`, contradicting the strong residual `Q=I²>0`.
- If `y=0`, strong and auxiliary residuals give `Q*V²=1` and `Q≥4`. Here V may be signed. If V is nonzero, its absolute value is a positive represented model natural, so `V²≥1`; the product is then at least four. If V is zero, the product is zero.
- If `X=0`, put `a=Y`, `H=4Y+3`, and `U=Y*q²>0`. The signed main norm and the model square-divisibility theorem yield `Dstar=U*d` for a signed model-ring d. The main expression gives `H∣U*(d−a*c)`, while the norm gives `R=d²−1−(a²+H)c²=0`. The checker independently verifies the free-ring identity `U=H*(shift*(d+a*c)−U*c²)−U*R+(U*(d−a*c)−H*shift)*(d+a*c)`, so `H∣U`. Since `4U=(H−3)q²`, also `H∣3q²`. But `Y=q³*s≥q³` and `q≥1`, so `H=4Y+3>3q²>0`, impossible for model-natural divisibility.

Signed magnitude is available through the pinned nonnegative-cone source, and `Trace75IntegralTransport.natural_dvd_of_signed` is an existing general source interface for reflecting signed divisibility to model naturals. The graph-specific proof, its magnitude and cancellation steps, and its provider imports have not been elaborated. Once the four inputs are forced positive, predecessors for the nine shifted coordinates give zero maps in both directions under the represented-port assumptions.

For degree, independent free-ring expansion verifies the A1 cancellation and an upper bound of 56. Matching compact P72/P115 port hashes were authenticated and an independent all-inputs-equal ray modulo **1,000,000,009** has degree 56 and leading coefficient 495452850. This is exact for the authenticated compact tuple, not a claim for arbitrary ports.

The parent 13/82 construction has an external standard-integer calibration review; this local all-model reasoning does not upgrade that calibration to an arbitrary-model theorem. The residue and q³-quotient paths, their compact tuple, the current-2011 PDF tuple, and their inherited endpoint/provenance questions remain distinct. No new Lean theorem, internal iPRA proof, PDF binding or global minimality is established.
