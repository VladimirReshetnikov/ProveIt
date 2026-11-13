# Independent review: conditional coarse no-same-data lift

The [reviewed packet](../../research/ordinary9-two-norm-coarse-no-same-data-lift/README.md) correctly maps the coarse two-norm witness and any hypothetical same-nine-input parent completion to the displayed `P72Exact.indices_ordinary` hypotheses. Subject to **standard-natural soundness of that retained theorem and its transitive source lemmas**, and to the pinned coarse-witness argument, the conclusion m=R contradicts the witness's m≠R. I found no missing premise or signed-to-absdiff mismatch. This remains conditional source-level reasoning, not a Lean-checked theorem, a fixed-compact result or a refutation of a parent zero with different coordinates.

The witness uses the noncompact ports `(127,87,54,139)`, q=128, `n=9,437,340`, `m=9,439,512`, `R=18,874,679=2n−1` and `mu=q⁴=268,435,456`. Its coarse construction has positive X, positive s and eta, `Y=q³s`, `c=eta+Yk`, `a=XY+Y`, first and main Pell pairs at those same n and m, and `k=2n+4(XY²)sFirst`. It has 0<eta<k; taking the shifted-parent input `n_zeta=(k−eta)−1` is therefore natural and gives `k=eta+n_zeta+1`. The nine projected F/main coordinates are unchanged by the hypothetical choice of the four auxiliary inputs.

The exact theorem-parameter mapping is `q,X,Y,k,R,g,c,a,s,i',f,T,u,n,sFirst,mu,m,eta`, with g the main Pell first coordinate and i'=n_i+1. Its premises are supplied as follows:

- q≥3, X>0, s>0, `Y=q*(q*q)*s`, eta>0, `c=eta+Yk`, and `a=XY+Y` come from the coarse witness.
- i'>0 follows from the parent's shift; f>0 follows from the strong unit equation and I=i'c²>0.
- R≥26, `R+1<mu`, `(2n)%mu=R+1`, the first ordinate at n, `k=2n+4(XY²)sFirst`, and the main ordinate at m are the stated coarse facts. The main Pell x-coordinate g supplies `g²=1+delta(a)c²`.
- The strong factor +1 gives `I²=Delta(f²−1)`, equivalently the theorem's `I²+Delta=Delta*f²`. The auxiliary factor +1 supplies its remaining norm equation after the absdiff conversion below.

At a hypothetical parent output zero all four integer factors are units. Independent modulo-four checks exclude −1 for the first, main and strong factors; the remaining auxiliary factor must also be +1. Since c>1 and i'≥1, I>1. The auxiliary norm rules out y=0 and gives `y²−1=I²(y²−V²)≥0`, so `y≥|V|`. With natural `u=y−V`, where `V=f²(Tc−R)−c`, set natural `A=f²Tc`, `B=f²R+c`. Then `A−B=V`, `absdiff(A,B)=|V|`, and `absdiff(A+u,B)=y`; these are exactly the two absdiff terms in the theorem. This remains valid for either sign of V, with T and R natural as required.

The theorem source concludes m=R, while the pinned values have m<R. The result excludes only a parent completion preserving those nine specific values; a parent zero with different values, the actual fixed compact tuple, and an existential witness-changing bridge remain open. No Lean process, provider/axiom replay, or formal PDF semantics was used.

The receipt reproduces the author and two independent predecessor checkers, checks the theorem's complete named hypothesis list and parameter order, and exercises 1,344 unit-sign residues plus independent signed-to-absdiff controls. It does not prove the retained theorem or the enormous witness in Lean. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary9-two-norm-coarse-no-same-data-lift-independent/check.py | cmp - reviews/ordinary9-two-norm-coarse-no-same-data-lift-independent/receipt.json
```
