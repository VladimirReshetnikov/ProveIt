# Independent source review of the coupled Pell construction

The reviewed [construction note](../../research/trace74-symbolic-coupled-pell-strategy/README.md)
has SHA-256 `adc16c02c4a861819bb76ab00bf42b139aafcf5802d5b093b8fc243f86fdbdca`;
its finite diagnostic has SHA-256
`e2768fb4109ad83700096b1b60130336c632cf48c2afe9bcd65f95df7bedc314`.
The carrier precursor note and checker have SHA-256
`ab3f8afaeb76e3062bf2e41a2fe5119c76b637018173cc37240e9b74463200db` and
`781c98e89187dfbb1b6f4a440161007367d17289b784a4691d1ada4c7d65be31`.

I checked the ordinary-integer construction as a mathematical argument,
including the exact tuple and signs, and found no missing algebraic step.
Conditional on the numerical gcd results from the recorded external
computations, it gives positive integer witnesses for the retained
74-row graph at the stated external beta and K0, for arbitrary natural
MC and MF, with `F+C≥q`. This is a source-level mathematical review,
not a Lean proof or a materialized full witness. The enormous numbers
and the two gcd computations are not kernel checked here.

Key checks:

* The sibling Pell interval provides positive `eta,zeta` with
  `eta+zeta=k` and `c=kY+eta`. The independent
  [payload check](../trace74-symbolic-fixed-payload-independent/README.md)
  verifies that the candidate's beta is `2^590069−1` and K0 is the
  hash-pinned external value used in the carrier CRT. In particular,
  the shared graph input is `w=X/q`, not an independently chosen 1.
* With `D=XY` a power of two, c odd, and the external checks giving
  `gcd(c,q²−1)=gcd(K0+w,q−1)=1`, the CRT moduli `D,c,q−1` are pairwise
  coprime. The three CRT equations can therefore impose `D|e`,
  `R≡−r (mod c)`, and `(q−1)|Breg` simultaneously. A sufficiently
  negative period shift ensures `G<0`, `R<0`, `C>0`; the fixed `w>1`
  then gives `Breg>0`.
* The recurrence identity `x_j−a y_j ≡ 2^j (mod 4a+3)`, the main Pell
  norm and `X=2^r` give `H|Kreg`. Along with the two CRT divisibilities,
  this makes the note's `N0` an integer.
* The main Pell unit matrix is invertible modulo `m=c²tau`; its orbit
  period is at most `m²` and divides `(m²)!`. The note's choice of `t`
  therefore makes `c|t` and `c²tau|y_t`, yielding positive `i`,
  `phi²=1+a`, `f=x_(2t)`, and `Q=(Delta*y_(2t))²`. It also gives
  `f≡1 (mod c)`, hence `gcd(f,c)=1`.
* For the proposed odd auxiliary index, the Chebyshev quotient identity
  follows from its two-step recurrence and `S²+z²≡1 (mod f)`. Pell
  composition modulo `f=x_(2t)` gives the required sign `−c`, while
  `c|t` and `r≡1 (mod 4)` give residue `r` modulo c. Together with
  `R≡−r (mod c)`, these make the proposed `T` integral. The separate
  [abstract orbit toy](../../research/trace74-coupled-orbit-toy/README.md)
  independently verifies this congruence pattern in a finite example.
* Substituting the proposed `v7` into the actual carrier register gives
  `Z=M tau phi yaux`. The chosen odd auxiliary Pell pair satisfies
  `Q V²−(Q−1)yaux²=1`, so the output identity
  `(Q−1)Z²−M²(E F0)(Q V²−1)=0` follows. The explicit bound on `s`
  makes both `T` and `v7` positive; the remaining eight coordinate
  positivities were checked against the same tuple.

I read the register and output definitions in
[`TenPositiveTrace75.lean`](../../Lean/DiophantineConsistency/TenPositiveTrace75.lean)
and checked the all-ring substitution `alpha=q−F−C`, which gives the
new positive `C` and new rank factor without assuming positive alpha.
I reran the restricted-fragment
[`check_lean_graph.py`](../../research/trace75-bfs-decimal-display/check_lean_graph.py)
and the [74-row coordinate check](../../research/trace74-mask-coordinate-probe/check.py);
both exited 0. These externally compare pinned source fragments and rows;
they are not a Lean theorem about JSON or PDF bytes. The coupled and
carrier finite diagnostics also exited 0, but do not materialize the
symbolic witness.

This review does not prove that the 75-operation graph has no positive
zero, decide positive-existence equivalence of the two graphs, prove
anything about ZFC consistency, or establish an iPRA endpoint. A complete
formal Lean verification and fresh authenticated dependency rebuild
remain distinct work.
