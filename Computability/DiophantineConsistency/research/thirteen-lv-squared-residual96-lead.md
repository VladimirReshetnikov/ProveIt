# Prospective 13-variable, 77-operation, degree-96 equation

Read-only algebraic follow-up, 2026-10-26, by `complemented47_review`.
The accepted LV72/124 and LV74/122 packets and maintained page are unchanged.
This note gives a concrete complete-schedule modification and zero-set argument;
it is not a materialized graph, a new executed audit, or a Lean theorem.

## Construction from the accepted LV72 equation

Retain exactly the thirteen positive coordinates, four current2011 ports, and
all abbreviations of `thirteen-lv-carrier122/PROOF.md`. In particular the carrier
is `L*V`, the ordinate is signed, the source high port has its single beta shift,
and the strong factor is the **uncorrected** normalized factor

```
P = tau^2-ell*(ell+k)
Q = D^2-Delta*c^2
U = Delta*(f^2-1)*(V^2-y^2)+y^2
Z = f^2-(b*i)^2*c^2*(Delta*c^2).
```

Replace `p72=P*Q*U*Z-1` by

```
p77 = (P*Q-1)^2 + (U-1)^2 + (Z-1)^2.
```

The positive zero sets are identical, on the same thirteen coordinates and
uniformly for the accepted positive-beta domain. No witness changes are needed.

* A p72 zero gives `P=Q=U=Z=1`, by the accepted separate norm-sign argument.
  Thus it is a p77 zero.
* A p77 zero is a sum of three nonnegative integer squares, so `P*Q=1`,
  `U=1` and `Z=1`. Since P and Q are integer units, each is 1 or -1.
  The accepted consecutive-Pell argument excludes P=-1 on every positive
  input, before any equation is assumed. The actual Delta residue excludes
  Q=-1; equivalently P=1 already forces Q=1 here. Hence it is a p72 zero.

This proof uses the entire zero sets; it does not assume a canonical witness,
positivity of y or V, a source zero, G>=0, or already decoded norms. It is enough
to compose the accepted LV positive-zero equivalence with this elementary
integer identity. The construction supplies no HA or internal-ZFC derivation.

## Literal tail and operation count

The actual 72-row graph ends with the live row `product0=N0*N1`, followed by
`product1=product0*Na`, `product4=product1*normalized_Ns`, and output
`polynomial=product4-1`. Keep the prefix through `product0` and replace those
last three rows with exactly these eight rows:

```
resPQ = product0 - 1
resU  = Na - 1
resZ  = normalized_Ns - 1
sqPQ  = resPQ * resPQ
sqU   = resU * resU
sqZ   = resZ * resZ
sumPQ_U = sqPQ + sqU
polynomial = sumPQ_U + sqZ.
```

Thus the proposed complete schedule has `72-3+8=77` binary operations:
42 multiplications, 18 additions, 17 subtractions. Squares count as ordinary
multiplication gates. The original V-squared row remains necessary inside U.
All old factor-producing rows remain connected to the output. Actual polynomial
dependence of every coordinate/port should still receive a separate finite
audit; syntactic connectivity alone is not a dependence proof.

The stronger-factor correction used in LV74/122 is unnecessary for this
degree target: its reduction from degree36 to34 affects a square below the
maximum degree96 and costs two additional operations.

## Exact degree from the accepted factor leaders

The accepted full factors have degrees `deg P=22`, `deg Q=18`, `deg U=48`,
`deg Z=36`. Therefore the three squares have degrees80,96,72. The degree96
leader is unique to `(U-1)^2`, so there is no leading cancellation. With the
accepted homogeneous abbreviations `q0=beta*J`, `k0=eta+zeta` and
`C0=q0-F-alpha`, it is

```
256*q0^44*k0^8*s^12*w^8*f^12*T^8*C0^4.
```

The coefficient of `J^48*eta^8*s^12*w^8*f^12*T^8` is
`256*beta^48`, nonzero at the actual positive beta. This proves exact total
degree96 conditional only on the already audited parent factor leaders.
An independent whole-gate audit of the modified graph remains to be made.

Within this simple residual-squaring approach, pairing P with Q is useful:
four separate residuals give the same degree96 at79 operations, while pairing
P with Z or Q with Z produces larger degree. This is not a general minimality
claim. The new point trades five operations for28 degrees relative to LV72/124;
it does not improve every size metric or the maintained65-operation front.

## Other algebraic shortcuts checked

The accepted mixed product already uses the relation `V=f^2*L-c` to reduce the
carrier's degree. Replacing it by L alone, L-squared, or V would lose the
proved two-sided bound `abs(V)<=L*V<=V^2`: the proof permits negative L and V,
and supplies no bound `L^2>=abs(V)`. Such a replacement needs a new domain
argument, not just a polynomial rewrite. The present note does not claim an
actual zero counterexample to those prospective replacements.

The existing correction `Delta*c^2+P-1` cancels the strong coefficient's
degree22 leader. Its remaining degree20 leader is independent of gamma,
whereas Q's degree18 leader contains gamma. Consequently adding a polynomial
multiple of `Q-1` of degree at most2 cannot cancel that remaining leader:
every resulting degree20 term is divisible by gamma. This rules out that
specific simple correction, not all reductions using the other norms.

The mixed-carrier origin remains the credited inert archive lead recorded in
`scaled-auxiliary118/THIRTEEN_VARIABLE_LEAD.md`; no archive code was executed.
This note's only proposed new change is the three-residual finalizer above.

## Source pins and next bounded check

The complete accepted LV README and ordinary proof, the earlier prospective
mixed-carrier note, and the relevant exact graph tail/Lean norm contracts were
read. No Lean build or mathematical computation program was run here.

* `thirteen-lv-carrier122/PROOF.md`:
  `0b4652adbdb5938ba52bf0865799acdc19dcbc13e23948ce16dc33c83cfd8386`.
* `thirteen-lv-carrier122/polynomial72.json`:
  `2ac2f00f08146d61b8d98c15b3f844b0ae00330eba825f80629d0a1e48e27045`.
* `Lean/DiophantineConsistency/ThirteenLVCarrier.lean`:
  `d64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02`.

After review, a small separate Lean zero-set finalizer and deterministic graph
delta/degree audit would make this candidate concrete. Neither requires changes
to the frozen native, controller, seed, or LV proofs.
