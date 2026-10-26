# Independent review of the Carrier65 rank and omitted-witness modules

Reviewer: `/root/circuit_reduction`, 2026-10-25. Verdict: **PASS** at the
exact source hashes below. ROOT authored the rank and witness-integration
modules. The reviewer read both complete modules and the complete rank
checks, compared them with the displayed polynomial and ordinary proof,
and independently reran Lean. No reviewed source was edited.

The reviewer authored the separately reviewed `FirstPellCarrier` dependency.
This receipt is an independent review of ROOT's scalar bounds and their
integration with the actual polynomial; it is not presented as an
independent review of the reviewer's own first-Pell implementation.

## Exact bindings

All paths below are relative to `Computability/DiophantineConsistency/`.

| Source | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CarrierRankBounds.lean` | 93 | `ca57b2098d1d99c45049ad77441b949ce3087cbc78eddd102f0b4ffd976fbbae` |
| `Lean/checks/CarrierRankBounds.lean` | 23 | `04fa02d5c2bcefaf0641ab43cf617ce065e6740c77329ce3d2ab820e8745654f` |
| `Lean/DiophantineConsistency/Carrier65Witness.lean` | 80 | `2b9324dc4594200c917b353b51a049815c0999beff31f26152d84e3fe0731f1f` |

The complete underlying actual-polynomial module was also read:
`Lean/DiophantineConsistency/Carrier65.lean`, 256 lines, SHA256
`be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154`.
The first-Pell dependency is `FirstPellCarrier.lean`, SHA256
`3e96510fa492760fe0876e2e230b9520c1429a20c7272c2a06b465b249ed859f`;
its separate focused checks have SHA256
`adff47a34509c867bd94c769494b41a6c7fea3cab98e7a1a60cf69dbe6a140b7`.

The ordinary comparison is `research/carrier65-independent/PROOF.md`,
SHA256 `53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749`,
especially sections 3 and 4. The displayed arithmetic was checked directly
in `equation.tex`, SHA256
`a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`.
This is the maintained decimal 2011-field page; no prospective 1997-field
specialization is silently substituted.

## Scalar bounds and their strength

The rank definition is exactly

```
((q-1)*(q-F)+alpha)*(q^2-1) + (MC+q*MF)*J.
```

On the displayed page, `b=beta*J=q-1`, `MC=mu`, and `MF=omega` already
includes its one beta shift. Thus there is neither an extra mask shift nor
an omitted rank summand.

`carrier_pos_of_transport` uses the actual transport unit and positivity
of K, w, F and z to prove `C=q-F-alpha>0`. It needs no supplied sign of
alpha or rank, and no Pell or native hypothesis. Its contradiction is
the same one as ordinary section 4: if C is nonpositive, the transport
expression is at most zero.

`rank_bounds` then proves

```
q*(q^2-1) < R < q^4-q^3.
```

The intermediate bounds on `G=(q-1)*(q-F)+alpha` are exactly
`2q-1 <= G <= q^2-q-1`. The positive mask term is strictly below
`(1+2q)*(q-1)`, using `beta*J=q-1`, MC<beta and MF<2beta. The upper
polynomial simplifies exactly to `q^4-q^3`; there is no dropped term.

The hypotheses are not stronger than the ordinary scalar box. In fact
`q>=3` is weaker than the ordinary consequence `q>=32`, and MF>0 is
weaker than MF>beta>0. The theorem does not assume a rank bound, positivity
of the first root, or the intended interpretation of any packed variable.

`rank_window` derives both `1<R` and the strict `R+2<w*s*q^4`, using
positive integer w,s and `q^3>=3`. This is precisely the strict window
required by `FirstPellCarrier.restore_quotient`.

The complete rank checks instantiate beta=31, q=32, J=1, MC=1, MF=32,
F=alpha=w=s=1. They verify the transport example with K=29,z=30, the
actual rank 985151, and both strict window inequalities. These checks
exercise the scalar theorem, not a purported complete consistency witness.

## Actual-polynomial integration

`Carrier65.core` has exactly the displayed coordinate order

```
J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma.
```

In particular the integration correctly reads w at 8, s at 7, n at 9,
eta at 10, zeta at 11 and z at 3. The kernel identities `rank_shape`,
`transport_shape`, `scale_shape`, `first_shape`, and `carrier_shape` match
the displayed definitions. The first-norm identity is
`ell*(ell+k)=(E*Y)*(E*Y+1)*k^2`, with no assumption on tau.

`PortBounds` states exactly beta>=31, K>0 and
`0<MC<beta<MF<2beta`. The integration explicitly derives q>=3 from
beta>=31 and J>=1. It does not mistakenly use the weaker `q_ge_two`
theorem, whose beta>0 premise alone would not supply q>=3.

At every positive actual zero, the existing sign theorem supplies W=1
and P=1 without assuming a sign for C, R or tau. The witness module first
derives C>0 and the rank window. Only afterward does it invoke the first-
Pell witness theorem with E,Y,k,n>0 and the exact carrier equation. This
order agrees with the ordinary proof and avoids circular positivity.

`positive_zero_restores_index` concludes tau>0 and existence of exactly
one integer h satisfying both h>0 and `k-h*E-R=1`. Its uniqueness proof
uses E>0 and the actual index equation. The final
`polynomial_zero_restores_index` theorem takes a zero of the actual
`MvPolynomial (Fin 14) Z`, applies its evaluation identity, and obtains
the same conclusion. No auxiliary native or canonical-witness premise is
inserted into that theorem.

## Independent execution and proof boundary

The following were independently run successfully from the repository
root with the configured Lean 4.32.0 environment:

```
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CarrierRankBounds.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/CarrierRankBounds.lean
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier65Witness.lean -o .lake/build/lib/lean/DiophantineConsistency/Carrier65Witness.olean
```

A separate temporary import/check file printed the axioms of
`Carrier65Witness.polynomial_zero_restores_index` and
`Carrier65Witness.positive_zero_rank_window`. Both reported only
`propext`, `Classical.choice`, and `Quot.sound`. The three rank theorem
axiom reports had the same standard set. No `sorryAx`, custom axiom or
native-decide axiom appeared.

These are fresh checks of the stated local modules against the prepared
dependency cache. They are not a fresh replay of every ancestral source
or the full repository. The proof endpoint is the arithmetic recovery of
the omitted witness for arbitrary ports satisfying `PortBounds`. Binding
the entire fixed native recipe, completing both directions to its precise
refutation predicate, and obtaining the final Con(ZFC) theorem remain
separate obligations. No degree or operation-count formalization is
claimed by these two integration modules.

There are no requested source changes or unresolved findings in this scope.
