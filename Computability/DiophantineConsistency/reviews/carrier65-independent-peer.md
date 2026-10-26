# Independent review: first-Pell carrier65

Reviewer `/root/controller_certificate`; independent proof and new audit
author `/root/complemented47_review`; idea credited to the incoming
Carrier65 archive identified below. ROOT coordinates acceptance and any
later complete page. I edited no reviewed artifact or accepted source
and made no commit.

**PASS, within the stated retained interface.** I read the complete
256-line independent proof,274-line newly authored audit,75-line README,
125-line certificate,311-line inert incoming proof and all65 rows of its
443-line graph. I also checked the scalar-interface and canonical
completeness passages in both previously reviewed native proofs.
The unbounded carrier argument is sound; the finite audit passes normally
and under `-O`. Independent checks agree with the whole graph formula,
all56 leading homogeneous terms, both complete coefficient tuples and
the explicit witness maps. No mathematical or executable gap was found
in this scope.

## Exact bindings and execution boundary

Paths are relative to `research/carrier65-independent`.

| Artifact | SHA256 |
|---|---|
| `PROOF.md` |`53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749`|
| `audit.py` |`39678e9d35dc1995608a92396e1cfae6e47ac6cfb17a853edbf76e8aa01628a8`|
| `CERTIFICATE.json` |`12002fda7018df2b878f7b7f50b864f91fec709df85a7a5225e4b364fa663c48`|
| `README.md` |`81942daf0ffc142a04f7dd3e28018943d69ecec80a52e0e55fe5df93ee804fe4`|
| `INCOMING_CARRIER65.json` |`bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7`|
| `INCOMING_PROOF.md` |`75434688038192dd63381f02c1196727ba8b986fe45accf937967ff29f80fed8`|

The exact complete parent graph is
`candidates/one-page-low-padding2963/polynomial.json`,
`a9a752b912689d1f2418ce1dcc149670a1a3e80843f9ca635131fb8f43693c61`.
I independently hashed the808157-byte archive
`docs/incoming/ConZFC_Pell_Carrier65_2026-10-25.zip` as
`759b713ab7d3853f4fbd687439f25bada1a824e6b71da7dc0dec0516fca6e514`,
and read its two proof/graph members as bytes to verify that the local
inert copies match exactly. I did not execute, import or adopt incoming
Python, build commands, decoder changes or historical coefficient data.

The newly authored audit was read completely before execution. It uses
only the standard library, loads pinned data rather than executable
project modules, and has explicit exception guards. Both read-only
commands reproduced the entire certificate byte-for-byte:

```
python research/carrier65-independent/audit.py
python -O research/carrier65-independent/audit.py
```

These commands are relative to `Computability/DiophantineConsistency`.
I did not use `--write`.

## Unbounded sign and witness argument

For m>=2, the consecutive-product Pell descent correctly excludes
u²−m(m+1)v²=−1: the inverse unit sends a solution with least positive
|v| to one with0<v'<v. The proof correctly classifies all positive
norm-one solutions using the same descent, including the v=1 exclusion
and the endpoint(1,0). When E divides m, the trace recurrence gives
u=1 modulo E; the first positive index has v=2, and every later one
has v>=4(2m+1). These facts do not assume the sign of the newly
abbreviated tau.

On a positive new zero, Delta>0 and exact integer cancellation reduces
the product to five integer units. The consecutive-product obstruction
excludes N0=−1 even before knowing tau>0. Delta is0 or3 modulo4, so
the main and normalized strong norms cannot be−1. The auxiliary norm
is a square modulo4 and cannot be−1 either. Thus Nt=1 follows, and
the proof obtains all four norm signs before using scalar recovery.

Nt=1 forces C>0. With u=q−F and positive alpha, the bounds
2q−1<=(q−1)u+alpha<=q²−q−1 are valid. The exact scalar boxes give

    q(q²−1)<R<q⁴−q³<E−2.

In particular R>1. Positive n then gives tau=En+k−R>k+2>0.
Applying the already proved Pell classification now gives tau=1 modulo E,
so h=(k−R−1)/E is integral. Since R+1<E and k>0, h>=0. If h=0,
the first Pell index forces R=1; every later index forces k>E even
though k=R+1<E. Both are impossible, so h>0 and the restored Nk is1.
This constructs a positive parent zero from every positive new zero.

Conversely, the pinned parent canonical completeness supplies positive
zeros with all the required unit signs and R>0. Its positive first Pell
root satisfies tau>k and tau=1 modulo E, while Nk=1 gives k−R=1
modulo E. Thus n=(tau−k+R)/E is a positive integer. Substitution
restores the old tau exactly and preserves every remaining factor.
No division of arbitrary ambient assignments is being asserted.

The main theorem needs only the parent soundness and canonical
completeness interface. The stronger statement about a bijection on
all parent zeros is expressly conditional on a separate all-zero parent
sign theorem. It is not silently used to prove zero-existence equivalence.
The new proof therefore avoids inferring canonical signs from the old
six-factor product alone.

## Literal graph, exact degree and independent diagnostics

All parent rows are preserved except the three rows producing Nk and
the output multiplication by Nk. Three rows producing En,En+k and
tau=En+k−R are inserted after R. The result is65 live integer-leaf
binary operations, with37 multiplications,16 additions and12
subtractions; all14 positive inputs and all four ports are live.
There are no hidden rational leaves, divisions or extra variables.

The sole leading cancellation occurs in N1. With Z=X+gamma*H,
the exact identity is N1=Z²+2acZ−Hc². The new audit expands its entire
323-term ancestor polynomial and checks this identity. The factor
degrees are22,18,62,2,46. Independently multiplying the highest forms
gives exactly

    8*(beta*J)^87*gamma*i^4*(eta+zeta)^13*w^12*s^25*T^2*f^4
      *[w*(beta*J−F−alpha)−z*beta*J].

The two negative factors N0 and Ns cancel their signs. The complete
leader has56 terms and degree150; the selected z*eta^13 monomial has
coefficient−8*beta^88, which remains nonzero at every actual positive
beta. My independent binomial expansion of all56 terms matches the
certificate leader hash
`56475193d7a99303a9fe0fb8f9e350e38fb0a03af97c42882b13d1d50cd6cba7`.
The certificate's full main-norm hash is
`0c3ed0542525a5542a7110515ba1495edaa91c06d4f018fff1580ded425e1366`.

Separate stdlib-only reviewer code imported no project modules. It
evaluated the whole direct formula against the literal graph on128
deterministic signed assignments, and checked the all-value identity

    P66(substituted tau)+Delta=(P65+Delta)*Nk.

It independently generated447 applicable exact Pell carrier examples,
checking descent, trace congruence, size cases and both integer witness
maps. These are transcription diagnostics; the unbounded proof above
establishes the theorem. The audit's explicit mutations reject reversed
tau subtraction, a floating-point numeral leaf, an omitted factor and
an extra declared variable. Its complete-port mutation also detects
removal of the physical marker bit.

## Both exact native applications and limits

The low-padding2963 proof is pinned by
`ad952c6f1717a69e6b489e8c7af0bb52ce09414b78cc994b892b6e7f996d06f6`,
with finite certificate
`d165186ba400ebc2074716d2e1a142505b93c6d150b3f1fc44e574e9664ca039`.
The scaled-clause2953 proof is pinned by
`602b9560017f52835d36de8c1969ec8348381c8dae31876cb86905c5de2cdebe`,
with finite certificate
`957faf013a17c2e8e04c03be166d903263d2aadaccac604d31f0791e005776ed`.
Their sections4 and12 supply the required scalar boxes and canonical
P66 interface. Those full proofs were independently reviewed previously.

The new audit reconstructs all four whole ports for each tuple from
its bound3297-coefficient array and literal mask recipes. I additionally
compared both sets of certificate records against all eight whole
decompressed files in their respective reviewed page packages. Every
byte length, bit length and raw hash agrees. The tuples remain69685
and69449 raw bytes respectively. The carrier does not alter their
coefficients, physical/native masks, field geometry, controller proof,
seed or language calibration. It does not assert the two specializations
are equal. The inert incoming graph's historical admissible942 binding
is correctly identified as historical; a production page must rebind it.

This proves a uniform reduction from15 variables/66 operations/degree157
to14 variables/65 operations/degree150 under the retained interface.
It preserves the established zero-existence/Con(ZFC) equivalence with
the same explicit ordinary machine, arithmetic and syntactic-refutation
contracts. It is not an actual consistency decision, global-minimum
claim or new end-to-end formal-kernel/internal-ZFC replay. No new complete
page, decimal numeral, renamed-symbol layout or rendering is certified
by this mathematical packet; those require separate source and visual
review.
