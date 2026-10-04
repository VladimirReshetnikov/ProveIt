# Independent audit of the nonelliptic quadratic certificate

Audit date: 4 October 2026 UTC

## Verdict

**PASS. No correction is required for integration.** Every asserted rational-input branch admits the stated finite rational conjunction, and the integer slack construction gives a sum-of-squares polynomial of exact total degree two with a unique positive witness tuple on valid inputs and none on invalid inputs. The zero-witness convention, unreduced counts, native input aliases, and half-open example are correct.

This is a source-bound conventional mathematical review. The author script and its recorded results were read only as inert text/data. No author or upstream program was executed, and no scientific source was edited.

## Source pins

Source directory: `/workspace/shared/nonelliptic-quadratic-certificate60-20261004`

- `PROOF.md`: `faaf236df7e6da3f05a38ea75ab91f0aa91e37db581fa00bd6116215bd306346`
- `SHA256SUMS`: `9ca99c66131f8b8c3f6324209fd08ada006caf0e5833099208d100d457247601`
- `verify_exact.py`: `a018f8db884b4d5ee8804f250fc67f0c8e063664aa8b6012694a54b3428f3557`
- `verification.json`: `39d75347cb025f0a7b0c12d12c39dd4342190b8286acb75528e1ec62bf4c62a5`
- `README.md`: `6a7fcb5e316d4a95cc727de8519de0817f0064313a45eceacdb697eae11dd9e2`

Dependency: the previously independently audited classification `PROOF.md` remains pinned to `70eb8f8398d474c3343493fc88c006ce91951a2eb747c9b4133c5c481b666231`.

All line references below refer to the pinned companion `PROOF.md`. Preservation evidence appears in the before/after inventories and `preservation.json`; it covers source bytes, file inventory, modes, sizes, and nanosecond mtimes.

## Rational conjunction and branch ledger

Lines 30–53 correctly use only rational-point equivalence. For B={0}, K={0}. For an irrational one-dimensional bounded-orbit subspace, the only rational point of B is again zero. Replacing that real line by the rational-point condition u=0 is essential and valid; no irrational line is represented by false rational equations.

A rational B line has one rational homogeneous equality. The nonnegative scalar case needs P alone, while the negative scalar case needs P and its one-step preimage. Unit Jordan blocks enter through this line case. All stable full-dimensional blocks, including singular and nontrivial Jordan cases, admit the already proved finite strict horizon. Real semisimple unit dynamics satisfy A²=I, and finite-order nonreal dynamics have order 3, 4, or 6.

For mixed unit/nonzero-stable spectra, the two time-prefix lists are strict and the two limiting projector lists are weak. When the stable eigenvalue is zero, the limit is reached, so all three time lists are strict. Thus the branch counts in lines 93–104 are correct, in order:

    (r,s,t)=(2,0,0), (1,m,0), (1,2m,0),
            (0,(H+1)m,0), (0,2m,0), (0,dm,0),
            (0,2m,2m), (0,3m,0).

Repeated or redundant rows receive distinct, individually forced slack variables. Keeping the original time-zero guards guarantees s+t>0 outside the two zero-rational-kernel branches. These are explicit construction counts, not minimal ones.

## Native aliases and sign preservation

Lines 13–19 are exact. With D=g₁+g₂+g₃, N=3D, X=3g₁−D, and Y=3(g₁+g₂)−2D. Hence (X/N,Y/N) is precisely the displayed centered native normalization. Positive integer inputs guarantee N>0.

The transformation g↦(N,X,Y) has determinant 27. Direct substitution verifies its rational inverse:

    9g₁=N+3X,
    9g₂=N−3X+3Y,
    9g₃=N−3Y.

Consequently no input or denominator witness has been introduced. Clearing each row by a fixed positive integer preserves its sign; multiplying the normalized rational row by the positive N gives exactly the integer homogeneous forms E_j, L_i, and M_k in lines 55–71. Every rational coefficient can be cleared in this way.

## Correctness and unique positive witnesses

For a fixed positive input, the squared residuals are nonnegative integers, so their sum vanishes exactly when each residual vanishes. Strict L_i>0 forces and is equivalent to the unique positive integer slack p_i=L_i. Weak M_k≥0 forces and is equivalent to q_k=M_k+1>0. The +1 shift is indispensable at equality. The equality residuals require no witness.

It follows that the complete ledger has exactly three positive input leaves, s+t positive witnesses, r+s+t affine residuals, and one final polynomial equation. No denominator, selector, sign, or POWER witnesses are hidden in the aliases.

Each residual has total degree at most one in the original inputs and slack variables, so F has degree at most two. If a witness is present, its own square contributes coefficient 1 to that witness's square and no other residual contains that witness. Therefore F has exact degree two. In the no-witness recipe F=X²+Y²; expanded in g this is

    5g₁²+2g₂²+5g₃²−2g₁g₂−8g₁g₃−2g₂g₃,

which is nonconstant of exact degree two. Its zero set on positive inputs is exactly g₁=g₂=g₃.

The product Z_{>0}^0 consists of one empty tuple, so the zero-witness statement is literally correct. It is not an existential witness omitted from the count. Uniqueness is per fixed integer triple and fixed residual list. Rescaling the triple may change slacks while leaving the normalized point unchanged, as the statement correctly explains. Exact degree is a property of the unreduced construction and is not claimed to be minimal on the restricted input domain.

## Half-open example

Lines 130–168 are correct. For A=diag(1,1/2), the rectangle is invariant and the nonrectangular row gives u+2^(−n)v<1/6. It holds for every n≥0 exactly when u+v<1/6 and u≤1/6. The weak boundary is a genuine unattained limiting constraint.

The five strict forms N±X, N±Y, N−6X−6Y and the weak form N−6X expand to the six linear forms displayed in lines 157–162. For g=(6,1,5), they give (N,X,Y)=(36,6,−3), strict values (42,30,33,39,18), and weak value 0. The unique positive tuple is consequently (42,30,33,39,18,1). Every finite orbit value is 1/6−2^(−n)/12<1/6.

For g=(7,1,5), (N,X,Y)=(39,8,−2), and the strict values are (47,31,37,41,3), all positive. The weak value is −9, forcing the inadmissible slack −8. This correctly rejects an input that passes every time-zero guard. The example's polygon is explicitly abstract and is not asserted to be a physical compiler chamber.

## Claim boundary and integration

The proof applies to fixed A and P, with A excluded only when it is infinite-order elliptic. Despite the abbreviated title, finite-order elliptic branches are explicitly included. Large stable horizons prevent inferring uniform polynomial-size explicit compilation. The finite polynomial-sign obstruction for infinite-order elliptic membership is not a lower bound on existential-integer certificate degree or arity, and the note correctly refuses that inference.

The author verification file reports 729 finite fixtures; that report is source data, not a computation independently rerun in this audit. The universal conclusion follows from the rational-conjunction reduction and the elementary unique-slack argument above. This new corollary may be integrated alongside the frozen classification without changing that classification or any physical implementation claim.
