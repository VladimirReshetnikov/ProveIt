# Independent review: degree 253 and 252 positive equations

## Verdict

ACCEPT, relative to the explicitly retained ordinary source61/native/controller calibration. No fatal error or mathematical gap was found in the new soundness map, completeness construction, exact-degree proof, or literal graphs.

- `positive/first.json`: ten strictly positive variables, exact degree 253, 102 live binary operations (61 multiplications, 21 additions, 20 subtractions).
- `positive/second.json`: ten strictly positive variables, exact degree 252, 104 live binary operations (62 multiplications, 21 additions, 21 subtractions).

This is not a claim that ZFC is consistent, a global simplicity record, or a new Lean/Rocq endpoint. The inherited logical calibration is retained and authenticated, not re-proved from scratch here.

## Source and independence

Reviewed the full new `positive/PROOF.md`, the complete preceding `prior/PROOF.md`, the relevant source61 auxiliary reconstruction proof, the zero-offset ratio/source interface, every new literal row, and the complete coefficient-binding objects.

`independent_audit.py` was written separately for this review. It imports no producer, package checker, or downloaded source program. It implements canonical commutative free-expression normalization and an independent formula transcription, traverses the literal graphs, recomputes byte bindings, and separately checks free-ring identities with SymPy. Its bounded modular-polynomial tests are supplementary, not the proof of the universal degree bound. Normal and optimized runs agree exactly; see `AUDIT.json`, `NORMAL_OUTPUT.json`, and `OPTIMIZED_OUTPUT.json`.

## 1. Whole-polynomial identity and positive soundness

The entire new literal output, not only its final carrier, was verified exactly against the independent formula and the old uncentered graph under

i_old=2i, n_old=n+S_j.

The comparison is over independent indeterminates for all ten inputs and all four coefficient ports. No finite sample or assumed root is used in this identity check. The changed center and doubled E register agree; the full carrier and each shared kernel register agree after substitution.

The required positivity is unconditional on the positive domain. With p=(q²+1)Y, v0=p²X, k=eta+zeta,

0<Q2=p(v0−p²)k²<Q1=pv0k²<v0²k²<D.

Since E=2E0 and E0=ic²>0,

0<E0(2A−1)D<S_j=2AE0D−E0Qj<ADE.

Hence the substituted old i and n are strictly positive for every positive input. This valid transfer avoids all the possible circular uses of Pell roots, source transport signs, or denominator congruences. The old polynomial's full soundness theorem therefore applies to every new positive zero.

## 2. Completeness and every positivity obligation

The parent canonical source supplies X=2^R>q, R≡3 modulo4, q³|Y, q⁴|X, nonnegative transport t, D=tau², and positive eta,zeta. These facts are supplied before choosing the strong Pell witness.

The determinant-one recurrence matrix has finite order modulo 2tau c². A positive period gives a positive Pell ordinate I divisible by 2tau c² and defines i=I/(2tau c²)>0. Thus I=tau E exactly. This is an existence construction with fresh witnesses, not an unjustified evenness restriction on an arbitrary old zero.

The retained source61 positive auxiliary reconstruction lemma needs only c|I, not an odd or minimally sized multiplier. The new witness satisfies the stronger divisibility c²|I. Its explicit

V*=chi_(Delta I)(R)/(Delta I),
y=psi_(Delta I)(R),
T*=(V*+c+Rf²)/(cf²)

is integral by the two compatible congruences modulo c and f² proved in that lemma. R≡3 modulo4 is present. Choosing a period does not destroy any hypothesis. Pell growth gives V*≥9Q², so the retained bound T*>9Delta I>alpha makes T=T*−alpha strictly positive.

For carrier positivity, y>V*>1 and y<2V*. Therefore

h_y=y−V*=(V*²−1)/((Q−1)(y+V*))>V*/(4Q)≥9Q/4.

The center is bounded above by ADE, while f>(A−1)I. Thus S_j−tau f<DE<I². Also the canonical projection gives 0<kappa<c<I and 0<Y/q³<c<I. In the proposed integer n, all remaining terms are nonnegative, and the possible negative loss is <I²+2I<4I². Since Q=Delta²I² and Delta≥3, h_y>4I². Consequently n>0 even at t=0.

The exact rational-center identity then gives Z_j/M=tau f+y, so a factor of the full norm vanishes. Every coordinate has now been constructed as a strictly positive integer. No pointwise inverse of the soundness substitution is asserted or required.

## 3. Exact degree, including cancellation

The proof works in the formal Laurent field obtained by scaling all independent variables. It is algebraic, not an analytic approximation. Both square roots have square leading forms, so the specified formal branches exist.

The exact identity

(ADE−g)(ADE+g)=D²E²−D, g²=D Fs

gives deg(ADE−g)=17. The further exact rearrangement

(ADE−g)−DE/(2A)=[DE(ADE−g)−2AD]/[2A(ADE+g)]

has degree at most9. Both polynomial remainders D−AQj were independently expanded and checked. Their degrees are15 and14, yielding center defects of exact degrees16 and15. Their leading forms do not vanish; the degree-nine error cannot cancel either.

The rational carrier remainder has degree at most6. Also deg(y−V)=−4. Thus the four norm factors have exact degrees38,38,25,16 or38,38,25,15. Multiplication by delta²M⁴ yields253 and252.

Independent symbolic multiplication of all complete leading factors gives precisely

[N1]_253=−2^20 q0^122 X0^27 Y^60 i^10 k0^32(q0−F)²,
[N2]_252=+2^20 q0^122 X0^26 Y^60 i^10 k0^32(q0−F)².

The coefficients at J^122 x^27 Y^60 i^10 eta^32 F² and J^122 x^26 Y^60 i^10 eta^32 F² are respectively −2^20 beta^122 and +2^20 beta^122. They are nonzero at the actual authenticated beta. The upper bound and attained coefficients therefore establish exact global degrees, independently of the supplementary ray checks.

## 4. Literal data and robustness

The independent checker verifies:

- Every one of 68 package manifest files and 52 retained parent source files.
- All four compressed and decompressed constant hashes, exact bit lengths, unchanged parent bytes, and the stated coefficient-box inequalities at the actual numbers.
- The full original compact44 binding, including the already-shifted MF. No source34 or BFS coefficient was mixed into it.
- Every row's valid operator and topological references, uniqueness, the whole input list, liveness of every input and operation, operation-class counts, and syntactic degree metadata.
- Full free-polynomial output identity with the prior uncentered circuit and full equality to the independently transcribed closed formulas.
- Complete four-factor norm identity, radical-defect identity, both remainder identities, and both full symbolic leading forms.
- Four complete modular univariate polynomials using the authentic payloads, agreeing with the degree and leading form.
- Ten actual graph/binding corruptions rejected: wrong even factor, reversed center sign, wrong correction operand, dead gate, and changed MF binding for each candidate.

No producer or inherited checker was executed. Hash verification authenticates retained source texts; it does not turn the inherited semantic calibration into a newly machine-checked proof.

## Accepted file identities

- first.json SHA-256: 50ec22ff0d9af5ff91161cbb3b54803bf2dae8b5d1f527cbb452cd3406d0f1e8
- second.json SHA-256: 708865394c91d175be177bf398977b8bebe7c4a9cbb61cb8fd1cb3b8ecd6869e

Any later mathematical, graph, or binding change requires re-review and a fresh receipt. Formatting-only changes to exposition do not change these polynomial identities.
