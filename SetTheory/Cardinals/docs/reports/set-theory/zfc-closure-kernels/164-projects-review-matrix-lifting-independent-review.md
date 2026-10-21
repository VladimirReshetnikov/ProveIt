# Independent review of the total raw-code matrix lifting

The lifting in `formalism-work/projection_basis.tex` is mathematically valid. It strengthens the earlier implication-context countermodel to all numerical inputs for the selected **total** projectors. It does not model the full native calculus.

Let the implication matrix be

|→|0|1|2|3|
|---|---:|---:|---:|---:|
|0|3|3|2|3|
|1|3|3|3|3|
|2|0|3|3|3|
|3|0|1|2|3|

The designated value and truth value are 3. Define `h(0)=3,h(1)=0,h(2)=1,h(3)=2`. For `n≥4`, define `h(n)=h(ell(n))→h(r(n))`, where `ell,r` are the total components of `unpair(floor(n/4))`, without inspecting the native tag.

## Universal proof

Both children are at most `floor(n/4)<n` when n≥4. The recursion therefore defines h on every natural code. For every a,b,

\[
 h(I(a,b))=h(a)\to h(b).
\]

If I(a,b)>0, its exact numerical destructors are a,b and the recursive equation applies. If I(a,b)=0, Cantor injectivity gives a=b=0, and the equation is the matrix identity `3→3=3`. This explicitly handles the zero alias. The last matrix row is the identity, so designated premises preserve designatedness under MP. Truth 0 is designated; falsity 1 is not.

For a word w among epsilon,L,R,RRR, follow the total projector path from arbitrary A. There are two exhaustive cases.

* If a proper prefix reaches 1, 2, or 3, its next projector is 0, and all later projectors remain 0. Thus the selected U is exactly 0. The constant-truth fourth-argument matrix family applies.
* Otherwise each proper prefix is either 0 or at least 4. Its h-value decomposes as implication of its two children's h-values: by the recursive definition for n≥4, and by `3→3=3` at 0. Iterating gives precisely the corresponding implication context with h(U) at the selected position. The already exhaustively verified finite context-family theorem applies.

Hence every numerical instance of the five families with `U=0,A,ell(A),r(A),p_RRR(A)` is designated, including nonimplication-tag inputs. Implication homomorphism also transfers the finite-matrix validity of I, K, Peirce, and cd59 to every numerical instance of those schemas.

All four matrix values have numerical representatives among 0, 1, 2, 3. The raw unrestricted instance

\[
 L(2,1,3,1)=2526379112
\]

has h-value 2, because its four inputs have values `(1,0,2,0)`. It cannot be derived using only truth, MP, the five selected total-projector families, and the listed additional valid schemas.

This is a theorem-recovery obstruction for the stated restricted resources. It does not establish that those resources, after adding the other native rows, GEN, or the theory bundle, fail to be equiconsistent with ZFC. It is not a lower bound on consistency strength or machine size.

## Independent arithmetic replay

`review_matrix_lifting.py` imports no author checker. It uses an independent binary-search Cantor inverse and exact integers. The receipt `matrix-lifting-independent-review.json` records:

* 9,216 implication-homomorphism cases, with 0≤a,b<96;
* 524,288 total-projector family cases, with 0≤A<8,192, arbitrary matrix values for B,C, and four projector words;
* 5,129 encountered proper-prefix low-seed escape cases;
* all 64 constant-truth matrix instances and the exact numerical unrestricted witness.

These finite checks supplement the universal argument above; they are not presented as an exhaustive numerical proof.

```sh
python3 -B review_matrix_lifting.py --output matrix-lifting-independent-review.json
```
