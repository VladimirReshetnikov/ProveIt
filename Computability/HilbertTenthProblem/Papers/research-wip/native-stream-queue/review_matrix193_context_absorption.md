# Independent review of matrix193 context absorption

**PASS, no requested author change.** I read the entire frozen [proof](matrix193_context_absorption.md) and [helper](matrix193_context_absorption.py), authenticated the full [receipt](matrix193_context_absorption.json) and its six pinned dependencies, and independently reconstructed the complete numerical instance. Fresh normal and optimized exact replays of the current author helper from / both passed. No predecessor helper, archived code or historical suite was executed.

The reviewed author pins are:

| File | SHA-256 |
|---|---|
| matrix193_context_absorption.py | 1304ea242ca6a5faafdb527ac3e56c6cd06b0276dca6441fc3477c7065054485 |
| matrix193_context_absorption.json | 73f8cae212c6c1917e73cc76c7bf3c43b8c587748bbf4327eddf4c82e726a436 |
| matrix193_context_absorption.md | d7492809ba00a011c8280172bb016f96f3f6c240de6a823ed717d82bda5e4f4b |

## Arbitrary-context proof and membership scope

For any fixed finite contexts U,V over the active alphabet, let L=Psi(V#) inverse and R=Psi(U) inverse. The original target for middle word z is L Psi(z) inverse R. The proposed phase changes are

    A_i upper: L inverse H_i L,
    B_i upper: R G_i R inverse,
    C upper:   L inverse C0 R inverse.

The unchanged lower blocks retain the parent's exact lower-marker theorem. Every positive word with lower target P has the forced shape A(s) C B(reverse(s)); conversely every such word has that lower target. On that shape the two interior pairs L L inverse and R inverse R cancel at every phase boundary, leaving

    new upper product = L inverse (old upper product) R inverse.

The same generator-name word therefore witnesses both directions of the matrix membership equivalence, including the one-letter C case. No bound on its length is assumed. The argument does not depend on the particular numerical contexts used in the receipt. It is valid for all finite z as a matrix identity; machine semantics are inherited only when U z V is a valid configuration word.

This is not a global two-sided conjugacy or a homomorphism on arbitrary positive products. The author states the phase restriction explicitly and checks a concrete failure of the stronger assertion. That restriction does not weaken the membership theorem, since its lower target already forces the required shape.

All context matrices and every old upper block belong to H'. Consequently every new upper block, every generated upper product, and every encoded bare target also belong to H'. The [previously reviewed first-row theorem](review_matrix193_gamma1_recode.md) therefore applies to the whole new membership interface: equal first rows imply equality. The three unchanged lower observations recover the remaining lower entry by determinant one. This uses properties of actual generated matrices and actual targets, not an additional oracle about arbitrary supplied matrices.

## Complete saved arrays and target arithmetic

A separate fresh calculation, using generic nested 2×2 and 4×4 matrix multiplication and no author imports, reconstructed the context matrices directly from the pinned letter matrices. It rebuilt every new generator and compared all 193 matrices and 3,088 entries with the saved array. All 193 lower blocks are unchanged, all 386 block determinants equal one, and the new matrices are distinct. Rules, tiles, identifiers, alphabet, terminal and separator agree exactly with the parent.

The inherited 167-generator accepted word multiplies to diag(I,P) in all sixteen entries. This agrees with the saved fixture at x=0 and its original input [110A0]. The fixture is a valid finite configuration and a genuine accepted product; it is not asserted to be a universal program.

The all-value target identity follows by checking its two complete coefficient matrices:

    L inverse (LR) R inverse = I,
    L inverse (LDR) R inverse = D.

Thus the transformed target is chi I minus psi D for all scalar chi,psi. I independently checked both coefficient identities and expanded the two saved straight-line sources as exact linear polynomials. The old first-row outputs in the concrete fixture are

    -68793567899 chi - 7318135096020 psi,
     427044708833 chi + 45428242464304 psi.

The new outputs are

    chi + 52500 psi,
    -29036 psi.

Every gate and supplied port of each source is live. The complete ledgers are six operations, 4M+2A, and three operations, 2M+1A. These are different target frames, related by the full matrix identity; the two pairs of scalar polynomials are not asserted to be equal.

The fresh whole-array recount also agrees with all reported resource numbers: 1,543 nonzero entries, maximum absolute coefficient 4,652,051,305,867,101,902,730, maximum magnitude length 72 bits, and total magnitude length 53,734 bits. The target-operation saving therefore comes with larger fixed coefficients in this fixture.

The new constants depend on the selected fixed contexts and hence on the selected program. The result does not leave one numerical S193 unchanged for all programs. Correctly indexed Pell391 coordinates and an unbounded positive-product certificate are still absent from the three-operation count. No affine ordinary-input loader, fixed-arity membership certificate, or new complete universal Diophantine bound is established.

## Unrestricted linear-projection obstruction

I also checked the author's whole-group obstruction. The actual matrices are J=I+[[0,9],[0,0]] and A=I+N, with

    N=[[-20,10],[-40,20]], N²=0.

Therefore the displayed formulas for all integer powers, including negative powers, follow exactly. For a first-row functional p M11+q M12, q=0 gives the collision I,J. If q is nonzero, r=9q and n=10q−20p give equal values on A^r and J^n, while their lower-left entries differ. Clearing rational denominators and adding a constant do not remove the collision.

This excludes a fixed affine linear first-row projection on the entire current H' group. It does not assert a false input, an accepted product with the wrong target, or an obstruction to every possible projection on a more restricted family. The author's stated scope makes those distinctions correctly.

## Replay evidence and boundary

The frozen author's checks cover 193 phase identities, 145 forced-shape products, the accepted 167-factor product, 28 signed/rational target comparisons, thirteen indexed literal-word targets and seven linear-collision illustrations. My independent numerical reconstruction and linear-polynomial expansion supplement those replays; the unrestricted results come from the proofs above, not from finite examples.

The author's CLI uses explicit exception checks, rejects duplicate/nonfinite JSON, and recursively compares exact JSON types. Both commands passed from / against the installed predecessor bytes:

    python3 /absolute/path/matrix193_context_absorption.py
      --root /absolute/path/native-stream-queue
      --expect /absolute/path/matrix193_context_absorption.json

    python3 -O /absolute/path/matrix193_context_absorption.py
      --root /absolute/path/native-stream-queue
      --expect /absolute/path/matrix193_context_absorption.json

Each displayed command is to be entered on one line. This is a bounded proof/source review of the frozen packet, not a general-purpose API audit or a reconstruction of the arbitrary-program U15 compiler. No repository or frozen author file was modified.
