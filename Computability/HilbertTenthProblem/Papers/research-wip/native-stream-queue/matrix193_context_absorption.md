# Absorbing fixed contexts into the directed193 generator phases

The [complete saved193-generator fixture](matrix193_context_absorption.json) absorbs the fixed left and right word contexts into the existing A/B/C generator phases. The ordinary input parameter x is unchanged, and the target becomes the bare even block `B^-x`. In the current faithful Gamma1(5) coordinates, its first row costs **3=2M+1A** from correctly indexed Pell391 coordinates, instead of the six generic context-assembly operations. No extra generators, matrix dimensions, tile identifiers or product factors are introduced.

This is a fixed-context transformation: the generator array now depends on the selected program's fixed contexts. It is not a claim that one unchanged numerical S193 recognizes every context at the same bare target. The exact Pell index and the unbounded product certificate remain unpaid. There is no new complete universal Diophantine operation bound.

## 1. Transfer for arbitrary fixed contexts

Use the complete [Gamma1(5) parent](matrix193_gamma1_recode.md), with faithful twenty-letter encoding Psi, upper subgroup H', and fixed lower target P. The old generators are

```
A_i=diag(H_i,E_i),            H_i=Psi(h_i),
B_i=diag(G_i,P^-1 E_i^-1 P), G_i=Psi(g_i)^-1,
C=diag(C0,P),                C0=Psi([J1]#)^-1.
```

Fix any finite context words U,V over the same active alphabet and put

`L=Psi(V#)^-1, R=Psi(U)^-1`.

For a middle word z, the old upper target is

`Psi(U z V #)^-1 = L Psi(z)^-1 R`.

Define a new fixed set of193 integral determinant-one block matrices by retaining every lower block and setting

```
A_i'=diag(L^-1 H_i L, E_i),
B_i'=diag(R G_i R^-1, P^-1 E_i^-1 P),
C'  =diag(L^-1 C0 R^-1, P).
```

All constants are effectively computable from the fixed contexts. They can be much larger than the parent coefficients; Section4 gives the actual fixture's tradeoff.

The lower-marker theorem is unchanged. A nonempty generator word has lower product P exactly in the inherited shape

`A_(i1)...A_(id) C B_(id)...B_(i1)`.

This includes d=0, the single generator C. On every such word, conjugations telescope separately on each side of C, giving

`upper(new product)=L^-1 upper(old product) R^-1`.       (1)

For example the middle factors in the product are

`(L^-1 H(s) L)(L^-1 C0 R^-1)(R G_rev(s) R^-1)`.

Thus the same generator-name word is a witness in both directions, with exactly the same length:

```
diag(Psi(z)^-1,P) belongs to the new semigroup
    iff
diag(Psi(U z V #)^-1,P) belongs to the original semigroup.
```

The statement applies to all finite z; the original machine interpretation is inherited when `U z V` is a valid configuration word. No newly claimed theorem about malformed machine configurations is needed.

Equation(1) is a **phase identity on the words forced by the lower target**. Multiplying every arbitrary semigroup element on its two sides by L^-1 and R^-1 is not a homomorphism. The argument does not assert that identity for words outside the forced A/C/B pattern. The helper explicitly includes a single-A countercheck against that incorrect stronger assertion.

## 2. The exact projection and ordinary input remain intact

Because L,R lie in H', every new upper block remains in H': the A and B phases are inner conjugations, and the central bridge is also a product of elements of H'. Thus every upper product and the bare target Psi(z)^-1 lie in H'. The parent's first-row injectivity theorem applies without alteration. The same two varying upper observations recover the full upper target. Retain the parent's three fixed lower observations `(11,12,21)=(1,2,0)`; determinant one recovers its remaining lower entry.

Consequently the projected predicate still describes exact membership among actual generated products. No new subgroup-membership, determinant or integrality oracle is inserted. This does not project arbitrary unrelated integer matrices.

For the ordinary-input family, the [inherited initialization theorem](u15_unary_block_interface.md) supplies, after choosing a program, fixed contexts U_S,V_S and the words

`U_S (W²)^x V_S`, with W=`01010111` and natural x.

Apply the transfer with those fixed contexts. The input is still x, not the bit length, a matrix coordinate or a freely chosen Pell index. The resulting fixed-program numeral recipe emits193 new generators. Each selected program receives its own fixed array; the concrete fixture below is not asserted to be one of the theorem's universal compiled programs. No arbitrary-program compiler was run here.

## 3. Complete target arithmetic: six gates become three

The parent has

```
B=Psi(W²)=[[-52109,29036],[-94920,52891]],
B=391 I+D, D=[[-52500,29036],[-94920,52500]],
D²=152880 I.
```

For correctly indexed coordinates `chi=chi_391(x), psi=psi_391(x)`,

`B^-x=chi I-psi D`.

Its required first row is therefore

`(chi+52500 psi, -29036 psi)`.

The entire new paid target source is

```
scaled11 = 52500 * psi;
target11 = chi + scaled11;
target12 = -29036 * psi.
```

All three operations and both supplied ports are live: two fixed-coefficient multiplications and one addition. The signed output entries are exactly the signed matrix interface used by the parent. No unpriced conversion to a positive-coordinate target is claimed.

The parent source computes two entries of `chi C-psi F`, with fixed `C=LR,F=LDR`, using four multiplications and two additions. Both full sources are saved and checked. For all scalar chi,psi, not just Pell values,

`L^-1 (chi C-psi F) R^-1 = chi I-psi D`.

The helper verifies the two complete coefficient matrices separately, so this is an all-value linear identity. The old and new coordinate outputs are in different target frames; they are not asserted to be identical scalar polynomials.

This is an upper bound for the displayed representation, not a three-gate minimum. Preparing fixed coefficients is part of the selected program's numeral recipe. The separate task of proving the supplied pair has **index x**, and the task of encoding an arbitrary-length product, are still absent. Renaming scaled Pell coordinates or moving linear equations inside a future membership predicate would have to be priced there. The full84 universal arithmetic frontier does not change.

## 4. A full fixed-context instance and its coefficient cost

The saved complete fixture uses

`U="[110", V="A0]"`.

At x=0 the original input word is `[110A0]`. Its inherited167-factor accepting product is checked after the full recoding and is exactly `diag(I,P)`, the new bare target for x=0, in all16 entries. For every natural x, the displayed middle block gives the finite valid configuration `[110 (W²)^x A0]`. The proof transfers its membership exactly; no claim about the whole acceptance set of this particular fixture is made.

Every one of the96 tile records and every rule, identifier, terminal and lower block is retained. Each original upper tile producer is reconstructed from the pinned letter matrices and tile text before changing it. All193 new matrices and all3,088 entries are saved. The changed upper coefficients are integers because all conjugating matrices have integral determinant-one inverses.

| Resource | Gamma1(5) parent | This fixed-context fixture |
| --- | ---: | ---: |
| Generators |193|193|
| Entry slots |3,088|3,088|
| Nonzero slots |1,543|1,543|
| Largest absolute entry |538,008,330|4,652,051,305,867,101,902,730|
| Largest magnitude bit length |30|72|
| Sum of magnitude bit lengths |23,832|53,734|
| Conditional target operations |6=4M+2A|3=2M+1A|

The smaller target operation count comes with larger fixed coefficients in this fixture. These are separate resources; no bit-complexity improvement is inferred.

## 5. Why simply keeping one linear row coordinate has no group proof

The unchanged group H' contains the actual letter matrices

```
J=Psi(J)=T^9=[[1,9],[0,1]],
A=Psi(A)=V²=[[-19,10],[-40,21]].
```

Thus `J^n=[[1,9n],[0,1]]` and

`A^r=[[1-20r,10r],[-40r,1+20r]]`.

Consider any fixed integer linear functional of the first row,

`ell(M)=p M11+q M12`.

If q=0, I and J have the same value. If q is nonzero, take

`r=9q, n=10q-20p`.

Then `ell(A^r)=ell(J^n)`, but the matrices are different because A^r has nonzero lower-left entry and J^n does not. Adding an affine constant or using rational coefficients changes nothing after clearing denominators. In particular neither of the two current varying entries alone is injective on H'. The other two individual matrix entries also coincide on I and J.

This is a complete obstruction only to those fixed linear projections **on this entire group in its current frame**. The collision elements are not claimed to be false accepted inputs or products with the required lower target. It does not exclude a nonlinear pairing with paid arithmetic, a separately certified restricted target family, or a different matrix basis with a different stabilizer theorem. Such an alternative needs its own exact membership proof; the existing whole-group row theorem cannot justify dropping another coordinate for free.

## 6. Fresh evidence, pins and replay

The helper authenticates the parent trio and three proof dependencies. It uses no predecessor imports or executable builders. Its finite checks comprise193 complete phase matrix identities;145 complete products in the forced shape; the genuine167-factor accepted product;28 all-value target checks including12 rational pairs;13 exact indexed literal-word targets; source closure/liveness and both complete paid ledgers; and seven illustrations of the general linear-collision formula. The unrestricted transfer and collision results are the proofs above, not inferences from those finite examples.

| Pinned file | SHA256 |
| --- | --- |
| `matrix193_gamma1_recode.py` |`ae24e64539b450fd9c4db0b3e04ce440d00562dcfe532a43002d7c52da34757c`|
| `matrix193_gamma1_recode.json` |`9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668`|
| `matrix193_gamma1_recode.md` |`6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742`|
| `matrix193_kernel_row_projection.md` |`400aab15caa9462808cc2dc2ef68f013797a9bc656c97acecdd610de81a13c6e`|
| `group_directed_semigroup193.md` |`75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e`|
| `u15_unary_block_interface.md` |`cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452`|

With the trio installed, from any directory:

```sh
python3 /absolute/path/matrix193_context_absorption.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/matrix193_context_absorption.json
python3 -O /absolute/path/matrix193_context_absorption.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/matrix193_context_absorption.json
```

The mutually exclusive `--output FILE` writes the deterministic receipt. JSON reads reject duplicate keys and nonfinite constants; checks remain active with optimized Python; saved comparison is recursive and type-exact. This is a bounded fixed-fixture CLI, not a maintained arbitrary-context compiler API. All predecessors remain unchanged.

Writer and fresh saved-receipt replays from `/`, normally and with `python3 -O`, passed on the final source and receipt. No archived code, predecessor helper, historical suite or arbitrary-program initialization compiler was executed.
