# A literal universal word table whose direct group interpretation collapses

Tseytin supplies an actual five-letter, nine-relation table with an undecidable fixed target. It cannot be substituted directly for the uninstantiated alphabet in the [group commutator route](group_commutator_universal_substrate.md): its universal group is trivial. The related seven-relation table has universal group the free group on two generators. These statements classify **all** group-valued interpretations of the respective tables, including invertible integer or rational matrices of any finite dimension.

This packet also implements the primary effective word reduction from a supplied finite group presentation into the nine-relation table. For the distinguished commutator inputs, a concrete choice of code has word length `|S|+20x+19`. Its raw base-eight integer value therefore cannot be computed by any fixed circuit using only additions, subtractions and multiplications on ordinary `x` and fixed program constants. This is a restriction on that literal loader, not on existential Diophantine encodings.

There is no new universal arithmetic count. In particular, the [244-operation product-scale illustration](group_projective_product_radix_scale.md) remains an illustration. The five generators and nine relations below are fully numerical; a paid unbounded rewrite history and a paid ordinary-input loader are still missing.

## 1. Exact primary presentation and input theorem

The primary source is G. S. Tseytin, *An associative calculus with an insoluble equivalence problem*, Trudy Mat. Inst. Steklov 52 (1958), 172–189. Its [English translation in the appendix of arXiv:2401.11757](https://arxiv.org/pdf/2401.11757) gives the literal tables in original §1(1)–(2), the program word in §3(11), the uniform word reduction in §6 Lemma 4, and the fixed-target reduction in §7 Lemma 9 and Theorem 2/Corollary 1. These are references to the translated original, not the preceding survey's section numbers.

On the alphabet `{a,b,c,d,e}`, let C1 have the seven symmetric relations

```
ac = ca       ad = da       bc = cb       bd = db
eca = ce      edb = de      cca = ccae.
```

The concrete fixed-target version C2 replaces the last relation and adds two more:

```
ac = ca       ad = da       bc = cb       bd = db
eca = ce      edb = de      cdca = cdcae
caaa = aaa    daaa = aaa.
```

Thus C1 has 33 defining-letter occurrences; C2 has 49. These count both sides, with repeated letters counted separately. They are presentation sizes, not arithmetic-operation counts.

Here is the exact effective interface supplied by the primary theorem. Present a group as a special monoid: use distinct symbols for each generator and its inverse, add both inverse-cancellation relations, and write each group relator as a word equal to the empty word. Denote the resulting special relators by `K1,...,Km`, and put `K0=empty`. Add fresh symbols `alpha,beta`, assign distinct nonnegative code integers with `n(alpha)=1`, `n(beta)=0`, and define

```
phi(z1...zk) = a b^n(z1) a b^n(z2) ... a b^n(zk) a,
S = twin(phi(alpha K0 alpha K1 alpha ... Km alpha)),
twin(a)=c, twin(b)=d.
```

For every original group word `P`, the primary result gives

```
P = 1 in the supplied group  iff  S phi(beta P beta) = aaa in C2.
```

The fixed C2 table is independent of the supplied group; `S` records that finite presentation. The checker implements this transformation, including the empty `K0` and both separator occurrences. The cited theorem proves its unrestricted converse; the finite checks below do not purport to reprove undecidability. When the source presentation comes from the existing commutator universality theorem, this gives a universal **word** substrate. It does not materialize the missing finite universal group presentation or turn `S phi(beta P beta)` into a paid scalar port.

## 2. Exact group completions

Let a homomorphism from C1 to an arbitrary group send its letters to `A,B,C,D,E`. Cancellation in `CCA=CCAE` gives `E=1`. Then `ECA=CE` gives `A=1`, and `EDB=DE` gives `B=1`. The four commuting relations impose no further restriction: `C,D` are arbitrary. Consequently the universal group of C1 is exactly `F(c,d)`.

For C2, cancel the nonempty common prefix in `CDCA=CDCAE` to get `E=1` again. The next two cancellations give `A=B=1`. Finally `CAAA=AAA` and `DAAA=AAA` force `C=D=1`. Hence the universal group of C2 is trivial.

The converse directions here matter. Sending `a,b,e` to the identity and `c,d` to arbitrary elements satisfies every C1 relation. Sending all five letters to the identity satisfies every C2 relation. Thus the arguments identify the entire presented groups, rather than merely finding quotients.

The source records exact Tietze certificates: after each previously justified generator erasure, a retained defining relator freely reduces to a conjugate of the next generator or its inverse. Replacing that relator by the generator and substituting the identity is reversible as a presentation move. Eliminating `e,a,b` leaves no relators on `c,d`; eliminating `e,a,b,c,d` in C2 leaves the empty presentation.

These group interpretations lose actual semigroup distinctions. The words `a` and `aa` contain neither side of any relation in either table, so each is an isolated vertex of the symmetric rewrite graph. They are distinct semigroup elements, although both have identity image in every group interpretation. In C2, `b` is likewise isolated and cannot equal the target `aaa`. Nevertheless every group interpretation sends both to the identity. Therefore replacing C2 word equivalence by equality of the corresponding invertible matrix products accepts every input word, including this explicit false target instance.

This rules out a direct homomorphic substitution of these tables into the physical invertible-shear alphabet. It does not rule out an HNN/Borisov construction, Mihailova subgroup membership, a constrained product language, or a separately paid rewrite-history relation. Those mechanisms add structure beyond a direct representation of C2.

## 3. The ordinary-input loader has a separate size obstruction

Use the local commutator convention

```
a_x = b^(-x) a b^x,
r_x = a_x a a_x^(-1) a^(-1),     x>=1.
```

Its freely reduced length is `4x+4`. Choose code integers

```
n(a)=2, n(b)=3, n(a^(-1))=4, n(b^(-1))=5,
n(alpha)=1, n(beta)=0,
```

and assign any remaining signed source generators distinct integers at least 6. These choices are compatible with the primary reduction, whose source presentation is fixed independently of `x`. The two occurrences of each `b` direction contribute `20x` letters to the code; the four `a`-direction occurrences contribute 16, the two `beta` occurrences contribute 2, and the closing `a` contributes 1. Therefore

```
|phi(beta r_x beta)| = 20x+19,
|S phi(beta r_x beta)| = |S|+20x+19.
```

Encode the five output letters by base-eight digits `a=1,...,e=5`, with the leftmost letter most significant. Every word `w` of length `L` then satisfies

```
8^(L-1) <= code8(w) < 8^L.
```

In particular the literal query integer grows at least as `8^(|S|+20x+18)`. A fixed straight-line circuit over integer constants and `x`, using only `+,-,*`, computes a polynomial in `x` by induction over its gates. Every such polynomial has at most polynomial growth on the positive integers, so it cannot equal this query integer for all positive `x`. Allowing finitely many fixed program constants does not change that argument. Nor does a fixed positive affine change of the ordinary input remove the exponential growth.

This obstruction concerns an auxiliary-free, fixed-length circuit outputting the **raw base-eight query word**. It supplies no lower bound for a circuit with existential witnesses and paid power/bit relations, a compressed word representation, or a different language reduction. In particular it does not establish an arithmetic lower bound for the abstract group route. The existing small polynomial matrix loader exploits unipotent powers; it is not a raw positional encoding of this semigroup word.

## 4. What the checker verifies, and the resulting next step

The [source](tseytin_group_completion_obstruction.py) and [receipt](tseytin_group_completion_obstruction.json) store the literal tables, all eight Tietze elimination steps, and two complete transformed example query words. The source exposes `group_to_fixed_target(rank, group_relators, word)`; signed integers represent the source group letters. Its correctness as a language reduction uses the primary theorem stated above.

Author writer and fresh replay pass. Exact finite checks comprise:

- 7,776 assignments of the five generators to S3 for each table, with exactly 36 C1 solutions and one C2 solution, matching the complete group classification;
- 11,111 signed-word normalizations in the C1 free quotient;
- 10 isolated-word checks, plus 511 actual C2 accepted words with 3,586 verified local rewrite steps;
- 288 independently decoded word/length/base-eight-size checks over three source ranks, three finite presentations and 32 positive inputs.

The S3 and word checks are supplementary finite audits. The all-group statement is the cancellation/Tietze proof, and the no-fixed-circuit statement is the polynomial-growth proof. The receipt explicitly sets its arithmetic-operation bound to `null`; it is not a disguised fixed-horizon or fixed-arity certificate.

Independent full proof/source/primary-translation review and two further
fresh replays pass without findings. A separate checker validates all eight
Tietze eliminations in a different C2 order,32,768 assignments per table
in the dihedral group of order8 (64 C1 solutions and one C2 solution),
240 independently assembled primary query maps,128 independently rebuilt
commutator encodings and ten isolated-word certificates. All four local
links pass. These checks retain the theorem and loader scopes above.

This resolves the tempting small-table shortcut: C2 is a genuine fixed universal word table, but directly interpreting its relations in the current matrix group destroys its accepted language. The actionable remaining alternative is to compile C2's nine symmetric rewrites together with a paid compressed or existential ordinary-input loader. Until that complete interface is emitted and proved, neither the table's 49 letters nor the group illustration's 244 operations is a universal polynomial bound.
