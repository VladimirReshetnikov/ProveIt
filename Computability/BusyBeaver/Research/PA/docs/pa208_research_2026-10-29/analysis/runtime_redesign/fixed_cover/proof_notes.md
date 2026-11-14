# Fixed-role cover with early vacuity gate

This construction changes the numerical axiom family while retaining its
PA consistency calibration. It preserves the seven logical rows, dominated
propositional row, truth, modus ponens, generalization, scheduler, direct
transfer command, and AX stack arity.

## Exact formula and exceptional matrix codes

Write I,Q,R for the native implication, universal quantifier and membership
constructors, F=1, and N(x)=I(x,1). Code0 is the closed truth alias.

For arbitrary a,b,c let

    V(a,b,c) = I(R(a,b), Q(c,R(a,b)))
    Vg(a,b,c) = 0 if c=a or c=b, else V(a,b,c).

For matrix/output code n set

    E(n) = R(1,n)
    G(n) = Q(n,I(R(n,1),R(n,0)))
    U(n) = Q(1,I(E(n),n))
    L(n) = Q(1,I(n,I(G(n),E(n))))
    H(n) = Q(n,I(U(n),N(L(n))))
    Bnew(a,b,c) = N(I(Vg(a,b,c),H(a))).

The source/test labels of the cover are fixed at0 and1. The output-dependent
binder n in G is ESSENTIAL for the safe n=0 case. A fixed independent binder
in G would instead make n=0 demand a set containing itself and is unsound
under IR.

Under the normalized native decoder in W+IR, Bnew is equivalent to
Vg AND NOT H. Vg is a membership-vacuity axiom or truth, hence sound.

For n>=2, every effective variable label in the matrix is below n, so the
output binder is fresh and distinct from source0 and test1. The guard is
Sub(v1,v0) and NOT H is a W cover instance.

For n=0, the matrix is closed truth. The local guard binder0 captures its
own source occurrence and G becomes Emp(v1) under IR. U is true and L says
that every empty representative belongs to the output v0. NOT H therefore
asks for an object containing all empty representatives. W supplies this
by first producing an empty source and then taking its true-matrix cover.
No extensionality or unique empty representative is used.

For n=1, the matrix is false under IR and the output/test labels coincide.
U becomes IR, L is true, and the outer output quantifier is vacuous in
those closed clauses. Thus NOT H is equivalent to IR and is sound.

## Completeness and PA-internal calibration

Every ordinary fresh atomic membership-vacuity instance V(a,b,c) is still
available by projecting Bnew at its own fresh triple. Thus the retained
pure-logic and equality-indiscernibility proof templates have unchanged
premises; no circular appeal to a restricted renaming principle is needed.

For a desired unrestricted W instance, perform the retained fresh-variable
normalization and double-negation padding to obtain matrix code n>1 and
source/test names0,1. The emitted triple (a,b,c)=(n,0,1) supplies the required
cover. The ordinary logical templates remove the padding and restore names.
The earlier native derivation of IR is unchanged. Conversely every new
bundle is sound in W+IR by the preceding cases. These finite syntax
translations are primitive recursive and PA-verifiable in the same sense
as the inherited calibration.

Hence numerical derivability of target1 in the new calculus is equivalent,
provably in PA, to inconsistency of W+IR, U, and PA. This is an ordinary
mathematical proof; no new kernel certificate is claimed.

## Register conventions and earlier gate

Registers are 0=N (candidate),1=T (top),2=W (stack),3=c,4=a,5=b/H,
6=X,7=Y,8=L (remaining proof word). The constructor macros require X=Y=0.
The new block starts at source ordinal2642 with T=old_top and arbitrary
stack J, candidate N, proof word L, and selectors a,b,c.

First construct V, leaving stack [old_top;J]. Move the unchanged five-call
gate ahead of the cover, modifying only its a-transfer:

1. w192 moves c to X and Y and clears c.
2. ifeq131 clears T exactly when X=b; clears X,b.
3. w211 moves Y to X and clears Y.
4. Duplicate a into b/H and Y, clearing a.
5. ifeq131 clears T exactly when X=b/H; clears X,b/H.
6. Move Y back to a.

At exit T=Vg, a is preserved, c=b/H=X=Y=0. The replacement at step4 is
`(CD4,((CI5,CI7),CC2))` (4 primitive occurrences); restoration is
`(CD7,(CI4,CC2))` (3). They replace a three-primitive move, so the early
gate costs38 rather than34 primitive occurrences. Each loop has a direct
all-natural induction proof. The symbolic audit records both comparisons.

## Variant fixed31

Replace every c-load in the old cover word by v177 (push old top and load1),
and its single b-load by pushwff171 (push old top and load0). The eight
matrix/output a-loads remain ordinary par166. This computes exactly H(a).
It uses737 rather than774 primitive occurrences: five replacements save6
each, and one saves7. Combine Vg and H with the unchanged I and N macros,
then clear a with `(CD4,CC1)`.

The entire old V/cover/combine/gate interval [2642,3766), length1124, is
replaced by1093 primitives. The new source has3878 primitive occurrences.
It leaves T=Bnew, stack [old_top;J], all selector and scratch registers zero,
and N,L unchanged.

## Variant cached67

After the earlier gate, b/H is dead and zero. Compute E=R(1,a) once using
v177;par166;wel181, costing74 primitives. This pushes Vg on the stack.
Move T into H using `(CD1,(CI5,CC2))`, costing3. Copy a into zero T while
preserving a using a four-primitive duplicate a→T+X and three-primitive
restoration X→a, costing7.

Evaluate the postfix constructor word for H(a), with its first a-load
omitted (a is already in T), and with both E subexpressions replaced by
par121 loads from H. This word costs615 primitives. It finishes at H(a)
with Vg at the top of the stack. Combine by the unchanged I,N pair and
clear both H and a (four primitives total).

The replacement costs1057 primitives, saving67; the source has3842
primitive occurrences. Its symbolic output and stack/register interface
are exactly the same as fixed31.

## Source and proof-search interface

The replacement acts in a closed arithmetic region. To preserve all
surrounding lexical control depths, the builder re-associates only the
closed factors inside source subtree001100111 (old ordinals158..3767),
retaining its final CB1. Both independent CFG resolvers agree, and every
external primitive operation and resolved successor matches the old one
under the ordinal shift. The source rows through ordinal136, including
the exact blank-start bridge frame, are unchanged.

AX still pushes its same ten explicit theorem heads: seven logical rows,
the dominated row, a generalized incoming cache, and the saved incoming
top. Its new top is always an implication code, hence not target1. Its
counter and cache reset and stack layout are unchanged. In particular,
all PUSH/H/DISCARD compiler macros initially discard AX's newly generated
top by direct transfer from cache0, so they do not require the disabled
bundle to be numerically0. Generalization's AX top is also discarded before
the quantified saved cache is selected. Bundle-selection simply selects
Bnew instead of the old family.

The interior startup suffix still yields nine explicit theorem heads above
opaque tail4, with candidate1 and cleared counter/cache. Its final top is
now the sound Bnew(0,2,0), rather than truth0. The protected-credit argument
uses theoremhood of this top, not its being literally0; its margin remains
seven. Strong completeness and cofinal successful candidates retain their
proof, with Bnew as the nonlogical axiom family and the unchanged stack
arities.

The literal physical table and its full arbitrary-value primitive
simulation must be separately compiled and checked. Fewer source
primitives alone do not establish a smaller TM state count.

## Improved selector-c variants

The cover matrix/output selector can instead be c. In the early gate,
replace the move Y→X by a duplicate Y→X+c (four primitives instead of
three). The first comparison has already cleared X and c, so this is a
valid duplicate; it restores the original c. Leave the original move
a→H and second comparison unchanged. At gate exit T=Vg, c is preserved,
and a=H=X=Y=0. This gate costs35 rather than34 primitive occurrences.

Use c-loads for the eight matrix/output loads and the same literal source0
and test1 loads. Clearing c at the end yields fixed_c34: saving34 source
primitives, for3875 total. The cached variant computes E=R(1,c), uses the
dead H register as above, and copies c into T with the existing c→T+X
and X→c loops. It yields cached_c70: saving70 primitives, for3839 total.
Both emit N(I(Vg(a,b,c),H(c))). Completeness uses triples (0,0,n), n>1,
whose gate is enabled. Every atomic vacuity instance remains available
by projecting its own emitted bundle. All soundness cases depend only
on n and are unchanged. The blank-start suffix has c=0 and is still sound.

After closed-factor reassociation, fixed_c34 has211 distinct source
nodes; cached_c70 has212. Both have depth34 and maximum zero run6, and
preserve all137 initial source rows exactly. The baseline has197 distinct
source nodes. Thus these arithmetic savings currently do not establish
any physical-state saving.

## Simpler unchanged-gate variants

Caching is unnecessary in the direct fixed-role emitter. Keep V, the
combining pair I,N, and the original gate exactly in their original order.
Replace only the cover word's five test-selector loads by literal1 loads
and its single source-selector load by a literal0 load. No extra cleanup
or gate changes are then needed. The saving is exactly37 primitives,
giving3872 total. Its emitted family is

    Bafter(a,b,c) = 0 if c=a or c=b,
                   otherwise N(I(V(a,b,c),H(a))).

Every enabled instance is sound by the same H(n) case analysis. Every
atomic vacuity instance is retained by projection, and every normalized
cover with matrix n>1 is available at (n,0,1). Disabled triples still
emit literal truth0, so the inherited startup and source-transfer
contracts retain even that exact numerical value.

The alternative variants fixed_c_after37 and fixed_b_after37 simply load
c or b at the eight matrix/output positions, still with the original
gate. Their cover-completeness triples are respectively (0,0,n) and
(0,n,1), n>1. Their primitive savings and all soundness arguments are the
same. They are supplied to explore the effect of exact old-DAG sharing.

## Best fixed-role grammar obtained

Two independent implicational exchanges are valid in the retained common
logical core:

    n → (G → E)   is equivalent to   G → (n → E),
    U → (L → F)   is equivalent to   L → (U → F).

The best completed fixed-role source uses both exchanges. Define

    L'(n) = Q(1,I(G(n),I(n,E(n))))
    H'(n) = Q(n,I(L'(n),I(U(n),F))).

With the unchanged original gate, its enabled bundle is N(I(V,H'(a))).
The exact constructor output is audited, and the two exchanges give the
same W cover under the inherited logical proof templates. The small-code
soundness and the atomic-vacuity projection are unchanged.

The artifact is `fixed_a_o1l1_37_optimized.sites.json`, SHA256
`0e5de91054a2cff50711c747a6d72ec02a2046a388ae14c4f5f0f3e6c725a0a8`.
It has3872 primitive occurrences,203 distinct source DAG nodes, depth34,
and maximum zero run6. It preserves all137 initial source rows. These
metrics remain above the baseline197-node source.

Further fixed-role experiments specialized constant membership and
quantifier operands by direct Cantor arithmetic, and used direct18
negation. They save271 primitive occurrences but produced at best210
source nodes under the tested grammar optimization. These experiments
support no physical-state improvement claim. Their arithmetic components
are proved in the sibling direct_negation/proof_notes.md.
