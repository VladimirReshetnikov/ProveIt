# Ordinary source/enumerator binding for equality-weakened frontends

## Result, exact scope, and reproduction

For each source listed in `binding_results.json`, the abstract register program,
started at the genuine root with clean selector/scratches and safe theorem
fields, halts exactly when its **specified native numerical calculus derives
code 1**. The proof below is uniform in natural-number parameters, proof lengths,
and register values. It covers GEN, MP, all row positions, gate failures, changed
AX parser arity, and cofinal candidate search. It is an ordinary mathematical
proof, with independently checked finite source identifications.

The surgical sources implement H_eq or its separately calibrated H_kappa
generalization. The canonical-V sources implement H_sym or H_7, as defined by the equality-calibration audit. Their exact row/bundle
calculi are identified below. Combining this result with that separately audited
ordinary equality interpretation establishes the ordinary source-to-ZFC bridge.
It does **not** by itself establish any binary-table, startup, state-count,
new Lean/Rocq, or internal PA theorem.

Run, from the workspace root:

    python -O research_sub236/enumerator_binding/check_binding.py

The checker uses only the Python standard library. It imports no optimizer,
emitter, upstream source checker, or reported certificate. It parses the pinned
219-node `Dag254.v` as data, builds a reference program with the specific changed
AX word, and compares its entire resolved control graph with each saved source.
It checks arithmetic operations, both decrement outcomes, escaping exits,
source entry, the unique halt, and all source leaves. It permits only explicitly
proved, no-interior-entry increment commutations and the terminating loop
identity in section 8. Formula checks are structural equalities, modulo the
explicit negative-conjunction associativity/commutativity stated below.

`binding_results.json` pins every input by SHA-256, records the exact AX read
fields and emission order, and gives a digest of its normalized complete graph.
The finite source check is an input-binding proof, not an experimental execution
of the enumerator. Four negative controls are rejected. Independent algebraic
reviews checked the block lengths and cofinal x-padding in sections 4--5 and
found no gap. All checks remain active under Python `-O`.

No new proof-assistant declaration is supplied or claimed. Existing checked
macro/provider theorems are reused mathematically as precisely identified in
section 9; their whole dependency closure was not rebuilt for this audit.

## 1. Parameterized native calculus and AX interface

Use the original natural codes, without replacing their arithmetic:

    P(x,y) = (x+y)(x+y+1)/2 + y
    I(x,y) = 4 P(x,y); R(x,y) = 4 P(x,y)+1
    A(i,x) = 4 P(i,x)+2; E(i,j) = 4 P(i,j)+3
    F = 1; N(x)=I(x,1); C(x,y)=N(I(x,N(y)))
    Ex(i,x)=N(A(i,N(x))).

Fix m >= 1. Let Q(a,h,b,c,u) be a top-first list of exactly m codes. In the
candidates it is the reverse of the saved AX emission order, and its last member
is A(a,h), the GEN row. Every other member is independent of h, and Q depends on
u only for H_eq. Let B(a,b,c) be the exact emitted negative-conjunction bundle.
Define gate G(a,b,c) to be 0 when c=a or c=b and B(a,b,c) otherwise.

Let D be the least numerical derivability relation containing:

1. 0 (the native truth code);
2. each non-GEN member of Q(a,0,b,c,u), for all natural parameters;
3. B(a,b,c), whenever c != a and c != b;
4. closure under MP: D(x), D(I(x,y)) imply D(y);
5. closure under theorem GEN: D(h) implies D(A(a,h)).

There are no undischarged assumptions in this definition. It is the numerical
proof relation supplied to the enumeration theorem. It does not admit arbitrary
formulas merely because a field can hold an arbitrary number.

Let push(L,S) prepend a top-first finite list to the infinite-zero-tail Cantor
stack S. The exact AX transition on working fields (t,S,d,h) is

    a=d+x; b=h+y
    (t,S,d,h) -> (G(a,b,c), push(Q(a,h,b,c,u) ++ [t],S), 0,0).

For H_sym and H_7, omit u throughout, or equivalently specialize Q's unused u
argument to 0 without reading a field. This distinction is essential.

For all candidate parameters, G != 1, and every member of Q != 1. An implication
code is divisible by 4, and a universal code is 2 modulo 4. Every non-GEN row has
an outer implication, including rho1's relative existential, K, S, symmetry,
and positive V. Every bundle also has an outer implication. A gated zero is
not 1. These are arithmetic facts for **all** codes, including 0.

## 2. Exact candidate row and parser bindings

Emission order is oldest-to-newest. The stack has the reverse order.

### H_eq: surgical restriction

Both `restricted_eq_exact236/minimal_existing_builder/source.json` and
`restricted_eq_exact236/local_closed_rotation/source.json` emit:

    GEN, rho8, rho7, rho6, rho5, rho4, rho3, rho2, rho1.

Thus m=9, GEN is stack position 9, and complete AX cleanup uses 10 NIPs.
The parser still reads y and then u. The original logical rows are unchanged.
The bundle is literally

    C(C(CP(a,b,c), GIC(a,b,c)), C(RelVac(a,b,c), EqHelper(a,b))),

where EqHelper(a,b)=I(E(a,b), A(E(a,b),E(a,b))). The scalar binder of its A
is the actual native integer E(a,b)=weq(a,b), not the formula c and not a
separately selectable fresh variable. The checker constructs this reference
by replacing the unique old Eq-vacuity subword's c-push with the Eq(a,b) builder,
then checks the **whole** source graph. The independent symbolic evaluation
checks that this is the sole formula change in the entire AX output.

The rotation and the backend `restricted_z8/source.json` and
`restricted_local_rotation_z7/source.json` independently match this same reference. They need no inherited whole-program hash implication.

### H_sym: positive canonical V and primitive symmetry

`symmetry_canonical_warm/source.json` emits, in its exact saved order:

    GEN, rho5, rho4, symmetry, S, rho6, K, V, rho3, rho2, rho1.

The canonical V row is a separate positive I(a,A(a,a)), at emission index 7
(zero-based, with GEN at index 0). It is not in the negative bundle and is not
gated. Here m=11, GEN is stack position 11, and complete AX cleanup uses 12 NIPs.
The parser reads only y after the selector and x. There is **no u read**.

The independently checked bundle has exactly CP, GIC and full RelVac as its
outer conjunction components, with the saved conjunction rearrangements.
`alternate_backend/symmetry_canonical_warm_repair_z8/source.json` implements the
same contract after the five closed loop replacements and exact reassociation.

### H_7: positive canonical V and retained rho7

`omit_equality_deep/source.json` emits:

    GEN, rho5, V, rho7, S, rho6, K, rho4, rho3, rho2, rho1.

Again m=11 and only y is read. V is the separate positive row at emission index 2.
The outer bundle components are CP, GIC and full RelVac. The backend transplanted
source has the same contract after the five closed loop replacements.

### H_kappa: alternate literal auxiliary builders

All 16 saved sources under `vacuity_reduction/kappa_exact236/` are also bound
independently. Their exact helper is

    I(E(a,b), A(kappa(a,b), E(a,b))),

where kappa is one of I,R,A,E applied to (a,b) or (b,a), as recorded separately
for each source. No interpretation of a formula as a binder is implicit: the
builder's integer result is the literal universal-label field. These variants
retain m=9, every original rho1--rho8 row, both y/u reads, CP/GIC/RelVac, and the
same gate. For each source the checker constructs a fresh reference AX word for
its declared builder, checks the whole word's symbolic formula, and compares
all actual source operations/guards against that reference. Saved backend
`kappa_rel_ba_0` and `kappa_imp_ba_0` sources are included when present.

The ordinary enumeration theorem needs no freshness assumption on kappa at all;
it identifies the exact helper actually enumerated. The additional logical
calibration is supplied by `general_kappa_equality_helper.md`: it suffices that
kappa(a,b) differs from a,b when a!=b, with no condition on the diagonal. This
includes the literal I(0,0)=0 diagonal case. The source checker establishes no
freshness fact merely from a candidate's metadata string.

### Parameter permutations and conjunction rearrangements

The saved rows use different permutations of a,b,c. The checker matches each row
against exactly one independent standard schema under a bijection of these three
parameters and checks that every required schema occurs once. For any requested
schema instance, choose the inverse permutation of its parameters. Because leaf
construction resets h=d=0 before AX, x and y can be any required nonnegative a,b;
selector c is independently encoded. No unwanted restriction a!=b is present.

Only conjunction reassociation/commutation, including under unchanged formula
contexts, is accepted for CP/GIC. Negative conjunction here is literal
N(I(P,N(Q))). Once classicality is available it has both implications for every
such reassociation/commutation. MP/GEN and rho2 lift these implications through
quantifiers; implicational contexts use classical propositional congruence.
The standard CP/GIC instances are therefore interderivable with the emitted
ones, with all variable labels and the actual matrix/output scalar c unchanged.
No general renaming, substitution, matrix replacement, or new freshness premise
is hidden in this comparison.

## 3. Command semantics, soundness, and the falsehood test

Non-AX command effects are unchanged, with p=d+x:

- MP x: if I(t,p)=h, set (t,S,d,h)=(p,P(0,S),p,0); otherwise (0,S,p,0).
- DROP x: set (t,S,d,h)=(h,P(t,S),p,h).
- NIP x: halt if h=1; otherwise set (t,S,d,h)=(t,unP(S).2,p,unP(S).1).

The parameterized invariant is

    D(t), D(h), and D(unP(tail^k(S)).1) for every k.

The zero stack is an infinite stream of truth code 0 because unP(0)=(0,0).
MP success uses D(h) plus the exact tested equation h=I(t,p). MP failure puts
truth 0 in t. DROP copies an existing theorem. A nonhalting NIP retrieves a
proved stack member. AX pushes the old theorem t, GEN of the existing theorem h,
and the specified axiom rows; its current G is an axiom or truth. Thus every
nonhalting step preserves the invariant. A halting NIP has cached h=1, so its
invariant gives D(1). This proves soundness from every safe starting state.

This argument explicitly includes the code-zero collision I(0,0)=0. Successful
MP with h=0 can only have t=p=0 (P(x,y)=0 iff x=y=0), and produces truth 0.
The definition of D already includes the native MP rule, so no syntactic
inverse-decoder assertion is required for the invariant.

## 4. Uniform proof-to-command compilation, including GEN

A block contract for a code z says: from every (T,S,0,0), the finite block either
halts, or returns (z,S,0,0). Early halt is allowed because it already establishes
the desired refutation search result. All lists below are finite.

Write NIP^k for k copies of NIP 0. Each AX below has a zero u field exactly when
its source actually reads u. In the three-field variants no u field is encoded.

### Truth/discard block

    MP 1; AX(c=1,x=0,y=0[,u=0]); NIP^(m+1).

The first MP must fail since I(T,1)>0 while h=0. It sets t=0,d=1,h=0 without
changing S. The AX has a=1,b=0,c=1 and hence current G=0, pushes Q++[0], and
resets d=h=0. Its m rows and final zero can all be popped safely, leaving exactly
(0,S,0,0). This proves the truth contract without assuming any initial T is a
theorem and without assuming the old row count 9.

### Any axiom row, including positive V

Let row z occupy top-first position j, with 1 <= j <= m. Run discard, then
AX with the desired a,b,c,u, then

    NIP^j; DROP 0; NIP^(m+2-j).

The first group loads row z into h. DROP sets t=z and pushes the old current
G. The last group pops that G, all remaining rows, and the saved 0. Every
popped current/cache entry is !=1 by section 1. The result is (z,S,0,0).
This selects any row independently of whether the bundle gate passed.
In particular K/S/positive V and rho1--rho6 are available before projecting
anything out of the negative bundle.

### Bundle

After discard, AX at desired a,b,c with c!=a,b followed by NIP^(m+1) returns
(B(a,b,c),S,0,0). This gives every gated bundle and no ungated one.

### GEN

Suppose p contracts to H. After p, run

    DROP 0; NIP 0; AX(c=i,x=i,y=0[,u=0]);
    NIP^m; DROP 0; NIP 0; NIP 0.

The first DROP/NIP sequence changes (H,S,0,0) to (0,S,0,H). It does not check
H as the cache before setting it, so H=1 is also allowed. AX now has a=i,b=H,
c=i, so G=0, and its bottom row is **A(i,H)** built from the old cache before
read_b. After m NIPs the cache holds that row; the final DROP and two NIPs
restore stack S and cache0 while making A(i,H) current. All other rows and G
are !=1. This establishes theorem GEN for every i and H, including i=0/H=0.
It does not generalize a hypothesis or presume arbitrary assumptions are true.

### MP

If pa contracts to U and pab to I(U,V), use the unchanged pattern with the
parameterized cleanup length:

    pa; DROP 0; pab; NIP 0; DROP 0; NIP 0;
    MP V; AX(c=V,x=0,y=0[,u=0]);
    NIP^(m+1); DROP 0; NIP 0; NIP 0.

After the first blocks, U has been saved below the result I(U,V). The next
NIP/DROP/NIP places U in t and I(U,V) in h, restoring S; if a NIP sees U=1,
the block has already halted. Otherwise MP V succeeds, leaving
(V,P(0,S),V,0). AX with c=a=V gates to0, saves V below its m rows, and resets
d,h. After m+1 NIPs, h=V and the extra P(0,S) remains. DROP and two NIPs
return (V,S,0,0), unless V=1 causes the allowed early halt. Thus MP works for
all natural conclusions, including zero and the target1.

Induction on the finite D derivation now produces a contract for every derived
code. This is a constructive finite proof compilation, independent of ordinary
semantic completeness and independent of the eventual sizes of native codes.

## 5. Exact serialization and fair cofinal enumeration

Commands MP/DROP/NIP are serialized identically in all variants:

    pack(MP x,r)=P(0,P(x,r)); pack(DROP x,r)=P(1,P(x,r));
    pack(NIP x,r)=P(2,P(x,r)).

The AX serialization depends on the **actual read count**:

    H_eq/H_kappa: pack(AX(c,x,y,u),r)=P(c+3,P(x,P(y,P(u,r))))
    H_sym/H_7:  pack(AX(c,x,y),r)=P(c+3,P(x,P(y,r))).

For a nonempty list, pack its last command with rest0; every earlier command
gets rest=(encoded remaining nonempty list)+1. The unchanged scheduler fetches
(np,np+1) when pl=0, and (pl-1,np) otherwise, then decodes selector and x and the
correct number of extra AX fields. The identity unP(P(x,y))=(x,y) proves direct
execution of each packed list by induction. A frozen old pack/execAt theorem
would be wrong for the K/S/V sources because it would consume one extra field.

During an unfinished candidate, every surviving command replaces pl>0 by a
component obtained by finitely many unpairings of pl-1. Pair components are
<= their input, so the new pl is strictly smaller than the old pl. This is true
with either AX arity. Thus a candidate drains in finitely many steps or halts.
Starting a new candidate increments np by1. Induction on the candidate number
shows every later natural candidate is reached unless an earlier command halts.
An initial pl need not be0: drain it first.

For D(1), let p be its block contract. Prepend a reset AX and append

    DROP 0; NIP 0; NIP 0.

Every AX resets d=h=0 regardless of dirty inputs, so p either halts or returns
current1 with its incoming stack preserved. The three-command suffix then
halts. This word works from **every** working state.

Cofinal padding remains available after deleting u. Given any initial candidate
cutoff N, choose the first reset as

    AX(c=0,x=N+1,y=1[,u=0]).

Its encoded number is >=N+1 because each argument is <= its Cantor pair.
Its reset contract does not require any fixed a,b, gate result, old cache, or
particular emitted rows. The compiled p accepts arbitrary current/stack once
its d=h fields are0. Consequently a refutation word lies above every cutoff,
with either parser arity. This replaces the old proof's unused-u padding trick;
there is no need to put a deleted fourth field back into the source.

Combining sections 3--5 gives, for every safe six-field state s,

    HaltsFrom(s) iff D(1).

Completeness alone is valid even for unsafe formula/stack fields. Soundness
requires the stated invariant and must not be inferred from arbitrary dirty
registers. In particular the safe logical seed represented by

    [N,T,W,A,D,H,X,Y,L] = [3,0,0,0,3,0,0,0,0]

is covered: selector/scratches are0 and all theorem fields are truth0.
The candidate startup check must separately identify this exact seed frame.

## 6. Gate completeness and the audited equality interpretation

The native bundle is gated solely by c!=a and c!=b. That gate never suppresses
GEN or a separately pushed logical row. After the derived classical basis:

- RelVac(a,b,c) is projected for every c!=a,b, exactly the audited family.
- H_eq's EqHelper(a,b) is obtained by choosing c=E(a,b), which is larger than
  both a,b. No requirement a!=b is introduced. The helper remains the same
  for any permissible dummy c and does not depend on that dummy.
- For H_kappa, choose dummy c=max(a,b)+1 to project its helper. This works
  even when the diagonal auxiliary equals a or b, including kappa(0,0)=0.
- CP(2,3,1) is available since 1 differs from2,3.
- For the equality-free GIC matrices in the audited interpretation, choose
  a=1,b=3,c=enc(p), where p is the exact padded named matrix. The audited
  code inequality c>3 supplies both gates. The actual matrix code and output
  binder stay coupled to this same c.

The H_sym/H_7 positive V leaves are selected directly by section4. K/S plus
positive canonical V and the retained rows yield the audited classical bridge
before bundle projection. H_eq retains original rho8 and rho6, so classicality
is inherited without general V. Thus there is no circular extraction of
classicality from a merely double-negated or gated V component.

The separate files `membership_defined_equality_calibration.md` ,
`general_kappa_equality_helper.md`, and
`research_sub236/equality_calibration_audit/AUDIT.md` give the uniform
membership-defined equality interpretation, binder-collision treatment, and
CP/GIC-to-ZF-to-ZFC comparison. This source audit establishes its demanded
supply of numerical rows and inference rules. It does not substitute finite
AX stack checks for that logical comparison.

## 7. Native code0, finite formula coding, and interpretation scope

The numerical enumerator never changes code representations: it uses I,R,A,E,
MP's exact integer equality, and target1 throughout. Native dec(0) is the
identity F->F, whereas encoding that displayed finite tree is16. We do not
assert enc(dec(n))=n, nor syntactic freshness of the raw free label0 in dec(0).

For native-to-model soundness, the code0 implication collision is handled by
its truth semantics; the existing `sat_wim` law has a separate x=y=0 case.
Canonical V(0) is true because dec(0) is true, including after assignment
update at0. For positive n, the independent code-label bound proves its
canonical binder n is fresh. H_eq's binder E(a,b)>a,b also includes a=b=0.

For transporting the comparison calculus into a native proof, use encodings
of finite formulas, whose encodings are positive, and the constructors'
homomorphism equations. It is unnecessary to recode arbitrary decoded machine
values. The audited interpretation preserves every equality-free selected
CP/GIC matrix literally and uses its actual code. Thus the ordinary consistency
comparison and the numerical D(1) endpoint coincide in the required directions.
No claim of a PA-internal proof-code equivalence is being made.

## 8. Ordinary program-identification proof

### Resolved path graphs

The checker expands the saved source into its ordered instruction leaves. At an
increment the next instruction is the next leaf. A successful decrement decrements
its register and takes that same successor; a zero decrement breaks one enclosing
left branch. A break k exits k enclosing left branches; continue k restarts at the
ancestor reached by k enclosing right branches. If an exit escapes the subtree,
its kind and remaining depth are retained. Normal root exit is recorded explicitly.
This is the ordinary RegisterPath/RMDag control semantics.

Equality of these resolved graphs gives a bisimulation on corresponding leaf
indices and identical natural register files. No field is sampled. Changed jump
spellings are irrelevant only when the checker has resolved their destinations
to the exact same indices or external exits.

### Straight-line increment commutation

Between branches, a finite sequence of increments contributes its register-count
vector and always terminates. Sorting these increments is permitted only within
a maximal run where every interior instruction has its immediately preceding
instruction as its **sole** incoming predecessor. The checker also verifies each
preceding edge is the single straight-line successor. Therefore no branch or root
entry can observe an intermediate order. The two runs reach the same final full
register file, and external entry/exit behavior agrees. This is a finite-block
simulation, not equality of intermediate instruction configurations.

This independently accounts for the increment reordering between original203
and the proved 219-node library; no old whole-program source hash theorem is
silently transplanted to a changed emitter.

### Five closed pretest/posttest replacements

For i!=j, the source-tree identity is

    ((D j,(I i,C2)),I i)  ~  (I i,(D j,C2)).

Both are closed: they have no escaping break, continue, or halt. With register
j=n, the left executes n decrement/increment rounds and a final increment.
The right executes an initial increment and then n decrement rounds each
returning to that increment, and finally exits on the zero test. Induction on
n gives termination in both cases, j=0, and i increased by n+1; every other
register is unchanged. The inequality i!=j is essential and is checked at every
rewrite. Their source instruction graphs are not asserted equal.

The pinned236 baseline and each transplanted alternate have five such
occurrences: one increments register0 and four increment register5, each
consuming register6. Both start and finish with exactly the same primary
registers. Any binary spare-list/frame argument is separate and belongs to
the literal runtime proof, not this source lemma.

### Exact whole-program reconstruction

The independent reference retains the literal 219-node main scheduler, dispatch,
MP, DROP, NIP, parameter readers, and all arithmetic/formula macros. It replaces
only the complete AX subtree by a closed sequence of those literal macro bodies.
Every macro used has boundary (0,0,false), so reassociating that sequence is
valid in the surrounding dispatch. The symbolic evaluator follows the proved
macro register contracts and checks the entire stack, the old cache's GEN use,
the exact y/u read count, and the unchanged five-macro gate/cleanup suffix.
Then the whole actual program is compared with the modified reference, including
all non-AX control. The candidate's `rows` metadata alone is never trusted.

For a clean root input, the unchanged scheduler/control/macro contracts prove
one root run equals one step of the parameterized enumerator. Every root run
finishes normally or takes its actual NIP halt; no extra exit is introduced.
Determinism gives the converse. Induction over finite root runs therefore lifts
the step correspondence to halting. Sections3--5 identify that halting with D(1).
Graph equality and the two terminating block equivalences transport the result
to each exact saved source in the receipt.

## 9. Reused formal providers and remaining promotion obligations

Under `research_sub246/source/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`:

- `Dag254.lean` / pinned upstream `prog/Dag254.v`: the literal219-node reference.
- `L2Lib254.lean`, `L2Macros254.lean`: arithmetic, stack, parameter-reader and
  constructor register contracts over arbitrary natural fields with clean scratches.
- `L2Control254.lean`: original fetch, dispatcher, MP and NIP contracts.
- `L2Axioms254.lean`: `pushF`, `par1F`, `par2F`, `par3F`, constructor functions,
  `readp2F`, and `gateF`; in particular `l71` proves the five-macro gate suffix.
- `L2Root254.lean`: the unchanged style of root-step/iteration composition.
  Its fixed `ax_eval` is **not** cited as a theorem about the new AX subtree.
- `Enum254.lean`: the source of the parameterized ordinary block and fairness
  argument; its fixed row counts and four-field AX serialization are **not**
  used unchanged for K/S/V candidates.
- `EnumSafeStart254.lean`: the cofinal-safe-start architecture. Its unused-u
  padding is replaced in section5 by x padding, so deleted-u frontends are covered.
- `Code254.lean`: exact code arithmetic/decoder laws; its old C254 axiom relation
  is **not** identified with D after equality-vacuity deletion.

The changed ordinary enumerator/source proof is supplied here. A checked new
Lean/Rocq theorem, including parameterized parser/rows and its exact source
instantiation, remains a formalization task. The old fixed-source Lean endpoint
alone does not prove it. Literal binary runtime, blank initialization, decoder
allocation/folds, and a final <=235 count remain separate candidate-specific
obligations; their evidence must name the same pinned source graph and seed.
There is no publication or new state-bound claim in this directory.
