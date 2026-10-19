# Logical-basis and theory-bundle experiments

## What this contribution establishes

Two exact logical transformations were investigated and compiled far
enough to measure their costs in the recovered routing backend.

1. Replace the four-parameter Lukasiewicz helper row by the three standard
   K, S and Peirce schemas, eliminating the fourth AX field and its reader.
   The best retained literal table has **250 working states**, consisting
   of 117 interpreter/framework states and 133 grammar states. Its new
   source correspondence, all 8,794 guarded instruction contracts, and its
   finite blank initializer are replayed by the supplied Python tools.
2. Reassociate or flatten the four outer theory conjuncts. This
   transformation is derivable already in minimal implication, with an
   arbitrary relative falsity parameter. All 11 ordered conjunction tree
   shapes and all 24 component orders were emitted and costed. The best
   of these 264 candidates is the original 245-state arrangement.

These experiments do not improve the 245-state frontier. No new Coq or
Lean endpoint for the final 250-state table has been closed. The proof
certificates, generic compiler argument and exact binary audits are
provided to make the measured alternatives reusable, rather than to
present a larger machine as the requested breakthrough.

## 1. Replacing the propositional basis

Write implication as `A -> B`. The original row is

```
L(a,b,c,u) = ((c -> u) -> a) -> ((a -> c) -> (b -> c)).
```

The replacement uses

```
K(a,b)   = a -> (b -> a)
S(a,b,c) = (a -> (b -> c)) -> ((a -> b) -> (a -> c))
P(a,b)   = ((a -> b) -> a) -> a.
```

All seven equality and quantifier helper rows, the cached GEN row, the
CP/GIC/vacuity bundle and its parameter gate remain present. The number
of logical helper rows rises from eight to ten. In the best measured
orientation, the source emits `P(a,b), K(c,b), S(a,b,c)` before emitting
the seven retained rows. Because the three numeric parameters range
independently, these orientations still give every substitution instance
of K, S and Peirce.

### Exact proof of equivalence of the numerical calculi

The source schemas operate on arbitrary natural-number formula codes.
The following argument uses only finite expressions in the implication
constructor and modus ponens. It therefore remains valid even at the
special code identities, including the truth code `0 = Imp(0,0)`.

The published file `CD254.v` proves K, Peirce and S from the old L row
alone: the named results are `thm_K`, `thm_P` and `thm_S`, obtained from
`cd_16`, `cd_25` and `cd_106`. The supplied
`check_upstream_lukasiewicz.py` parses that pinned file as finite data
and checks all 111 declarations. Its only initial schema is L; the
remaining proof operations are explicit substitution into an already
verified universally quantified lemma and modus ponens. All 106 MP
steps pass. No Coq parser, elaborator or external theorem database is
trusted by this replay.

For the reverse implication, suppose

```
h : (c -> u) -> a,       k : a -> c.
```

Assuming `g : c -> u`, the term `k(h(g))` proves `c`. Discharge `g`,
giving `(c -> u) -> c`. Peirce at `(c,u)` then gives `c`, and K gives
`b -> c`. Discharging `k` and then `h` yields exactly L. The file
`ksp_to_lukasiewicz.json` expands this argument into 77 DAG nodes:
21 K instances, 17 S instances, one Peirce instance and 38 MP steps.
The replay checker accepts no assumption nodes and does not trust the
generator's deduction-theorem implementation.

Let `C_old` and `C_KSP` be the least classes of numeric codes containing
truth, their indicated helper schemas and the same gated bundle, and
closed under the same MP and GEN rules. Replacing every K/S/P leaf by
its old-L proof gives `C_KSP ⊆ C_old`. Replacing every old-L leaf by the
77-node proof gives `C_old ⊆ C_KSP`. Induction on a finite derivation
therefore gives equality of these classes, not merely external model
equiconsistency. The proof transformations are effective finite
substitutions and can be formalized in ZFC. This argument leaves the
underlying SIR-to-ZFC comparison unchanged.

### Source and state costs

The first emitter pass, before permuting basis orientations, measured:

| Basis | AX macros | Dictionary calls | Fine operations | Named Wade states |
|---|---:|---:|---:|---:|
| Original L | 186 | 533 | 1,270 | 281 |
| K, composition H, Peirce | 194 | 584 | 1,321 | 282 |
| K, S, Peirce | 196 | 594 | 1,331 | 280 |
| K, S only | 189 | 558 | 1,295 | 279 |

The last row is a cost experiment: no proof that the retained quantified
rows restore classical completeness was supplied, so it is not used as
a complete basis. Likewise, a fixed-falsity L variant must not be called
complete merely because its Boolean instances are tautologies.

There were 1,296 tested combinations of K/S/P parameter permutations
and row orders. The best initial routed grammar had 134 states. A retained
45-second annealing run reduced this to 133, giving the literal 250-state
table. The state total is independently rebuilt as `117 + 133`; an older
framework count appearing in a searcher's raw metadata is not used for
the table's state accounting. This demonstrates the limitation of counting
saved source routines: deleting `read_u` saves one state in one backend,
but the longer emitted axiom list uses more distinct shared grammar nodes
in the backend that attains 245.

The canonical table is `routing_KSP_best/machine/ksp_250.tm`, SHA256

```
125b42fb7ac3db95e43f74e20d75cbfde543de71354e8ee488152ecd2e90dcc1
```

It has working states 0 through 249, start state 0, and halt target 250.
All 500 transition rows are present. The rebuilt new source has 6,770
instruction leaves and maximum path depth 54. Its exact register-program
comparison has 3,171 control pairs and 6,340 successor edges. The affine
audit checks 2,024 zero and 2,024 positive decrement cases, 2,725
increments, 132 breaks, 1,888 continues and one halt, totaling 8,794.
The inherited affine register-box contracts remain its explicit macro
assumptions; their inference rules are not weakened for the new source.

Sparse and dense binary interpreters independently agree after 407,915
blank steps, at a valid empty-program-counter dispatcher frame, head -5,
header 176, with logical registers `[3,0,0,0,3,0,0,0,0]` and 351 ones.
This finite agreement checks the initializer. It is not a test of eventual
nonhalting.

## 2. Generic completeness macros for ten helper rows

This section supplies the stack proof required by changing the AX row
count. Reusing the old constants 9, 10 and 11 without adjustment would be
incorrect.

Let `m` be the number of logical helper rows. Number them in stack-pop
order as `R_1,...,R_m`. Each is an implication or universal formula, so
its numerical code differs from the falsity code 1. The GEN code also
differs from 1. Let `W=(T,S,D,H)` denote the top formula, stack, numeric
parameter and cached formula. AX with fields `(c,x,y)` sets

```
a = D+x, b = H+y,
W' = (gate(a,b,c),
      [R_1(a,b,c),...,R_m(a,b,c),All(a,H),T] ++ S,
      0,0).
```

The brackets denote Cantor-coded stack cons, not a changed tape alphabet.
`gate` is 0 when `c=a` or `c=b`, otherwise the original theory bundle.
The other commands are exactly the inherited commands. `DROP` pushes T
and copies H to T. `NIP` halts if the *old* H is 1; otherwise it pops the
stack into H. `MP x` increases D by x, checks `Imp(T,D)=H`, and if the
check succeeds makes D current and pushes a truth cell; it always clears
H. Unmentioned command numeric fields below are zero.

Define `Contract(p,X)` to mean that from **every** `(T,S,0,0)`, block p
either halts or returns `(X,S,0,0)`. Allowing early halt is essential when
an intermediate theorem is already the falsity code.

### Truth/reset block

```
discard_m = MP 1 ; AX(1,0,0) ; NIP^(m+2).
```

From `(T,S,0,0)`, `Imp(T,1)` is nonzero, so the MP comparison with H=0
fails. It returns `(0,S,1,0)`. AX has `a=c=1`, hence gate 0, and pushes
m helper rows, the GEN row and the old truth cell. All cells passed
through H before the final pop differ from 1. Exactly `m+2` NIPs restore
`(0,S,0,0)`. Thus `discard_m` has the exact truth contract.

### Axiom and bundle leaves

For helper index `1 ≤ j ≤ m`, use

```
leaf_j = discard_m ; AX(c,a,b) ; NIP^j ; DROP ; NIP^(m+3-j).
```

After discard, AX reads the desired a,b,c without additive contamination.
The first j pops place `R_j` in H. DROP makes it current and pushes the
gated bundle. There remain `m-j` helper cells, one GEN cell and the old
truth cell below that inserted bundle, hence `m+3-j` remaining pops.
Their final pop restores H=0 and the original S. Gate and every helper
passed through H have codes unequal to 1. This proves the helper contract.

For the actual ungated theory instance, requiring `c ≠ a,b`, use

```
bundle_leaf = discard_m ; AX(c,a,b) ; NIP^(m+2).
```

The current bundle stays in T while the entire pushed list is removed.

### Generalization

Given `Contract(p,H0)`, use

```
p ; DROP ; NIP ; AX(i,i,0) ; NIP^(m+1) ; DROP ; NIP ; NIP.
```

If p returns, DROP and NIP move H0 into the cache and leave T=0, without
changing S. AX has `a=c=i`, so it pushes the m helper cells followed by
`All(i,H0)` and the old truth cell, with current gate 0. After `m+1`
pops the cache contains the GEN code. DROP makes it current; the last
two pops clear the temporary truth cell and the original truth cell.
Thus the block returns `(All(i,H0),S,0,0)`. This reasoning remains valid
when H0=1: the cached 1 is consumed by AX before another NIP is executed.

### Modus ponens

Given contracts for pA and pAB, with outputs A and `Imp(A,B)`, use

```
pA ; DROP ; pAB ; NIP ; DROP ; NIP ; MP B ; AX(B,0,0)
   ; NIP^(m+2) ; DROP ; NIP ; NIP.
```

After both successful premise blocks and the first three stack commands,
T=A and H=`Imp(A,B)`. If A=1, a preceding NIP already halts. Otherwise
MP succeeds, giving `(B,[0]++S,B,0)`. AX has `a=c=B`, so gate 0, and
the next `m+2` NIPs recover B into H while preserving the already pushed
truth cell. DROP makes B current. If B=1 the following NIP halts;
otherwise the final two pops return `(B,S,0,0)`. This proves the desired
contract in every case.

Induction on a C_KSP derivation now builds a contract for every theorem.
For **m=10**, the constants are: 12 pops for discard, bundle and MP
cleanup; 11 pops to reach GEN; and `13-j` pops after a helper is selected.
The symbolic-stack script additionally replays these identities at
m in `{1,2,8,10,12}`, explicitly including the early-halt cases A=1 and
B=1, and reports 1,062 checks. This finite symbolic replay catches the
index arithmetic; the quantified argument above supplies its scope.

### Cofinal proof coding after removing u

The new AX command has three fields `(c,x,y)` and packing

```
pack(AX(c,x,y),r) = P(c+3, P(x, P(y,r))).
```

Other command codes and the nonempty-list convention are unchanged. For
any desired cutoff n and any compiled contradiction block p, prepend
`AX(0,n,0)` and append `DROP; NIP; NIP`. The first AX resets D=H=0 from
any working state; its current top and stack need no further constraints
because `Contract(p,1)` quantifies over both. If p returns, the suffix
places 1 in the cache and then halts.

Its nonempty candidate code is at least n:

```
n ≤ P(n,P(0,r)) ≤ P(3,P(n,P(0,r))).
```

Here r is the encoded remaining list pointer. Thus there is still a
halting refutation program above every initial candidate cutoff. The old
fourth AX field is **not** needed for the cofinality argument. The first
two source routines, fetch and selector read, are unchanged, so the
ordinary dirty-root absorption argument also applies to this changed
program once stated for that program. The existing Lean theorem about
the original DAG cannot simply be cited as a theorem about the new DAG.

The normal soundness invariant is unchanged: T and H are theorem codes,
and every stack head is a theorem code. AX, MP, DROP and NIP preserve it
unless NIP halts with a cached proof of 1. Together with the contract and
cofinality arguments, this gives the mathematical new-enumerator
calibration. Porting this reasoning through a new Coq/Lean source and
literal-table endpoint remains an explicit integration task.

## 3. Flattening the theory bundle

For an arbitrary formula F define the negative conjunction

```
And_F(A1,...,Ak) = (A1 -> ... -> Ak -> F) -> F.
```

For four formulas put

```
Nested = And_F(And_F(A,B),And_F(C,D))
Flat   = And_F(A,B,C,D).
```

Both directions are derivable using **K and S alone**. Typed lambda
terms that display the proofs are:

```
Nested -> Flat:
  lambda n k. n (lambda ab cd.
                  ab (lambda a b. cd (lambda c d. k a b c d)))

Flat -> Nested:
  lambda f k. f (lambda a b c d.
                  k (lambda h. h a b) (lambda h. h c d)).
```

The exported Hilbert certificates contain respectively 299 and 251
nodes. All leaves are K or S instances, all other nodes are MP, and there
are no assumption leaves. In particular this equivalence does not need
Peirce, ex falso, irreflexivity, or a proof that the relative F code denotes
absolute falsity. It therefore applies directly to the numerical source
constructor and its possibly degenerate parameter instances.

The old outer bundle uses nine implication constructors, apart from its
four components; Flat uses five. More generally a binary tree on n leaves
uses `3(n-1)` such constructors and its n-ary flattening uses `n+1`, a
saving of `2(n-2)`. The savings in constructor occurrences are real.
They do not imply a saving in distinct compiled grammar nodes.

The four components are the original CP instance, GIC instance and the
relation/equality vacuity instances. All 11 ordered n-ary tree shapes on
four leaves, combined with all 24 component permutations, were tested.
Each candidate passed an exact symbolic check of the full emitted AX
stack, and was segmented/assembled using the existing six-zero constrained
dictionary at four additive-cost penalties. The minimum is the original
balanced component order, with 128 grammar states. The fully flat order
CP,GIC,relation-vacuity,equality-vacuity starts at 129 grammar states and
remained there after its retained 45-second annealing run. These results
are search outcomes, not lower bounds on every possible compiler.

## 4. A ruled-out shortcut and a scoped dirty-seed audit

Fixing u to F in L and adding K appears cheaper than K/S/Peirce, but it
is not a complete **pure propositional** basis. A three-valued matrix
with designated value 2 and F=0 is

| `->` | 0 | 1 | 2 |
|---|---:|---:|---:|
| 0 | 2 | 2 | 2 |
| 1 | 2 | 0 | 2 |
| 2 | 0 | 0 | 2 |

It validates L[u:=F], K, ex falso and double-negation elimination, and
preserves designated truth under MP. Yet `a -> a` fails at a=1 and S has
counterinstances. The supplied exhaustive checker verifies this finite
certificate. It interprets no quantified or equality schemas; stronger
claims about the enriched full calculus would require additional work.
Raw exploratory cost JSONs retain their contemporaneous `UNPROVED`
labels; this paragraph and the status index record the later obstruction.

The appendix checks that the original source's safe dirty-root theorem
allows X=35 at seed `[3,0,0,0,3,0,35,0,0]`. It also records why this says
nothing by itself about the correctness of a shared-grammar deletion.
`DirtySeed35.lean` is explicitly **UNCOMPILED** and is only a small
specialization of existing declarations, not a new machine theorem.

## Primary references and provenance

- Original exact source and numerical logic:
  https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254
- Source formula schemas:
  https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/tools/logic/spec.py
- Existing L-only proofs of K, S and Peirce:
  https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/logic/CD254.v
- Existing eight-row enumerator proof being generalized:
  https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean
- Existing arbitrary safe-start cofinality theorem:
  https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumSafeStart254.lean
- Prior 245 routing package:
  https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Research/ZFC/candidate-routing245/README.md
- F. Pfenning, *Single Axioms in the Implicational Propositional Calculus*,
  CADE 1988 (primary discussion of the classical implicational bases):
  https://www.cs.cmu.edu/~fp/papers/cade88.pdf

Mira-Cult, Jeff Ketchersid and Andrew James Wade are credited with the
published source/runtime work. The vendored dependency subset carries
the inherited notices and available MIT-0 licenses. New experiments and
proof replay adapters are distinct from those inherited components.
