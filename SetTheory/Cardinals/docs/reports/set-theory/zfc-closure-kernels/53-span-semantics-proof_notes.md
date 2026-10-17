# Proof audit and two complete negative compiler controls

Audit pin: `VladimirReshetnikov/ProveIt@43026ff42f0939f09b9e95495248cfadcad38e38`.
Original program/compiler pin: `jeff87654/busy-beaver@297ab8df7e5de329605c3875b4934643b371a5e3`.

## Exact current endpoint

The selected machine is the complete original-calculus register-permutation
candidate, not the earlier equality-free `raw-candidate-252.tm` or the 248-state
grammar experiments. Its canonical table has 252 working states, 504 rows,
start state 0 and separate halt label 252. The canonical SHA-256 is
`8dae0c2359aa8bf87d32543b9e53e1f87fe4716c016a4e2fd174bfe09e520797`.

Two current Lean modules give the closed external theorem

```
(not (exists t, (machinePerm252.run t).state = none))
  iff not (BProv ZFCax_s [] Form.fBot).
```

`BinaryZFC252` composes `BinaryPerm252.blank_halts_iff_zf_refutation` with
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Independently,
`ChoiceCalibration254` constructs the actual constructible subtype of a ZF
model, proves its Choice axiom from its own ZF/Power/Regularity/V=L bundle,
supplies an explicit constructible empty ordinal to witness nonemptiness,
and applies first-order soundness and completeness to compare refutations.
The final statements have no model, Choice, coverage, startup, or runtime
premise. The reported standard Lean dependencies are `propext`,
`Classical.choice`, and `Quot.sound`; no new kernel build was run in this audit.

The source explicitly calls these external metatheorems and leaves effective
arithmetic proof-code/trace comparison in PA open. The user's requested
metatheory is ZFC, not PA. Ordinary first-order completeness, relative
consistency through constructibility, and finite computation arguments can be
formalized in ZFC. Nevertheless a closed external Lean theorem is not, just by
its kernel check, a displayed internally coded ZFC derivation. Keep this
distinction without incorrectly treating the unresolved PA project as a new
missing model/Choice assumption in the already closed external theorem.

Exact pinned references:

- [Candidate README](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md)
- [BinaryZFC252.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryZFC252.lean)
- [ChoiceCalibration254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean)
- [Endpoint integration scope](https://github.com/VladimirReshetnikov/ProveIt/blob/43026ff42f0939f09b9e95495248cfadcad38e38/Computability/BusyBeaver/Research/ZFC/binary_zfc252.md)

The `reference` directory retains the retrieved endpoint texts and exact
enumerator definitions. Copies are source data; they do not install a proof
environment or import compiled Lean objects.

## A different semantic reduction: observe the first creation of falsity

Let `F=1`. At command boundaries, use the predicate that the current formula
`T`, cached formula `H`, and every entry of the theorem stack differ from 1.
The zero initial state satisfies this predicate. The infinite-zero-stream
convention for stack zero causes no exception.

Every AX output is a code of an implication or a universal formula, hence is
0 or 2 modulo 4 and differs from 1. This includes all eight logical rows,
the gate's truth-zero alternative, the C/G/vacuity bundle, and the cached
formula's generalization. AX also saves the old current formula, which is
covered by the predicate. DROP only copies or pushes existing formula values;
NIP only reads the stack. An unsuccessful MP produces zero. Consequently the
only command that can first introduce code 1 is a successful MP whose
conclusion parameter is 1.

Modify the abstract enumerator as follows: NIP always performs its old pop;
successful MP halts immediately when its conclusion is 1; every nonhalting
transition is otherwise unchanged. This modified enumerator halts iff the
original enumerator halts from the zero state:

1. Until a successful MP concludes 1, the predicate is maintained. Therefore
   NIP's old halting test never succeeds, and both enumerators follow the same
   configurations.
2. An original finite halting run must previously have a first MP conclusion
   1; otherwise the predicate would still hold at its halting NIP. The modified
   run reaches that MP and halts.
3. At a modified halting MP, the common original prefix has the original
   theorem invariant. Its two premises give an actual `C254 1` derivation.
   The established original enumerator completeness then implies original
   halting. This direction does not assume that the same original trace will
   immediately notice its newly created 1.

This is an ordinary finite-induction argument about the precise enumerator,
not a deletion of equality or a change of consistency strength. The separate
variant that also omits MP's dummy zero push requires the known adjusted MP
proof-compilation block; it does not have the same prefix-by-prefix proof.

### Concrete cost, fully charged

`mp_birth_cost.py` reuses the exact finite source DAG and pinned Wade backend.
It replaces NIP's `inc X; compare(X,H); pop H` by `clear H; pop H`, and adds a
preserving exact-one test either after successful MP's copy to T or just before
that copy on D. The test returns the register unchanged for values 0 or at
least 2, and halts for value 1. The D version needs a new double-increment
node; the T version shares existing node 159.

| Complete Wade control | Decision | Framework | Working states |
|---|---:|---:|---:|
| Exact original | 219 | 62 | 281 |
| First-MP test on the new T | 222 | 62 | 284 |
| First-MP test on D before copying | 223 | 62 | 285 |
| T test, additionally omit dummy zero push | 222 | 62 | 284 |
| D test, additionally omit dummy zero push | 223 | 62 | 285 |

Every reachable source decision is independently re-extracted from the emitted
table. Every working state has two rows after the one documented missing
backend row is totalized to a tape-preserving rightward halt. Each changed
variant passes 101 exact register-path tests of its exact-one guard and 50
clear-and-pop tests. These tests use literal zero-padded path semantics:
break counts zeros, continue counts ones, and carrying preserves the zero
suffix. A naïve interpreter that merely counts enclosing subroutine calls
does not implement this semantics.

The initializer is fully charged in each table, but its changed blank-start
invariant and binary simulation are not proved. In particular the increase
from 281 to 284/285 cannot be added to or subtracted from the separately
optimized 252-state artifact. These are complete negative cost controls.

## Deterministic modus ponens: another measured negative control

The second experiment avoids guessing the consequent. At an MP entry, the
opcode register A is zero. It saves the old T there, divides cached H by four,
rejects a nonzero remainder, unpairs the quotient into antecedent/consequent,
and compares the antecedent with the saved T. Equality returns the consequent
as new T; failure returns zero. The old additive D is ignored and preserved;
W is preserved; A, H, X and Y finish zero. The optional first-birth variant
tests the successful result for 1 and replaces NIP by an unconditional pop.

The source uses every original logical and theory constructor. It supplies
all helper states, including quotient/remainder validation, temporary-value
transport and cleanup. Nothing is charged as a free inverse operation.

| Complete Wade control | Decision | Framework | Working states |
|---|---:|---:|---:|
| Deterministic MP, original NIP halting test | 238 | 64 | 302 |
| Deterministic MP plus first-birth halting | 241 | 64 | 305 |

Each variant passes 2,178 exact register-path cases: H from 0 through 120,
T from 0 through 8, and two distinct stack/additive-parameter settings. These
cover successful detachment, all four residue classes, zero/truth alias,
mismatched antecedents and actual successful conclusion 1. The independently
re-extracted tables include the full framework and its two additional
dispatcher states. The generic inverse parser is more expensive because the
old forward arithmetic remains shared with AX. These experiments do not
establish a lower bound on jointly changing arithmetic, layout and syntax.

The altered proof compiler can use MP parameter zero, the existing reset AX
with a matching zero gate, and one fewer cleanup NIP after successful MP.
That gives a concrete ordinary completeness route. No new Lean theorem,
compiler simulation or clean blank bootstrap is asserted here.

Reproduce both controls, entirely offline, from this directory:

```
python3 mp_birth_cost.py
python3 deterministic_mp_cost.py
```

Complete DAGs, transition tables, counts, hashes and validation records are in
`mp_birth_results` and `deterministic_mp_results`. Source attribution remains
Mira-Cult (original program/machine), Jeff (finite DAG and verification), and
Andrew James Wade (compiler). `backend/LICENSE.wade` retains the MIT-0 license.
The original finite DAG is
[Dag254.v](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/prog/Dag254.v),
SHA-256 `538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3`.

## Affine/prefix codec proof obligations

For constructors `C_i(a,b)=m_i P(a,b)+t_i`, the following are sufficient local
conditions: integer `m_i>=2`; nonnegative tags; implication has tag zero;
every other tag is positive; membership has tag exactly one; and the four
arithmetic progressions are pairwise disjoint. A convenient exact arithmetic
disjointness test is that `gcd(m_i,m_j)` does not divide `t_i-t_j` for every
distinct pair. Under these conditions constructors are injective and disjoint,
and every child and variable label is strictly smaller than every positive
constructor code.

Holes need not invalidate a codec. A total decoder may send each hole to the
truth alias T0. But `enc(dec n)=n` then fails, and no bijection may be claimed.
Prove numerical soundness for all natural input parameters using that total
decoder, and prove completeness on canonical named-formula encodings. The
zero implication alias needs its special MP case: `Imp(x,y)=0` forces x=y=0,
whose decoded conclusion is already true.

Every positive hole decoded as T0 still has all its labels below its code.
Code zero is different: T0 contains label zero, so the assertion that every
label of `dec(c)` is strictly below c is false at c=0. The dynamic C/G matrix
gate must retain a separate semantic-truth treatment of c=0. Keep the exact
`c != a,b` gate and prove arbitrary-matrix coverage; constructor disjointness
alone proves neither freshness nor coverage. A formula-code transformation
also changes the numeric variable chosen as its output binder. Therefore a
plain uniform integer remapping is not automatically a translation of the
entire bundle or of every original numerical proof.

The current retained full equality engine avoids earlier refuted quantifier-
only shortcuts. Deleting equality removes the original mechanism for
cross-variable instantiation and alphabetic variance. Likewise replacing
original rho6 by its familiar dual needs an exact relative-falsity argument:
F is the membership atom Rel(0,0), and binder zero can capture it. The historic
reduced 252/248 experiments are not alternate proofs of the selected complete
permutation candidate's endpoint.
