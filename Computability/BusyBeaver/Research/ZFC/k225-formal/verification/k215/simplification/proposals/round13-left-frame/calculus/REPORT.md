# Optional next step: formula-local equality capabilities

Pin: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95` in VladimirReshetnikov/ProveIt.

## Finding and priority

Phase 14 has already done the important broad extraction: `TarskiDerived.Rows`
and an explicit `Kalmar.Classical` basis serve both `Thm` and `ThmK`. Do not
present that sharing as new. Likewise the shared dominated implication core,
direct full seed, and round-12 QHyp proposal are not discoveries in this packet.

The remaining next step is narrower: share the *Leibniz induction and specialization
proof*, with the missing equality-vacuity fact requested only at actual binders
of the formula. This is an optional proof-maintenance improvement, not the main
line-saving recommendation of this round. The prototype replaces three production
files: 780 -> 775 physical lines and 33,252 -> 32,595 UTF-8 bytes, a net 5 lines /
657 bytes less. These counts INCLUDE new helper APIs and explanatory comments;
they exclude the separately supplied, uncompiled 44-line audit client. They are
source-size figures, not measured build savings, verified kernel savings, or
endpoint-module reductions. The K client itself shrinks 215 -> 185 lines, but
its shared providers grow, so the 30-line client reduction is not net savings.

## Exact logical interface

The generic `leibniz_core` takes:

1. A theorem predicate `T : NF -> Prop` and `hC : Kalmar.Classical NF.imp NF.bot T`.
2. The existing `Rows T`, unchanged from phase 14.
3. Provable symmetry `forall x y, T (x=y -> y=x)` and provable transitivity
   `forall x y z, T (x=y -> (y=z -> x=z))`.
4. A formula f and the existing guards `not Bound x f` and `not Bound y f`.
5. Precisely the local capability
   `forall i, Bound i f -> T (x=y -> forall i, x=y)`.

It returns both directions of `x=y -> (f <-> rn x y f)` using one induction.
The last premise is not an arbitrary semantic predicate or an extra global
calculus axiom. It is an explicit object-language theorem requested for each
binder that appears in f. Recursive calls restrict that premise to the chosen
subformula; the quantified case uses it at that case's actual binder.

The two adapters discharge it differently:

- `Thm`: `.vacEq x y i` is available because `Bound i f` together with the
  unchanged two Bound guards establishes `i != x` and `i != y`.
- `ThmK`: the unchanged `QF f` premise gives `qf_bound`, so `Bound i f` is
  impossible. No unrestricted equality-vacuity provider is installed or used.
  The public `KThmK.leibniz` retains its original `EqFree f` argument as well.

The reusable `specialize_core` is even smaller. Besides hC and Rows, it needs
only `T (x=y -> (f -> g))` and `T ((exists x, g) -> g)`. It combines generalized
forward rewriting, existing `all_imp_ex`, and the existing `rho1 x y` witness.
It knows nothing about freshness or syntactic classes. Each old wrapper still
constructs the exact elimination theorem it previously needed:

- Thm keeps `y != x`, `not Bound x f`, and `not Bound y f`.
- ThmK keeps `y != x`, `QF f`, and `EqFree f`; it still proves equality-freedom
  of `rn x y f` and still calls `not_occurs_rn` to discharge its freshness test.

The alpha-renaming theorem statements AND bodies are unchanged. Their existing
freshness (`not Occurs y f`) and fragment hypotheses are not weakened or hidden.
No arbitrary equality-vacuity, full Thm-to-ThmK transfer, or removal of capture
conditions is asserted.

## Small equality-witness extraction

`eq_refl_of_vac hC c x hv` derives x=x from one supplied theorem
`hv : T (x=x -> forall c, x=x)`, using rho7's contraction, existential
monotonicity, rho1 c x, and `ex_elim_of_vac`. It does not require c to be fresh
as a separate premise; the caller already supplies the appropriate theorem.

The ordinary caller uses c=x+1 and `.vacEq`; the K caller uses c=wel x x and
`.helper x x`. This makes their genuine difference explicit without duplicating
the reflexivity argument. The short symmetry/transitivity proofs were left in
place because introducing adapters for them added more interface overhead than
it removed. That rejected micro-refactor is not part of the final patch.

## A useful extra result, without changing the old contract

The generic Leibniz core handles equality atoms via derived equality transitivity
and symmetry. For quantifier-free K formulas, its binder capability remains
vacuous even if equality atoms occur. `LocalEqualityAudit.k_qf_leibniz` therefore
states a stronger auxiliary rewrite theorem requiring QF but not EqFree.

This does NOT justify dropping EqFree from specialization: its existential
elimination still requires a vacuity theorem for the renamed body. The stronger
rewriting theorem is an uncompiled corollary, not an adopted endpoint change.

## Source and compatibility evidence

`inputs/` contains ten exact blobs obtained through the read-only GitHub
connector. `INPUT_PINS.json` records Git blob SHA-1 and SHA-256; the source audit
rechecks both. The three edited inputs also match the independent current-source
review. No received generator/build script was run and no repository was pushed.

`build_proposal.py` is a new, owned, deterministic text transformer. It writes
three complete proposed files, the patch, and exact metrics. `audit_proposal.py`
reruns only this owned builder, checks byte determinism, verifies all 62 original
explicit theorem headers after whitespace normalization, and confirms all six
imports unchanged. The old implicit section parameters and elaborated types
still need kernel checking; textual headers alone are not their proof. It also
checks preservation of the local capability and K's helper/fragment guards, rejects
admission commands, and exhaustively checks the one conditional implication
pattern on 32 Boolean assignments. That finite test is not a validation of the
quantifier theorem or the formal proof term.

`proposed/LocalEqualityAudit.lean` supplies six old-interface typed clients and
one stronger QF-only rewrite corollary, followed by explicit axiom-report commands.
These are future obligations, not executed reports.

Replay from any working directory:

    python /path/to/research215_round13_calculus/audit_proposal.py

Expected checked-in result: `AUDIT.json`, status `PASS_SOURCE_AUDIT_ONLY`, ten
input blobs, theorem-header counts 27/20/15, and the exact production totals above.
The builder and audit refuse optimized Python. The checker deliberately does not
run Lean or Rocq, imported repository code, received scripts, or external tools.

## Verification boundary and adoption order

No Lean or Rocq executable is installed on the inspected PATH or standard searched
locations. This patch has NOT been elaborated or kernel checked. The exact proof
terms and recursive argument elaboration must be tested before adoption. There is
no claim of a fresh endpoint assumption report, unchanged kernel axiom profile,
unchanged transitive import closure, or formal equivalence merely from this audit.

Compile in dependency order: TarskiDerived, TarskiLeibniz, then KThmK; compile
LocalEqualityAudit; rebuild the maintained phase-14 endpoint and compatibility
clients and compare their named axiom reports with the accepted phase-14 record.
The imports remain directed Derived -> Leibniz -> KThmK, so the proposed extraction
adds no module or direct import edge. Runtime/source/program data and the machine
remain untouched.

## Rocq scope

The pinned Rocq `rocq224/src/Complete222.v` already uses the direct full-seed code
`tau (th (Wn (Wn (tr source_names phi))))` and the abstract interpreted predicate Q.
This is recorded as existing work, not a new proposal. This packet establishes no
corresponding Rocq duplicated-induction count or tested Rocq patch. It does not
suggest replacing Rocq's working proof interfaces to mirror Lean, nor transferring
Lean proof-irrelevance or kernel assumptions across languages. Use this round's
separate structural review for its concrete Rocq reduction.
