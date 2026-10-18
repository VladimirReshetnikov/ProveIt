# Independent audit of the context246 proof boundary

## Scope and result

This audit reads the delivered `zfc-context246-20261018.zip`, obtained from
ProveIt commit `8cdc55ff9281b0aaba49bf74b0b225d57f12b893`. The package itself
pins its inherited sources to `e0b512a63e2c1ca6a1698fa437b8568f1643ff6b`.
These are different provenance roles, not competing machine versions.

**No counterexample was found to the context246 local contracts, bootstrap,
or ordinary mathematical composition.** The package's exact 246-state table
has a conventional proof conditional on accepting its explicitly identified
inherited interpretation lemmas and the reviewed symbolic checker. It does
not have a newly compiled 246-state Lean/Rocq endpoint. An external Lean
theorem for permutation252 is not automatically a ZFC proof of the altered
table. The report itself states this distinction correctly.

The important positive conclusion is that leaving *PA* internalization open
does not obstruct the user's weaker request for an ordinary proof *in ZFC*.
The particular interpretation arguments used here are set-coded model
constructions formalizable in ZFC. This is a specific mathematical argument,
not a blanket translation theorem for Lean or its universes.

No file under the repository was edited. The verification commands below
were run on this audit's separately extracted copy. No inherited Lean
dependency closure was rebuilt.

## Independently rerun checks

The following all passed:

| Check | Actual scope |
|---|---|
| `code/check_folds.py` | 494 restricted commuting rows; exact incoming-edge premises; 246 graph-reachable working states; source reconstruction agreement |
| `code/check_macro_inductions.py` | Four arbitrary-length one-block identities; the carried-word identity; positive decrement, zero decrement, increment; all nine marking selectors |
| `code/review_affine_source.py` | Fully consumed 6,459-node source tree, 6,460 leaves, complete successor paths, all 8,391 guarded cases, 342 guard controls |
| `code/check_bootstrap.py` | Exact 410,735-transition blank prefix and complete final tape support |

The affine recheck records 1,931 zero decrements, 1,931 positive decrements,
2,601 increments, 128 breaks, 1,799 continues, and one halt. The smallest
literal-step count is 13. It preserves all overflow and trailing-zero path
cells. The maximum leaf depth is 34, below the required distance 40.

These checks are finite computational proof checks under sound symbolic
rules; they are not themselves a newly checked proof-assistant kernel. The
literal bootstrap proves initialization only, never nonhalting.

## 1. The two forced-symbol identifications

The marking fold `0 -> 20` is valid because each plain register block has
shape `01^(v+1)`. After `60/0` moves onto its first one, old `0/1` and retained
`20/1` are both `(0,L,2)`. The excluded `0/0` branch cannot arise during valid
marking, including a zero register. Removing state 0 disconnects old startup
states 1 and 3. Their deletion needs a fresh blank initialization, which the
package supplies.

The pulse fold `97 -> 255` uses a preceding write, not a sampled read mask.
Entry to old 255 is only through `75/0`. That step writes one at position
`x`. If the neighbor at `x+1` is zero, the following step writes one there
and returns to `x`, which is therefore known to contain one. Old `97/1`
and retained `255/1` are both `(1,L,131)`. Arbitrary exterior tape content is
allowed in this local argument.

The restricted quotient identity intentionally omits six old state/read
pairs. Its universal use requires the marking and preceding-write
invariants, plus the instruction traces' avoidance of those exceptions
outside the boxes. An exhaustive row identity alone would not establish
unbounded equivalence on arbitrary tapes.

## 2. Prefix carry, moving header, and spares

With `B(v)=01^(v+1)` and `C(v)=101^v`, the relevant word identity is
`C(A)1 = 1B(A)`, proved by induction on the finite list A. It is the reason
positive decrement leaves a new one at the old file origin and moves the
header one cell to the right.

The audited contracts are:

| Operation | Exact effect |
|---|---|
| Mark index r | Erase its compulsory one; no value or boundary change |
| Increment | Increase selected value; append one spare of value 1 |
| Positive decrement | Decrease selected value; boundary moves right 1; preserve spare suffix |
| Zero decrement | Restore file; return via old 112; preserve spare suffix |

Zero decrement needs a following block. Nine primary registers plus a
**nonempty** spare suffix guarantee this for every selected physical index
below nine. The spare values themselves are arbitrary natural numbers.
Increment preserves nonemptiness by appending; both decrements preserve the
existing suffix. Thus no finite spare reserve is consumed by a long run.

The full distance is `d = header - dispatch_head`. It is not merely the
number of zero cells after the stored PC. If a positive decrement occurs,
let delta=1; otherwise delta=0. If PC carry crosses the left marker, let
epsilon=1; otherwise epsilon=0. The frame update is
`h' = h - epsilon`, `d' = d + delta + epsilon`. Therefore `d >= 40` persists.

**Important rejected shortcut:** changing `75/0` directly to `(1,L,63)` and
deleting 255 would shorten the increment tail, but it also changes the
zero-decrement case. In that case state 75 sees the separator of the next
block, and 255 must distinguish its mandatory next one from the blank tail
seen by increment. Verifying only the increment macro would miss this
failure. This proposed 245-state modification is not certified.

## 3. Why the 8,391 cases cover unbounded execution

The independent parser checks the complete rooted forward binary tree,
including unique parenthood and every source token. A cached leaf count
alone would be insufficient. Each logical increment/decrement uses a
register below nine and the fixed physical mapping
`(N,T,W,A,D,H,X,Y,L) -> (6,2,0,4,3,7,8,5,1)`.

For a clean stored path P and consumed leaf Q of length l, its zero
extension satisfies

`P 0^(d-|P|) = Q 0^(d-l) = Q 0^(n+40-|Q|)`, with `n=d-40 >= 0`.

The clean-path predicate supplies zero bits past the consumed leaf. This
rebasing covers a stored path shorter than a leaf and an unused trailing
zero suffix. The independent source review checks full successor paths,
including overflow, instead of relying only on a stripped representation.

The affine engine's sound rules are literal transition execution, scans of
uniform runs justified by unary induction, safe peeling only when the
constant length is positive, representation changes that preserve the
whole tape, and the four proved box contracts. Its guard names the same
physical register as the marked block. Its single-effect box state prevents
a second unnoticed update. Literal access to an opaque context is rejected.

The complete target is compared, not simply a visit to dispatcher 96.
Some valid instruction traces revisit 96 before restoring their full frame.
A classifier that accepts the first such visit would be unsound.

Positive segment lengths establish halting equivalence without an infinite
choice principle: for the reverse direction use strong induction on the
binary halting time. A nonterminal source step has a positive finite binary
segment ending active. Absorption of halt makes that segment shorter than
the presumed remaining halting time. Apply induction at its endpoint.

## 4. Exact initialized root and completeness

The verified context246 root is old dispatcher 96, head -5, marker -6,
header 176, empty PC, physical values `[0,0,0,3,0,0,3,0,0]`, and 167 spares
of value 1. Its full tape has exactly 351 one-cells and is zero elsewhere.
Its logical register vector is `(3,0,0,0,3,0,0,0,0)`.

`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0` is the correct
specialization. The arguments are `(N,A,D,X,Y,L)`, not physical indices.
Both formula fields are truth code 0 and the stack is its safe zero stream.

Starting the candidate counter above zero loses no refutation:
`EnumSafeStart254.pad_code_ge` and `padded_program_halts` explicitly supply
arbitrarily large padded halting proof programs, while `reach_ge` proves
that each later candidate is eventually reached unless the run has already
halted. `DirtyRoot254.stage_virtual` handles arbitrary initial numerical
scratch/control fields. These are stronger, precise statements than an
informal assertion that an enumerator is fair.

Broader roots are available: the exact safe condition is
`C254(T) and C254(H) and Good(W)`. See `safe_root_codes.py` for a conservative
checker and the final section below for its mathematical justification.

## 5. Ordinary ZFC internalization

Fix natural-number codes for syntax, derivations, finite configurations,
and computations. Let Ref(T) mean existence of a finite first-order
refutation in that fixed presentation. The inherited mathematical chain is

`C254(1) <-> Ref(NativeAx) <-> Ref(ZF) <-> Ref(ZFC)`.

For the exact conventional theorem, the required inherited ingredients are:

1. Literal source program versus structured program, plus safe dirty-root
   soundness and padded completeness.
2. Numerical code calculus versus the actual native first-order theory,
   containing CP, every syntactic Form-GIC instance, and raw irreflexivity.
3. The native-to-ZF model construction via an extensional bisimulation
   quotient and its **internally** well-founded subdomain; and the reverse
   interpretation using rank containers and Collection in ZF.
4. The ZF-to-ZFC model construction through internal constructibility.

Inside ZFC, every structure here is set-coded. Satisfaction is recursion on
finite syntax for a set structure. Henkin completeness yields an inhabited
set model from syntactic consistency; it does not require a transitive or
externally well-founded model. Bisimulation relations form a set of subsets
of the carrier squared; the quotient is a set. The WF and L domains are
definable subsets of their ambient set carriers.

The inspected `WellFoundedPart` source explicitly quantifies over represented
subsets in its internal minimal-element predicate. `WFModel` proves closure
with a literal GIC witness formula, translates Separation and Replacement
with guards, derives Infinity by separation from an inductive set, and
keeps Power explicit. It does not incorrectly take the externally
well-founded part of an arbitrary ill-founded model.

The inspected `ChoiceCalibration254` supplies an explicit inhabitant of L,
establishes ZF and Choice on that subtype, and transfers refutations using
soundness and completeness. No truth predicate for the ambient universe,
large-cardinal model, external Foundation of the model relation, or assumed
model of ZFC is needed. Uniform induction on formula codes handles the
schemata.

Consequently the concrete finite simulation proof and these set-coded
interpretations give an ordinary ZFC proof of

`Halt(M246,blank) <-> Ref(ZFC)`,

and negation gives the requested nonhalting/consistency equivalence. The
equivalence itself has no consistency hypothesis. A serialized ZFC proof
object, a new exact-table Lean endpoint, and an effective PA proof-code
translation are distinct further formalization tasks. This audit inspected
the selected source interfaces and their arguments, not every dependency
or a fresh full Lean build.

## 6. Independence claims

From the ZFC-internal implication `Nonhalt(M) -> Con(ZFC)`, Gödel's second
incompleteness theorem excludes a ZFC proof of nonhalting if ZFC is
consistent and its usual derivability conditions are used. The external
correctness argument also identifies actual nonhalting with actual absence
of a finite ZFC refutation.

Mere consistency must not be used to exclude a ZFC proof of the false
existential halting statement. A consistent theory can prove its own
inconsistency. A sufficient additional hypothesis is Sigma1 soundness,
because halting is Sigma1. Thus full two-sided independence needs that
qualification. The context246 report makes it correctly.

## 7. Conservative broader safe-root certificates

The code constructors are `P(x,y)=tri(x+y)+y`, `Imp(a,b)=4P(a,b)`,
`All(i,b)=4P(i,b)+2`, `Eq(i,j)=4P(i,j)+3`, and falsity code 1.

The accompanying checker accepts only the following theorem-building rules:

- 0, by `C254.truth`;
- `All(i,b)` from a certificate for b, by `C254.gen`;
- `Imp(a,b)` from a certificate for b, by K and MP;
- `Imp(1,b)`, by `Code254.c254_efq`;
- `Imp(a,a)`, by the inherited implicational identity theorem;
- `Eq(i,i)`, by logical equality reflexivity and the existing
  `alias_complete`/`c254_of_thmG` route.

The last rule targets the named formula `NF.eq i i`, whose encoding is
literally `weq i i`, so it does not rely on an unproved general numerical
completeness theorem or on translating the special truth alias 0 back
through the decoder.

The accepted formula codes in 0 through 9 are exactly `{0,2,3,4,6}`.
`Good(W)` follows by repeatedly unpairing W, certifying its head and then
its tail, until 0. The strict decrease of a positive tail follows from the
Cantor pairing formula. `Enum254.good_cons` then constructs the proof from
`good_zero`. Examples beyond the zero stack are W=3,6,9,10. A rejected
certificate means only "not accepted by these conservative rules".
