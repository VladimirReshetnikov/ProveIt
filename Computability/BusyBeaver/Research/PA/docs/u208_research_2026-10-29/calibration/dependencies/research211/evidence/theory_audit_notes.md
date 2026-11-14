# Theory U and inherited calibration audit

## Result

The unary theory report contains a substantive conventional mathematical argument
for mutual interpretation of U and PA and for PA-verifiable finite-refutation
translations. I found no concrete mathematical flaw in its dependency chain during
this audit. This is not a formal verification: neither an exported PA derivation nor
a kernel-checked Lean/Rocq/MM0 endpoint is provided for this U construction.

The most important reporting distinction is that the released 212-state machines
do not directly execute the positive dyadic theorem stream introduced in the unary
report. They inherit an older native numerical calculus D_U, with truth 0, falsity
1, seven logical rows, an additional dominated propositional row, modus ponens,
generalization, and the gated U214 covering bundle. Its bridge to U/PA is a separate
mathematical dependency and must be retained.

## Unary-theory proof checked

Sources: `sources/extracted/pa_unary_power_cover/pa_unary_power_cover/sections/`
(`unary_core.tex`, `unary_arithmetic.tex`, `upper_transport.tex`).

The legal schema requires FV(phi) subset {x}. It supplies only a weak cover:

    forall a exists b [forall x (x in b -> phi(x)) and
                       forall x (Sub(x,a) -> (phi(x) -> x in b))].

It does not permit source a as a free parameter of phi. It does not assert ambient
extensionality, exact powers, unrestricted separation, or arbitrary common bounds.

The lower interpretation uses coextensionality with saturation at all places where
membership in the first argument needs a congruence. Its numerical predicate has
hereditary strict linear order and endpoints for intersections with every existing
ambient object. This is a definable first-order predicate, not external finiteness.

The crucial dependency order is valid on its face:

1. False matrix yields empty objects. Numerical local facts supply predecessors of
   nonempty numbers without asserting total successor.
2. For unary Q, filter failures at source n. The least failure inside n has a
   predecessor; if there is no failure inside n, use n's own predecessor. This
   derives induction before successor existence. The formula
   Q(v)=forall p (BaseAndStep(theta,p) -> theta(v,p)) internalizes arbitrary
   parameters legally.
3. Induction yields comparison and least numerical tuples modulo coextensionality.
4. A globally least failing numerical tuple can be bound inside a unary matrix.
   With explicitly proved invariance and bounded support, the weak cover therefore
   supplies exact numerical comprehension at that tuple, contradiction.
5. Apply this to successors and numerical powers. These supply bounded saturated
   singleton/pair/ordered-pair objects and numerical graph comprehension.
6. Canonical histories quantify the old history as a bound variable, avoiding an
   illicit free graph parameter. Pointwise uniqueness comes before graph extension.
   This yields total addition/multiplication and the PA recursion equations.

The upper interpretation is binary membership E(x,a)=Bit(a,x). Sub(x,a) implies
x<=a, so for each fixed arithmetic matrix PA induction constructs the relevant
finite bitset. This also validates the stronger parameterized weak-cover theory.
The proof is formula-by-formula; it does not invoke a uniform truth predicate.

`upper_transport.tex` and `unary_arithmetic.tex` provide the necessary syntactic
uniformity argument: substitution, freshening, finite tuple formulas, graph
translations, and proof concatenation are primitive recursive; structural and
proof-length induction verify the transforms in PA. Thus the report is claiming
PA |- Con(U) <-> Con(PA), not merely an external semantic equiconsistency.

## Positive-interface distinction

`positive_interface.tex` and `emitter.tex` show a separate positive system with
atomic target q0 and seed not D, D=forall v E(v,v). The positive theory alone has a
one-object total-relation model, so its ordinary consistency is not calibrated.
The calibrated assertion is nonderivability of q0, or consistency after adding
not D. The raw unrestricted generator plus not D is linked to W+IR by two exact
low-code collisions and padding/freshening transformations. These arguments are
relevant theory context but do not by themselves verify the older literal TM.

## Actual machine bridge

The 212 reports explicitly identify D_U and retain the 213 direct-transfer parent.
The direct parent is extracted for this audit at
`work/theory_audit/direct_parent/U213_ConPA_2026-10-28/`.
The U214 dependency is at
`work/theory_audit/u214/U214_ConPA_Reduction_2026-10-28/`.

In U214 `proofs/role_emitter.tex`, matrix/output label a, source b, tested c are
used with gate c!=a,b. The regular case a!=b gives W covering; the coincidence
a=b makes the subset guard equivalent under IR to emptiness. An empty source
therefore supplies the needed witness. Truth 0 and false 1 aliases are treated
explicitly. Completeness pads a desired matrix to n>1 and chooses (a,b,c)=(n,0,1),
then projects the bundle and restores names. Atomic vacuity is also retained.

The direct parent `proofs/source_transport.tex` binds the exact copied 774-primitive
U214 emitter into the ST215 control structure. It explicitly does not substitute
Con(PA) into the already established fixed K215 theorem.

The direct parent `proofs/startup_suffix.tex` is essential. Blank startup reaches
source ordinal 136 after 48,140 literal steps, with store
(N,T,W,A,D,H,X,Y,L)=(1,0,13,0,0,1,0,0,1). This matches 141 source steps from the
interior seed at ordinal 106 with W=4. The incoming cache 1 is an arithmetic
parameter and is not claimed theorem-valued. The suffix yields nine actual
theorem heads above opaque tail 4; it does not start at an ordinary clean root.

The all-natural credit proof assigns S=-1, MP=0, AX=+10 and proves the scheduler
suffix starting at candidate 1 has debt at most 2. Nine explicit heads leave
margin 7, so the unsafe tail never becomes top/cache. A ghost explicit list length
is necessary because Cantor pairing has P(0,0)=0. The report handles that alias.
The cofinal strong compiler works above arbitrary underlying stacks once AX
clears counter/cache; this preserves completeness after the finite startup.

## Appropriate endpoint statement for a new local reduction

If a new table M is shown by a PA-formalizable finite-block simulation to preserve
halting of the selected U212 parent, state that theorem first. Compose it with the
retained numerical/source and unary-theory proofs to obtain the intended endpoint:

    PA |- not Halt(M,blank) <-> Con(U) <-> Con(PA).

Explain that the new local theorem is universal / invariant-backed as appropriate,
while the complete consistency endpoint inherits the exact named mathematical
dependencies. Do not call Python case enumeration an exported PA or kernel proof.
Finite run checks are implementation evidence and cannot establish nonhalting.

## Possible theory-level research directions

No immediate theory alteration discovered here is a proved state saving. Dropping
the gate or the bundled atomic-vacuity clause needs a new logical completeness
argument; simply observing that U has only one schema does not justify deletion.
Compiling the positive dyadic emitter could ultimately remove logical/arithmetic
overhead, but that would replace the current source architecture and its startup,
so its nine polynomial multiplications are not evidence of a smaller binary TM.

A local literal-table reduction is currently the least disruptive path because
it can retain all the delicate source and theory obligations unchanged.
