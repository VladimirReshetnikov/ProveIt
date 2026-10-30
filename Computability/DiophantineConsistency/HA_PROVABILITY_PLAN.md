# HA provability of the current consistency equations

The owner strengthened the goal on26 October2026: prove in Lean both the
current Diophantine equivalence and that the equivalence is provable in
intuitionistic Heyting Arithmetic (HA). The owner then clarified that a
Lean proof that an HA proof EXISTS is sufficient. There is no requirement
to print, normalize, serialize or enumerate a literal HA proof certificate.
This supersedes encoded ZFC derivation as the primary remaining target.
Equation-size reduction, frequent detailed commits and normal fast-forward
synchronization with origin/main continue.

## Current status, 29 October 2026

For the maintained 14-variable equation in `equation.pdf`, the HA
proof-existence target is **complete**: the unconditional theorem
[`ha_current_iff_consistency`](Lean/DiophantineConsistency/HACurrentEquation2011.lean)
establishes an HA derivation of both implications between absence of a
positive solution and the formal ZFC consistency sentence. This is not a
proof of either side separately. The same file also has a closed Lean IΣ₁
proof-existence endpoint. See the later 28 October entries for the
construction and its axiom audit.
That checked endpoint is snapshot evidence: later upstream merges changed
ZFC interpretation modules reachable from it, and
`ArithmeticConstructionAssembly` was subsequently changed. A dependency-aware
current-source replay is still needed. This qualification
does not identify a defect in the previously checked theorem.
The 27 October estimate and earlier checkpoint descriptions below are
historical, not the current status. The strengthened active objective also
requires a Lean proof of PRA provability. The [PRA plan](PRA_PROVABILITY_PLAN.md)
records why the external Parsons-theorem argument is not yet such a Lean
proof and identifies the missing formal interfaces.

For the smaller 13-variable, 87-operation adaptive candidate, the
[unconditional model theorem](reviews/adaptive-unconditional-equivalence-independent.md)
now proves both directions between no zero and no represented machine halt in
every IΣ₁ model, with local normalization discharged. A separately checked
[`HAExpressionAssembly`](Lean/DiophantineConsistency/HAExpressionAssembly.lean)
turns an appropriate all-model bridge into an actual HA derivation of the
equivalence to ordinary ZFC consistency. The two providers have shared paths
with differing compiled objects; a focused integration and fresh replay have
since checked the HA client as described below. A complete current-source
provenance audit remains. The model equivalence alone is not an HA
proof-existence theorem.

A prior rough estimate of 70–85% concerned the 87-operation proof architecture
before the focused HA builds described below. It is not a time estimate or a
measurement of the remaining source-provenance work. The 14-variable HA
theorem itself is complete on its checked snapshot,
subject to the current-source replay qualification above.

The exact 87-operation HA client has passed an 83-module author build and a
fresh independent build; its endpoint checks report only `propext`,
`Classical.choice`, and `Quot.sound`. The author reused a prefix whose
transitive imported-object environment was not fully authenticated: 15
intermediate object or dependency hashes differ from the fresh build. The
fresh build's provenance is being audited; both retain pinned historical HA
and `ZF` objects and inherited package ancestry. See the
[author receipt](reviews/ha87-focused-pinned-zf-author-pass/README.md).

A later zero-reuse 85-module author build has a matching
[isolated-source independent replay](reviews/ha87-isolated-peer-pass/README.md):
all source, direct-input, object and full-log hashes agree. This is evidence
for its frozen pre-merge snapshot. Subsequent workspace source changes require
a new current-source rebuild, and the historical HA, ZF, Foundation and
transitive package ancestry remain inherited.

A newer 86-operation direct-ordinate candidate now has a Lean theorem, with
matching author and independent scoped replays, that its fixed-port no-zero
sentence is equivalent to the 87-operation candidate's no-zero sentence in
every IΣ₁ model. See the [independent receipt](reviews/adaptive-direct86-fixed-equivalence-independent.md).
Subsequent upstream merges changed source modules in that theorem's dependency
chain, so this is checked snapshot evidence, not a current-source replay.
The 86 branch has since been rebuilt on the historical 87-operation machine
provider. The [independent compatibility replay](reviews/adaptive86-machine-compat-rebase-v6-independent.md)
checks its fixed-port no-zero equivalence with represented-machine nonhalting
in every IΣ₁ model. It inherits the historical machine provider and uses six
private additive helper declarations and two private supports, with extra
imports in the relevant clients; it is not a full current-source closure. That machine theorem
alone does not supply the ZFC bridge or an HA or PRA proof-existence theorem.

An exact 86-operation HA client and its independent extension replay have
compiled 27 modules and checked a theorem asserting existence of an HA
derivation of the equivalence to ordinary Foundation ZFC consistency. Both
extensions use the original 87 author provider, whose reused prefix has the
transitive-environment gap described above. A separate 27-module extension
against the fresh 87 peer has now passed its author build and a matching
independent replay, both with final audits. A later upstream merge changed
guarded dependencies, so this is checked snapshot evidence. Historical HA,
ZF, Foundation and package provenance remains inherited. See the
[86 author receipt](reviews/ha86-focused-extension-author.md).

## Exact target and established results

Progress estimate on 27 October 2026: **roughly 40–60% of the full HA
proof-existence target**. This is a judgment about the remaining mathematical
work, not a measured fraction of completed files or a delivery-time estimate.
The HA calculus, PA-to-HA proof translation and several relevant formula
normalization results are established. The full arithmetic equivalence
needed by the transfer theorem remains open. Work was organized around
three substantial connections: actual ZFC/source-checker proof interpretation,
actual control-to-tape simulation, and internal polynomial/Pell witness
assembly. The actual checker/runtime equivalence now has independently
accepted closed IΣ1 and PA proof-existence theorems below. The other two connections
remain substantial, including internal binary population, mask/word/carry
and tableau construction in the polynomial connection.
The checked scheduler/control halting theorem, literal tape/boot theorem
and relaxed auxiliary norm theorem below are completed parts of those
connections. Tagged Collection, register-box execution, symbolic execution
and half-index recovery have since passed independent review
below. No closed Lean
theorem yet asserts that the full equivalence has an HA proof.

The estimate remains **about halfway**, with substantial uncertainty. The
completed HA calculus, PA-to-HA translation and consistency normalization
do not remove the need for a closed arithmetic theorem about this exact
equation. The source/ZF interpretation and simultaneous polynomial witness
construction still require mathematical development; they are not merely
final file assembly. Machine simulation has now passed complete composition
and its closed arithmetic proof client. This estimate counts neither proof
files nor independently replayed checkpoints as equal units of progress.

The [internal binary population package](reviews/arithmetic-binary-population-root.md)
now supplies total fixed Sigma1/Delta1 population graphs and proves binary
recurrences, arbitrary internal block concatenation and complement weights
in every IΣ1 model. Zero widths/values and leading-zero blocks are included.
Independent fresh pairs match both objects, complete logs and all fourteen
standard-only reports, with zero refresh. Exact carry/no-overlap tests,
mask weights, binomial extraction and actual tableau interpretation remain.
The reviewed [integer half-binomial route](reviews/arithmetic-half-binomial-population-route-root.md)
replaces real estimates by finite integer comparisons; its new represented
power, Pascal and factorial proofs remain explicit work.

The [actual auxiliary seed](reviews/arithmetic-pell-auxiliary-seed-root.md)
now constructs five positive f,i,T,u,y from only internal a,R with
R%4=3, including a=0. Both oriented residues modulo f*f and c, the
literal T identity and the additive auxiliary norm are derived by two
genuine Sigma1 phase inductions and exact quotient arithmetic. Independent
fresh pairs match both objects, complete logs and all five standard-only
reports, with zero refresh. Simultaneous outer/source witnesses and the
full converse remain; no final HA equivalence is inferred from this seed.

The [concrete current radix client](reviews/arithmetic-carrier-radix2011-root.md)
now recovers the represented power and actual width94517 radix from the
same maintained positive or natural split zero. No norm, port, index,
power or radix premise is supplied. The positive internal block count L
remains distinct from coordinate v9, and the residual exponent may be
zero. Independent fresh pairs match both objects, complete logs and all
eight standard-only reports, with zero refresh. Internal population,
mask/word/carry/tableau interpretation and converse witnesses remain.

The [literal carrier soundness theorem](reviews/arithmetic-carrier-soundness2011-root.md)
now derives all five additive equations from the actual positive splitNatural
zero in every IΣ1 model. It binds the original signed cuts, applies all four
negative-unit exclusions, derives transport and only then justifies natural
rank/tau subtraction. Actual port bounds and the one positive-domain shift
are proved. Independent fresh pairs match both objects, complete logs and
all five standard-only reports, with zero refresh. Power/radix composition
is supplied above; binary population, actual mask/word/carry/tableau
interpretation and simultaneous converse witnesses remain before full HA.

The [internal radix alignment theorem](reviews/arithmetic-radix-alignment-root.md)
now derives a positive block count, q=exp(d*N), the exponent bound and the
exact remaining factor exp(R-d*N) from the actual exponential factorization.
No binary-radix or exponent-divisibility oracle is supplied. Independent
fresh pairs match both objects, complete logs and eight standard-only
reports, with zero refresh. The concrete width94517 client is supplied above; no
native word or final polynomial equivalence is inferred from this generic
arithmetic result.

The [closed checker/machine theorem](reviews/arithmetic-checker-machine215-root.md)
now supplies actual IΣ1 and PA proofs of one fixed sentence equating the
actual History222 refutation predicate with the literal decimal215 halting
sentence. Its all-model realization retains Type0 exactly where required
by the forward compiler. Independent fresh pairs match both objects,
complete logs and six standard-only reports, with zero refresh. This
discharges the runtime proof-existence connection; the actual ZF/ZFC source
and polynomial connections remain before the final HA equivalence.

The [actual transitive source certificates](reviews/validator-seed-transitive222-root.md)
now construct raw and guarded tagged transitive containers and exact tagged
pairs, with actual Proof(seedTheory) codes and fixed Sigma1 formula graphs.
The same full-seed witness is retained, and arbitrary parameters, repeated
labels and U=t remain. Independent fresh pairs match both objects, complete
logs and all 17 standard-only reports, with zero refresh. Guarded profile
code laws, Eqv/Member, QHyp, quotient/WF and uniform ZF/ZFC calibration remain.

The [complete actual215 runtime theorem](reviews/arithmetic-runtime215-root.md)
now proves both directions between actual Enum live(0,4,0) halting and
first-projection halting of the literal decimal215 blank machine, with
arbitrary internal clocks in every IΣ1 model. The supported Sigma1 relation,
all simulation premises, exact seed graph, full halted payload and accepted
95,714-step boot are discharged. Independent fresh pairs match both objects,
complete logs and all 15 standard-only reports, with zero refresh. The
closed checker/machine IΣ1/PA client is supplied above; actual source ZF/ZFC and
polynomial/population/tableau/witness connections still precede full HA.

The [direct squared-ordinate seed](reviews/arithmetic-pell-squared-seed-root.md)
has passed independent source review and fresh replay. In every IΣ1
model it derives a positive strong-norm witness at the explicit index
`R*ycoord R a`: internal two-step quotient induction proves the original
ordinate squared divides this new ordinate. This avoids generic internal
finite pigeonhole for the displayed fourteen-variable strong seed. It
supplies the strong seed used by the accepted auxiliary construction above;
it does not yet construct all simultaneous outer/source witnesses or
establish the complete converse. The independent 105/30-line pair matches
both objects, complete logs and four standard-only reports with zero
prerequisite refresh. ROOT authored the pair; the independent controller
replay and ROOT acceptance reauthentication are recorded separately.

The [canonical215 control-frame theorem](reviews/arithmetic-control-frame215-root.md)
now fixes the represented entry graph, proves full consumed-path rebasing
and derives actual six-case step/halt transport with arbitrary internal
registers and zero gaps. Both independent objects, complete logs and all
20 standard-only reports match, with zero refresh. Whole iteration,
the initial frame and boot composition are supplied by the accepted
runtime theorem above; no final polynomial PA or HA equivalence is claimed.

The [internal signed-factor extraction](reviews/arithmetic-signed-pairs-root.md)
now turns an actual scaled five-factor signed product into five positive
additive identities, using four negative-unit exclusions and deriving the
transport factor's sign. It handles arbitrary internal representatives and
cancellation without an integer quotient. Independent fresh pairs match
both objects/full logs and all seven standard-only reports with zero refresh.
The literal binding and actual norm exclusions are applied by the accepted
carrier soundness theorem above; its remaining polynomial bridge is explicit.

The [concrete logical source images](reviews/validator-seed-logical-images222-root.md)
now supply all five actual equality axioms, literal irreflexivity and GIC
in one discharged moving-marker image contract. Its concrete source
refutation-to-seed theorem has no image oracle; the actual checker witness
adds IΣ2. Independent fresh pairs match both objects/full logs and all
fifteen standard-only reports, with zero refresh. Tagged transitive
containers are supplied above; profile Eqv/Member, quotient/WF and ZF/ZFC
calibration remain.

The [internal negative-norm exclusions](reviews/arithmetic-negative-norms-root.md)
now prove the required modulo-four and consecutive-factor sign obstructions
in arbitrary IΣ1 models. Genuine bounded internal descent handles the
consecutive factor, retaining the n=1 counterexample and both inverse-root
orientations. Independent fresh pairs match both objects/full logs and
all seven standard-only reports, with zero refresh. Signed-product and
literal polynomial binding are supplied by the accepted soundness theorem above.

The [actual215 source-site theorem](reviews/arithmetic-site215-root.md)
now derives all six instruction execution cases from actual LeafAt membership
and the complete closed 4,751-site certificate. Internal data and zero gaps
are arbitrary, clocks are positive, and full path/register suffixes remain.
The terminal predicate is first(configuration)=0. Independent fresh pairs
match both objects/full logs and all nineteen standard-only reports with
zero refresh. Canonical consumed-path rebasing, the represented frame and
whole control/tape calibration remain before PA/HA assembly.

The [internal power-recovery theorem](reviews/arithmetic-pell-power-recovery-root.md)
now derives `X = Exp.exp R`, the represented exponential graph and
`Exp.exp R < Y` from the literal transport/four norms and genuine port
bounds. Both Pell indices are derived. A fixed Sigma1 comparison and a
nonnegative quotient avoid arbitrary-base exponentiation or signed modular
oracles. Independent fresh pairs match both objects/full logs and all nine
standard-only reports with zero refresh. Concrete internal ports, actual
polynomial-zero extraction and simultaneous cofinal witnesses remain before
PA/HA assembly.

The [actual recognized GIC image theorem](reviews/validator-seed-gic-images222-root.md)
now discharges `AxiomImages gicTheory V`, including arbitrary internal
recognizer closure counts. The matrix is relativized before swapping its
slots; genuine Sigma1 induction closes the changing-marker family. Its
Type0 model boundary matches the reused syntax API and suffices for the
proof-existence completeness route. Independent fresh pairs match both
objects/full logs and all twelve standard-only reports with zero refresh.
Finite axiom images, quotient/Member/WF and actual ZF/ZFC calibration remain.

The [actual215 Home theorem](reviews/arithmetic-home215-root.md) now supplies
positive internal execution of the real Home checker, including zero gap,
empty true runs and the exact eighteen-step boundary for every right tail.
Its stepper and executor discharge Home semantics and preserve the moved
flag, retaining the genuine fallback premises. Independent fresh pairs
match both objects/full logs and all 14 standard-only reports with zero
prerequisite refreshes. All-site instruction contracts are supplied above;
canonical paths and whole control/tape equivalence remain open.

The [literal scalar-window and first-index theorem](reviews/arithmetic-pell-first-index-root.md)
now derives the bounds needed for half-index recovery from the maintained
fourteen-field data, additive transport identity and port bounds. The actual
four additive norms yield both Pell indices, `2*n = R+1`, and the positive
omitted quotient in `k = R+1+4*E*Y*h`. Independent fresh pairs match both
objects/full logs and all five standard-only reports, with zero prerequisite
refreshes. Power recovery is supplied above; concrete internal ports,
extraction of the norms from polynomial zero and cofinal witnesses remain
before PA/HA assembly.

The [changing-marker derivation transport](reviews/validator-seed-marker-relativization222-root.md)
now handles all ten actual internal derivation constructors, using genuine
Sigma1 bounded-budget induction and explicit source axiom images. Its
falsum endpoint composes the accepted marker discharge; the IΣ2 endpoint
then supplies an actual checker refutation witness. Independent fresh pairs
match both objects/full logs and all 15 standard-only reports, with zero
prerequisite refreshes. The GIC component is supplied above; the remaining
source images and ZF calibration still precede the ZFC-to-checker bridge.

The [actual215 symbolic executor theorem](reviews/arithmetic-symbolic-core215-root.md)
now interprets the real checker oracle, every symbolic step and successful
executor runs over arbitrary internal arithmetic data. It preserves the
moved flag and derives positive clocks from an initially false flag.
Normalization preserves the entire numeric configuration, and all four
ordinary-Nat sepsR/sepsM/INC/DEC algebraic clients are proved. Independent
fresh pairs match both objects/full logs and 15 standard-only reports,
with zero prerequisite refreshes. Home and sites are supplied above; canonical paths
and whole control/tape equivalence remain open.

The [actual tagged Collection theorem](reviews/validator-seed-tagged-collection222-root.md)
now constructs genuine source Proof certificates for arbitrary internally
typed binary matrices and free parameters, with exactly Empty(t) and t in a
as source antecedents. It retains tagged global support with an unrestricted
input witness and coverage for tagged inputs in a. The arbitrary-matrix step
uses actual source equality replacement. Three fixed total syntax graphs
bind the matrix, body and conclusion. Independent fresh pairs match both
objects/full logs and 13 standard-only reports. The actual GIC schema image
and uniform recognizer closure are supplied above; the remaining source
images and quotient/WF/ZF/ZFC calibration remain open.

The [actual half-carrier index theorem](reviews/arithmetic-pell-half-index-root.md)
now derives the main Pell pair at the literal rank from the actual norms,
signed residues and explicit large-ordinate/half-window bounds. Exact odd
coordinate division and represented Sigma1 induction retain alternating
signs under both moduli; no modular inverse or square-root cancellation is
used. The literal adapter handles either sign by absolute difference and
uses the full scaled strict coefficient. Independent fresh pairs match both
objects/full logs and ten reports. Deriving the scalar bounds from the
literal data, the first-index identity, powers and cofinal witnesses remains
before final polynomial/PA/HA assembly.

The [changing-marker discharge theorem](reviews/validator-seed-marker-discharge222-peer.md)
now removes every internally sized domain side set and its negative empty
marker guard from an actual residual source derivation. The family shift
law, genuine Sigma1 induction, actual inhabited-tag and empty-object proofs
yield a source falsum proof, including counter zero. It uses no shift-fixed
domain assumption. Independent fresh pairs match both objects/full logs
and 14 reports. The preceding arbitrary-derivation interpretation and
actual source axiom images, quotient/WF and ZF/ZFC calibration remain open.

The [actual215 register-box theorem](reviews/arithmetic-register-boxes215-root.md)
now proves marking, increment, zero decrement and positive decrement for
all nine physical registers with arbitrary internal data and positive
execution clocks. INC appends one spare; positive DEC retains its extra
left bit. The zero branch alone needs an existing spare. Fixed PR graphs
and genuine Pi1 induction in IΣ1 handle internal scan and spare counts.
Independent fresh triples match all three objects/full logs and 14 reports.
One unchanged numeric-prefix helper was explicitly refreshed; no Foundation
module was rebuilt. The later symbolic packet above supplies the ordinary-Nat
encoding comparison and executor. Home and sites are supplied above; control/tape composition
remain open.

The [actual relaxed auxiliary norm theorem](reviews/arithmetic-pell-index-divisibility-root.md)
now supplies the original-base Pell coordinates and both p|m and c|m for
the same positive internal index. Genuine Sigma1 quotient induction and
two scaled natural coefficient certificates derive the latter divisibility;
no cubic-congruence or power theorem is required. The structural helper
retains zero indices. Independent fresh pairs match both objects/full logs
and seven reports. The [mathematical note](research/arithmetic-pell-two-certificates.md)
records the shorter proof. The later half-index packet above proves the
target-index step with explicit scalar bounds. Their derivation, first-carrier
alignment, cofinal witnesses and final equation/PA/HA assembly remain open.

The [actual relaxed-norm integral-solution theorem](reviews/arithmetic-pell-integral-solution-root.md)
now forces the common-unit index multiple from actual positive norm and
large-c inputs, then restores m>0, p|m, f=X_m(a) and
i*c*c=delta(a)*Y_m(a). Independent fresh pairs match both objects/full logs
and five reports. The later index packet above supplies c|m and the complete
relaxed auxiliary implication. Subsequent index recovery and cofinal witness
construction remain to be proved.

The [internal Pell strong-divisibility theorem](reviews/arithmetic-pell-strong-divisibility-root.md)
now derives the sequence gcd, index-divisibility reflection including0 and
the arbitrary-scale common-divisor consequence. Norm certificates and a
bounded Sigma1 Euclidean descent prove the actual represented identities.
Independent fresh pairs match both objects/full logs and seven reports.
The later integral-solution packet above supplies large-c index forcing;
final c|m and full relaxed integrality remain to be proved.

The [internal common-unit theorem](reviews/arithmetic-pell-common-unit-root.md)
now derives the shared base and two positive internal indices from the
actual norm and proves both represented composition identities by Sigma1
induction. Independent fresh pairs match both objects/full logs and four
reports. The later strong-divisibility theorem above supplies sequence gcd;
large-index forcing, cubic congruences and full relaxed integrality remain.

The [internal gcd normalization theorem](reviews/arithmetic-gcd-normalization-root.md)
now constructs a fixed total unique Sigma1 gcd graph by least positive
natural coefficient certificates, then derives the actual relaxed-norm
common-discriminant factors. Independent fresh pairs match both objects/full
logs and eight reports. The later common-unit packet above combines it with
KnownUnit and represented sequence composition. Strong divisibility and
full integrality remain to be proved.

The [actual internal guarded-comprehension theorem](reviews/validator-seed-guarded-comprehension222-root.md)
now constructs genuine source Proof certificates for raw pairs, two-root
and guarded comprehension over arbitrary internal matrices/free parameters.
The guarded endpoint has only Empty(t) as antecedent and retains U=t.
Five fixed total raw syntax graphs and all capture-safe binders are checked.
Independent fresh pairs match both objects/full logs and22 reports.
The later Collection packet above extends it. Marker-safe proof transport,
actual schema-image/recognizer binding, quotient/WF and ZF/ZFC calibration
remain to be proved.

The [actual internal augmented comprehension theorem](reviews/validator-seed-raw-comprehension222-root.md)
now constructs a genuine source proof for arbitrary internal unary matrices
and free parameters. It preserves full member closure, branch overlaps and
all binder shifts, with actual Proof certificates and fixed total raw syntax
graphs. Independent fresh pairs match both objects/full logs and11 reports.
The later guarded packet above extends it. The parameter-safe marker,
Collection and quotient route still precedes actual ZF/ZFC calibration;
no source-model premise is substituted.

The [bounded marker-counter proposal](research/validator-seed-marker-counter-proposal.md)
describes a possible all-internal transport invariant with marker index j,
domain side-set length j and a fixed induction budget. It tracks ALL at j+1
and SHIFT at j−1, followed by simultaneous marker/domain discharge. This is
a mathematical proposal with six inspected source pins, not a Lean theorem
or compiler authorization; actual tagged and quotient axiom images remain.

The [actual215 tape/boot theorem](reviews/arithmetic-machine-tape215-root.md)
now represents continuation of the literal decimal evaluator, proves every
sparse row on arbitrary internal tape halves, and composes all13 boot chunks
at the exact95714 clock. The same fixed Sigma1 graph lifts the finite boot;
both internal blank/boot halting directions include the early-halt exclusion.
Independent fresh pairs match both objects/full logs and13 reports.
The later scan/box/Home/site packets above supply uniform instruction
execution; canonical and whole control/tape calibration remain open.

The [actual internal scheduler/control halting theorem](reviews/arithmetic-dag-runtimeperm222-root.md)
now composes repeated execution in both directions using a fixed Sigma1
relation and derived positive clocks. It retains arbitrary internal data
and the exact pointer0/candidate4/zero-work seed. Independent fresh triples
match all objects/full logs and11 standard-only reports. Its generic
transport is the single explicitly approved unchanged-source refresh.
The literal215 tape/site/boot/clock simulation, actual source-ZFC calibration
and internal polynomial witness transformations remain before PA/HA assembly.

The [internal known-unit theorem](reviews/arithmetic-pell-known-unit-root.md)
now implements the bounded least-unit search and Sigma1 descent for an
arbitrary positive discriminant with one known positive solution. The same
derived base/scale classifies every internal solution, including ordinate0.
Independent fresh pairs match both objects/full logs and four standard-only
reports. Internal gcd/common-discriminant construction, composition and
strong divisibility remain before full relaxed integrality.

The [actual internal DagPerm root](reviews/arithmetic-dag-rootperm222-root.md)
now constructs the whole execution at every internal boundary and proves
exact scheduler agreement with pointer/candidate progress. Its actual
equality123,156-atom AX word and complete dispatch retain zero/collision
cases. Independent fresh builds reproduce both objects/full logs and13
standard-only reports. The later runtime theorem above composes repeated
runs and positive clocks; literal215 tape/site/boot/clock simulation remains.

The [internal Pell residue classes](reviews/arithmetic-pell-residue-classes-root.md)
now derive full arbitrary-index plus/minus classes, the signed doubled step
with2p≤m, and odd-index witnesses in every IΣ1 model. The local growth gap
is guarded by n≥2; the excluded target0/base2 collision is proved separately.
Independent fresh pairs reproduce both objects/full logs and15 standard-only
reports. Strong integrality, Qh identities, first/main carrier indices,
cofinal simultaneous witnesses and final PA/HA assembly remain open.

The next arithmetic route is documented in the
[bounded known-unit proposal](research/arithmetic-pell-known-unit-next-plan.md)
and [gcd normalization derivation](research/arithmetic-pell-gcd-normalization-note.md).
A known positive unit bounds a finite least-unit search. Elementary gcd
normalization then puts both relevant norm solutions over one discriminant,
potentially replacing the external squarefree/fundamental-unit setup.
The known-unit descent, gcd normalization and common-unit composition are
now proved above, along with strong divisibility and large-index forcing.
The final c-divides-index argument is also proved above by two coefficient
certificates; later target-index recovery and cofinal witnesses remain.

The [uniform internal seed-source basis](reviews/validator-seed-source-basis222-root.md)
now constructs the exact represented open proof of every internally typed
full-seed body,with total raw constructor graphs and actual closed-instance
recognition. Genuine source proofs provide empty objects,singletons and a
joint empty marker with an inhabited tag. Independent builds reproduce both
objects/full logs and17 reports. The [reviewed source route](research/validator-seed-tagged-interpretation-plan.md)
still needs guarded comprehension/Collection,explicit marker transport and
the genuine QHyp quotient/WF interpretation before ZF/ZFC calibration.

The [actual internal DagPerm macros](reviews/arithmetic-dag-macros-perm222-root.md)
now supply concrete run witnesses for pairing,unpairing,reads,all13 AX atoms
and fetch, using the accepted actual control table and physical register file.
The rotated fetch loop is proved with genuine Sigma1 iteration. Independent
fresh builds reproduce both objects/full logs and22 standard-only reports.
The later root theorem above constructs its whole structured execution;
the repeated-run halting bridge and literal machine simulation remain.

The [actual internal first-norm theorem](reviews/arithmetic-pell-first-norm-root.md)
now classifies every x²=1+Q(Q+1)k² solution in the represented sequence,
deriving doubledness, bounded internal time and2Q/4Q residue quotients.
It descends by the literal unit(2Q+1,2), justifies natural subtraction and
uses genuine Sigma1 order induction. Independent builds reproduce both
objects/full logs and eleven reports. First/main index identification,
cofinal simultaneous witnesses and full equation PA/HA assembly remain.

The [current13/88/51 finite certificate](reviews/adaptive-current13-metrics-root.md)
now covers the accepted literal graph at its exact current47,313-byte tuple:
every paid/live gate, all specialized leaders, exact degree51 and complete
coefficient reconstruction. The external Lean ConZFC endpoint is already
closed. This promotes a current-tuple size comparison without a new Lean
build or kernel totalDegree theorem; its internal PA/HA endpoint remains open.

The [internal Pell reflection/period package](reviews/arithmetic-pell-periodicity-root.md)
now supplies both nonnegative quotient witnesses after any internal number
of4n periods, actual model remainders and first-window residue injectivity.
It uses genuine Sigma1 induction and justified subtraction, including the
n=0/modulus1 case. Independent builds reproduce both objects/full logs and
ten standard-only reports. The later residue-class and first-norm packets
above extend this checkpoint; simultaneous carrier witnesses still remain.

The [actual internal DagPerm/p215 bisimulation](reviews/arithmetic-control-bisim-perm215-root.md)
now compares both represented control runs with arbitrary internal register
files and time witnesses. All2,850 entries,45 blocks and both bounded branch
successors are checked, including complete reserved/high-bit bounds.
Independent fresh builds reproduce both objects/full logs and eleven reports.
This removes the actual control-program comparison; structured checker
dispatch and literal215 machine/tape/boot/clock simulation still precede
the final PA premise and its HA transfer.

The [actual p215 control catalogue](reviews/arithmetic-control215-table-root.md)
now binds all4,751 packed rows to the actual179-node program and supplies
represented IΣ1 run/specification laws. Independent builds reproduce both
objects and all nine axiom reports. ROOT authenticates the complete frozen
evidence without a third compile. The next runtime obligations are actual
DagPerm/p215 bisimulation, structured execution and literal machine/tape
calibration; this catalogue theorem does not supply the final PA premise.

The [concrete full-seed source theory](reviews/validator-full-seed-theory222-root.md)
now has a fixed Delta1 recognizer, genuine internal Pi2/IΣ2 universal closure,
and discharged AxOK for equality,irreflexivity and the full seed schema.
The actual source interpreter maps its internal falsum proofs to History222
value2. Independent replay matches both objects/full logs and13 standard-only
reports. The tagged-domain marker/guard/quotient interpretation and actual
ZF/ZFC proof calibration remain required before the PA-to-HA assembly.

The [internal Pell residue/index package](reviews/arithmetic-pell-congruences-root.md)
now gives actual quotient and remainder certificates,4Q transport under
the explicit first-index identity, arbitrary norm-solution residues and
strict index order/uniqueness. All indices are internal IΣ1 elements.
Independent replay matches both objects/full logs and nine standard-only
reports. Further carrier/index and simultaneous witness construction is
still required before the actual equation/ConZFC PA theorem.

The [current literal adaptive equivalence](reviews/native-adaptive-current2011-root.md)
now closes both external consistency equivalences for the13-input graph
at the exact current ports, including the once-shifted high coefficient.
Independent fresh replay matches both objects and ten axiom reports.
This supplies another exact polynomial endpoint for later internalization;
it does not supply the required PA derivation or HA proof-existence theorem.
No specialized metric/frontier promotion or displayed-equation edit is made.

The [actual whole DagPerm table](reviews/arithmetic-dag-controlperm222-root.md)
now has kernel-checked catalogue equality for all4751 rows and unconditional
root occurrence at entry1,fuel488. Independent fresh PackedTables/main/
Checks replay reproduces all objects and12 standard-only reports. This
discharges the table/occurrence boundary, while structured interpreter
execution,p215 control/site/tape simulation and the final HA theorem remain.

The [internal Pell classification](reviews/arithmetic-pell-classification-root.md)
now proves the stated Pell norm iff a represented internal index<=y,
uniformly over all IΣ1 models. Descent justifies natural subtraction and
the bounded-universal invariant has an actual Sigma1 certificate.
Independent builds match both objects and six standard-only reports.
This closes solution classification for base b+2/discriminant(b+1)(b+3);
carrier congruences,index restrictions and cofinal witness construction
still precede the final PA-to-HA equation theorem.

The [adaptive canonical converse](reviews/native-adaptive-canonical-root.md)
now turns every positive Carrier65 zero into a positive zero of the literal
adaptive graph, retaining full PortBounds and deriving all private witness
signs and the actual first-index quotient. Independent builds match both
objects and six standard-only reports. This external existence map does
not yet specialize the current ports or internalize the arithmetic in PA/HA.

The [actual full-seed source image](reviews/validator-source-full-seed222-root.md)
now gives the literal closure-and-root-request body a current C222 history
witness for every internally typed matrix, arbitrary free environment and
free-safe output stream. Independent builds agree on both objects and17
standard-only reports. The actual schema recognizer/parameter closure,
tagged Collection and quotient interpretation still precede a fixed
source-ZFC AxOK/calibration theorem and the final HA transfer.

The [internal Pell recurrence](reviews/arithmetic-pell-recurrence-root.md)
is represented uniformly over arbitrary IΣ1 models, with fixed total
Sigma1/Delta1 graphs and actual Sigma1 induction for its norm,growth and
addition identities. Independent two-leaf replay matches both objects
and nine standard-only reports; all95 Foundation prerequisites are reused.
This begins the required internal number-theoretic construction. It does
not yet classify Pell solutions or supply the carrier congruences and
cofinal witnesses needed by the final PA-to-HA assembly.

The [literal adaptive graph](reviews/native-adaptive-graph-root.md)
now binds the smaller construction's88 binary gates to its four cuts and
proves complete positive source reconstruction from a graph zero. An
independent pair reproduces both objects and eight standard-only reports;
a separate literal text audit passes normal/optimized Python and rejects
220 actual corruptions. This is an external integer/natural theorem. Its
canonical converse,current specialization and internal arithmetic proof
remain separate; the displayed equation's HA endpoint is still open.

The [internal register loops](reviews/arithmetic-dag-loops-root.md)
now supply actual current DagPerm subroutine proofs at arbitrary internal
counters, with a nonvacuous represented occurrence check. Independent
six-prerequisite/two-leaf builds match every object and pass eight
standard-only reports. The whole actual table/occurrence and exact215
simulation remain necessary before the closed arithmetic runtime bridge.

The [actual C222 equality-image theorem](reviews/validator-equality-images222-root.md)
now discharges AxOK for the actual finite equality recognizer, with all
five closed source images and a literal Eind-only irreflexivity image.
Independent builds pass25 standard-only reports and identical objects.
This removes a concrete theory-specific premise; the substantial remaining
set-theory/schema images and fixed source-ZFC calibration are still required.

The [adaptive source reconstruction](reviews/native-adaptive-source-restoration-root.md)
now derives all31 positive source coordinates and all22 literal rows from
the smaller construction's four positive cuts. Independent builds pass
five standard-only reports with identical objects. This is an external
integer/natural theorem; whole graph binding,the canonical converse,current
endpoint composition and the separate PA/HA internalization remain open.

The [bounded even seed-label theorem](reviews/validator-seed-padding222-root.md)
now provides actual seed and matrix-vacuity witnesses for arbitrary internal
typed matrices using a bounded even self-label and odd binder stream.
Independent builds pass eleven standard-only reports with identical
objects. This discharges the stated self-label freshness construction;
it does not yet interpret tagged comprehension/Collection or discharge
the fixed source theory's complete AxOK premise.

The [actual C222 source-proof interpreter](reviews/validator-source-derivation222-root.md)
now translates all ten internal Foundation derivation cases under an
explicit AxOK theory-image premise. Genuine Pi2/IΣ2 induction covers
arbitrary internal codes and contexts. Independent builds pass seventeen
standard-only reports with identical objects. The generic logical kernel
is complete; actual source-axiom images,including the substantial tagged
seed/set-theory construction,remain necessary for the fixed ZFC reduction.

The [adaptive Mersenne recovery](reviews/native-adaptive-mersenne-root.md)
now supplies the binary-radix conclusions from the smaller equation's
positive cuts and actual width identity, including3∤q,q∣X and a positive
power of radix2^94517 with94517*N≤R.toNat. Independent builds pass
eight standard-only reports with identical objects. This external integer
arithmetic theorem does not itself internalize the polynomial/Pell proof
in PA or HA; complete source restoration and the converse also remain open.

The [actual C222 source quantifier contexts](reviews/validator-source-quantifier-context222-root.md)
now lift GEN/ALL/EXS through arbitrary internal contexts with actual
checker witnesses. Typing and fresh_resources discharge every source
hypothesis's required vacuity. Independent builds pass23 standard-only
reports with identical objects. This supplies the quantifier steps for
the next ten-case internal proof induction; its axiom-image premise and
the substantial source set-theory interpretation remain separate work.

The [actual C222 checker/enumerator equivalence](reviews/arithmetic-enum-soundnessperm222-root.md)
now has genuine closed IΣ1 and PA proofs, with both directions between
actual checker falsity and halting from pointer0,candidate4,work0. Its
Sigma1 invariant retains bounded certification while live and an actual
falsity witness after halt. Independent builds pass twelve standard-only
reports and identical objects. This closes the proof-state/scheduler link;
actual source-ZFC,exact215 and internal polynomial/Pell calibration remain
required before the PA-to-HA assembly.

The [actual C222 NNF-negation theorem](reviews/validator-source-negation222-root.md)
now supplies both checker-witnessed implications for every internal typed
source formula and arbitrary encoder states. Its explicit Pi2 invariant
uses IΣ2 code induction. Independent builds pass sixteen standard-only
reports with identical objects. This discharges source negation compatibility;
quantifier transport through internally sized contexts,full derivation
induction and source-axiom calibration remain separate work.

The [actual C222 local preservation theorem](reviews/arithmetic-command-preservationperm222-root.md)
now retains bounded proof certificates across every successful command and
extracts an actual History222 value2 witness at halt. Independent two-leaf
replays agree byte-for-byte and pass eight standard-only reports. The next
reverse-enumerator invariant is Sigma1: a halted state retains its falsity
witness, while a live state retains a certified working code. This still
requires scheduler induction and does not supply source-ZFC, exact215 or
polynomial calibration.

For each selected literal polynomial P, the intended endpoint is a Lean
theorem asserting `HA.Proves equivalenceSentence`, with `HA.Proves` meaning
existence of a finite derivation using intuitionistic first-order logic,
the usual arithmetic axioms and the full first-order induction schema.
`HA.Proves` is now defined in [HAProofs](Lean/DiophantineConsistency/HAProofs.lean)
and independently checked. The particular `equivalenceSentence` and its
completed provability theorem remain targets.

The sentence must express, in arithmetic, that P has no positive integer
solution iff the actual sealed-ZFC proof predicate has no refutation.
Use P(x+1) on natural variables, represented as equality of two natural
polynomials, for the positive-domain side. The ZFC side must be an actual
arithmetization of the repository's proof convention, not an uninterpreted
atom named ConZFC. A primitive-recursive function-language extension would
need a proved conservative elimination into conventional HA.

The external Lean equivalence is already closed for the maintained
14-positive/65-operation/degree150 equation and the three accepted
13-positive forms, in
[CurrentPositiveZero2011](Lean/DiophantineConsistency/CurrentPositiveZero2011.lean).
The current scaled auxiliary replacement is also covered by
[CarrierScaledAuxiliary118](Lean/DiophantineConsistency/CarrierScaledAuxiliary118.lean).
Their independent endpoint replays and axiom reports are documented in
the [formalization plan](LEAN_EQUIVALENCE_PLAN.md). A source-authenticated
361-module custom dependency validation has passed at the pinned09eaa
snapshot:191 fresh and170 authenticated reuses. A separate15-command
post-merge refresh also passed; see the
[original replay](reviews/current-positive-zero2011-closure-replay.md) and
[limited refresh](reviews/current-positive-zero2011-refresh-replay.md).
Neither is an HA proof-existence theorem.
The later13-source upstream merge also passed a separately scoped
[94-command refresh](reviews/ha-postmerge-refresh-20261026.md), with191
standard-only reports and353 authenticated reused objects. It includes
the maintained and mixed-carrier endpoints, and preserves the twelve
explicit unchanged-client reuse boundaries.

The [first-norm auxiliary correction](research/thirteen-first-norm-correction92/README.md)
now gives13 positive variables,84 operations and exact degree92. Either
sphere equation first forces P=1, so the correction vanishes; every
positive assignment is retained in both directions. Independent fresh
Lean builds pass eight standard-only reports, and complete normal/optimized
finite audits verify the two leading cancellations and all fixed ports.
See the [root acceptance](reviews/thirteen-first-norm-correction92-root.md).
This trades nine operations for four degrees against13/75/96. Its external
ConZFC equivalence is checked; the HA endpoint remains open.

The [complete normalized product](research/fourteen-normalized-product106/README.md)
now supplies14 positive variables,67 operations and degree106 with the
unchanged current ports. The exact scaled identity and positive delta
preserve every positive zero. Two independent fresh current-source builds
pass six standard-only reports; normal/optimized complete finite audits
verify the full degree, all paid operations and all47313 coefficient bytes.
See the [root acceptance](reviews/fourteen-normalized-product106-root.md).
Its external ConZFC equivalence is checked; its HA endpoint remains open.

The current-port mixed-carrier13-variable variants at72/124 and74/122
also have checked entire-positive-zero maps and closed external ConZFC
equivalences. Their [independent replay](reviews/thirteen-lv-carrier122-root.md)
passed16 standard-only reports, with separate complete finite metric checks.
Their HA proof-existence endpoints remain open alongside the maintained page.
The grouped-square13/77/96 variant likewise has a checked external endpoint
and exact positive identity map to LV72; its
[root replay](reviews/thirteen-grouped-squares96-root.md) retains the separate
finite metric and cached-prerequisite scopes. Its HA endpoint is also open.
The shared-residual13/76/96 presentation is now externally checked too:
it computes exactly the grouped polynomial using one fewer operation.
Its [independent replay](reviews/thirteen-shared-squares96-root.md) passed
eleven standard-only reports and separate complete normal/optimized finite
metric checks. Its HA proof-existence endpoint remains open.
The unit-sphere13/75/96 form now has its own externally checked entire
positive-zero equivalence, preserving all witnesses while changing the
polynomial. Its [independent replay](reviews/thirteen-unit-sphere96-root.md)
passed13 standard-only reports and complete separate finite metrics.
Its HA endpoint remains open alongside the other selected forms.

[ObjectCurrentEquation2011](Lean/DiophantineConsistency/ObjectCurrentEquation2011.lean)
supplies a set-theory-language no-solution sentence with exact arbitrary-model
positive-domain semantics. That work is retained, but the new HA target
needs an arithmetic sentence and intuitionistic derivability. No further
ZF-model-only completion is required merely to satisfy the new goal.

The arithmetic equation sentence is now supplied by
[ArithmeticCurrentEquation2011](Lean/DiophantineConsistency/ArithmeticCurrentEquation2011.lean).
Its `unsolvabilitySentence` compiles the exact current fourteen-variable
successor-shifted expression into the ordinary `0,S,+,*` language. All four
complete coefficient ports are actual compact binary numerals, not free
symbols. Exactly fourteen universal binders close the no-zero formula.
The generic compiler has exact semantics over every commutative semiring;
its natural-number interpretation is precisely no positive integral zero
of the displayed polynomial. Three fresh leaves and ten standard-only
axiom reports passed [independent review/replay](reviews/arithmetic-expression-lean-peer.md).
This binds the equation side. The arithmetic ZFC-checker sentence and the
HA equivalence derivation remain open.

[HADeduction](Lean/DiophantineConsistency/HADeduction.lean) now composes
actual finite HA proofs by concatenating their supporting axiom lists.
[HANegativeStability](Lean/DiophantineConsistency/HANegativeStability.lean)
constructs intuitionistic stability proofs for negations, conjunctions and
universals, with the full context shifted at universal introduction.
Four leaves passed [independent replay](reviews/ha-deduction-stability-lean-peer.md)
and sixteen reports using only `propext` and `Quot.sound`.

[HAEquationStability2011](Lean/DiophantineConsistency/HAEquationStability2011.lean)
binds this to the literal current sentence: HA proves `¬¬NoZero → NoZero`.
Its derivation has an empty context and an empty arithmetic axiom list.
Both leaves passed [independent replay](reviews/ha-equation-stability2011-lean-peer.md)
and four standard-only reports. This proves a particular logical property
inside HA. It does not prove NoZero itself or the consistency equivalence.
In particular, double-negation stability alone does not identify a formula
with its full Gödel–Gentzen translation. The translation comparison for
the complete no-zero/consistency equivalence remains to be proved.

## Two viable proof routes to audit

One route proves, within HA, both positive-witness implications:

```text
an actual coded ZFC refutation -> a positive zero of P;
a positive zero of P -> an actual coded ZFC refutation.
```

Negating these implications yields the requested consistency equivalence
intuitionistically. There is no need to extract a refutation from a double
negation of consistency. A new external witness interface can first expose
the existing arithmetic constructions directly from a supplied refutation,
avoiding the current convenience wrapper's classical double-negation step.
That interface alone will not constitute an HA formalization.

A second route proves existence of a PA derivation and applies a verified
Gödel–Gentzen translation plus HA equivalence to the original sentence.
This may avoid reconstructing every external proof in intuitionistic form.
The desired no-witness statements suggest a negative arithmetic formulation,
but the exact translation/stability obligations must be proved for the
chosen proof-checker formula and equation sentence. A standard-number Lean
iff does not itself provide the required PA derivation. Classical Tarski
validity alone likewise does not establish intuitionistic derivability.

The Foundation library already has the first-order Gödel–Gentzen theorem
in Lean, as well as the Coq port. The small
[FoundationTheoryGG](Lean/DiophantineConsistency/FoundationTheoryGG.lean)
adapter now lifts it to finite theory assumptions, preserving the actual
translated axiom list. Both leaves passed an
[independent fresh replay](reviews/foundation-theory-gg-root.md), with59
prerequisite modules authenticated against their v4.32 build traces.
Arithmetic axiom and induction preservation, syntax interoperability and
the particular target's stability remain separate obligations. See the
[existing API audit](reviews/ha-existing-foundation-api-audit.md).
An existence theorem via general proof translation is acceptable: no
expanded derivation for the enormous fixed integers must be displayed.

## Concrete foundational checks

- `PAHF.PASyntax` has reusable arithmetic syntax and induction axioms, but
  its proof calculus has unrestricted excluded middle. It is PA, not HA.
  The existing type-valued bounded-PA proof trees likewise contain LEM.
  Removing LEM must be explicit in a genuine new derivability relation;
  erasure into PA is only a one-way validation.
- `HAProofs` now supplies that relation: sixteen intuitionistic deduction
  rules with capture-avoiding quantifier side conditions, a finite list of
  conventional arithmetic axioms, and full formula induction. Its
  [author receipt](reviews/ha-proofs-author.md) and
  [independent replay](reviews/ha-proofs-lean-peer.md) record ten axiom
  reports and authenticated reuse of five prerequisite modules. This
  defines genuine HA theoremhood; it is not yet the desired HA theorem.
- The shallow `PA.Model` has induction for every Lean predicate. An
  argument using that stronger semantic bundle must not be mislabeled
  validity in every first-order PA model. Formula-instance induction and
  ordinary external induction are different interfaces.
- `PAHF.PASyntax` is a large monolithic dependency. Any reused object must
  have authenticated source/toolchain provenance. A small independently
  namespaced arithmetic calculus is preferable to pretending a partial
  source extraction is that accepted module.
- Standard Lean axioms in an external audit do not identify which HA
  induction instances or proof rules justify the arithmetic argument.
  Conversely, classical reasoning in the Lean METATHEORY is allowed when
  proving existence of a genuine HA derivation; it must not be silently
  inserted as an HA object-language rule.

## The machine calibration needs its own arithmetic audit

The literal715-digit machine is linked to refutations through
[KEndpoint215](../BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean) and
[KEndpoint](../BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean).
The current lower chain is not presented as a direct ZFC proof checker:
`c222_of_zf_refutation` uses C222 semantic completeness, the seed/model
construction and `zf_consistent_of_formSeed`. The final ZF/ZFC transfer
uses `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

These are valid external Lean interfaces at their recorded scope. Their
proofs do not automatically establish arithmetic provability of this
calibration. There is, however, substantial completed internal arithmetic
machinery: `ZFCinPA.ValidatorConsistencyEquivalence` proves the validator
consistency equivalence in IΣ₂ and PA; `LSchema` already supplies internal
ZF/ZFC Choice transport; and `BinaryConsistencyRotation240` proves the
consistency equivalence for the exact represented Rotation240 binary
machine in IΣ₂ and PA. Reuse these results rather than reconstructing them.

The remaining comparison concerns the actual215 table and boot seed,
the changed C222 calculus, and the distinct coded proof conventions.
The user-specified `k225-formal/verification/k215/README.md` explicitly
separates its external endpoint from an internal PA theorem. Its215
candidate counter starts at4; the represented240 validator uses different
startup data and the older254 calculus. No definitional rewrite between
these has been found in the inspected sources. Existing represented
lookup and positive-clock simulation frameworks are useful interfaces,
but their exact215 contracts must be proved. The
[constructive/source audit](research/ha-current-equation-constructive-audit-20261026.md)
records these concrete differences and the searched scope. This is an
open comparison obligation, not a claim of unprovability in HA.

The exact215 graph/step/run specialization is now checked in
[ArithmeticMachineRun215](Lean/DiophantineConsistency/ArithmeticMachineRun215.lean).
The bounded transition graph is compiled from the actual typed decimal table,
not a replacement machine. Its primitive-recursive run is total and unique
at every time of every IΣ1 model, and agrees with the actual whole-tape run
at ordinary natural times. IΣ1/PA prove the closed run-totality sentence;
the closed halting sentence has the exact standard interpretation.
Eight fresh leaves passed [independent root replay](reviews/arithmetic-machine215-root.md)
with24 standard-only reports and124 authenticated cached prerequisites.
The sole decoder change narrows one import; a separate two-leaf regression
retains the external equation endpoint. This is not a full closure refresh.

The [C222 audit](research/ha-c222-internalization-audit.md) gives the missing
all-model witness equivalence explicitly: exact215 halting iff the old C254
history checker accepts falsity. It separates represented C222 checking,
internal logical/seed calibration and actual counter4 runtime simulation.
The changed equality leaf now has a checked
[C254 adapter](../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorGrowG222.lean):
for every internal a,b,c in every IΣ1 model it constructs an actual old-checker
proof code for the literal `growG` formula. Its Sigma0 graph agrees with the
actual C222 definition. Seven fresh main/check/prerequisite commands passed
[independent root replay](reviews/validator-growg222-root.md), with ten
standard-only reports and114 authenticated cached prerequisites. The changed
seed bundle still requires additional internal syntactic interpretation work.
Its literal helper-free syntax now also has checked
[bounded circuits](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticSeedTemplates222.lean)
for req/clos/nks/vrel/bundle222, with exact Nat bindings and arbitrary-internal
IOpen graph correctness. Two leaves passed [independent root replay](reviews/arithmetic-seed-templates222-root.md)
with16 standard-only reports and102 authenticated cached prerequisites.
The repeated matrix/binder c, false code1 and legal a=b,c=0 case are retained.
These are representation results; they do not prove the seed internally valid.
None of these missing statements is supplied by standard-Nat simulation.

The actual calculus now has a checked
[Nat proof checker](../BusyBeaver/Lean/BusyBeaver/ZFC/Code222Proof.lean),
including `C222 n ↔ ∃code, check222 code n=true`. Old raw-tree parsing and
quoting are reused as syntax; new recursive validity and conclusions bind
both changed leaves and MP to the actual C222 definitions. Its
[independent replay](reviews/code222-proof-root.md) passed nine reports.
The [bounded row](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticRow222.lean)
then represents exactly those numeric rule semantics in every IOpen model,
with arbitrary-child standard parser agreement and invalid-tag rejection.
Its [independent replay](reviews/arithmetic-row222-root.md) passed ten reports.
Neither packet assumes old C254 semantic agreement for the changed calculus.

[ArithmeticSequenceHistory](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticSequenceHistory.lean)
separately reuses Foundation's generic primitive recursion. Its fixed
history/value syntax has Sigma1/Delta1 graphs, unique totality, exact
sequence length and all-index lookup equations in every IΣ1 model,
conditional on an explicitly represented total step. Both totality
statements retain that premise. Its
[independent replay](reviews/arithmetic-sequence-history-root.md) passed15
reports. Actual C222 instantiation, whole-code Nat binding, internal seed
calibration and exact counter4 runtime simulation are the next obligations.
These three packets total six fresh leaves over pinned cached prerequisites;
they do not establish the final arithmetic consistency equivalence.

The actual instantiation is now supplied by
[ArithmeticHistory222](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticHistory222.lean).
Its syntax-fixed step graph composes actual div/rem, Cantor projections,
sequence lookups and the C222 row. Child-index bounds make the internal
successor recurrence depend on this evaluator's own preceding values.
It proves represented unique evaluation and an actual closed IΣ1 theorem
of total unique Boolean evaluation, by existing arithmetic completeness.
The [independent replay](reviews/arithmetic-history222-root.md) passed both
new leaves and14 standard-only reports over118 cached prerequisites.
Whole-code Nat agreement with the literal decoder is still separate, as
are the logical seed and exact-runtime consistency calibrations. Total
evaluation alone proves neither acceptance soundness nor HA equivalence.

The [all-code Nat adapter](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticHistory222Nat.lean)
now proves exact agreement with the actual decoder/checker for every code,
including malformed inputs, by strong induction generalized over parser fuel.
It defines no duplicate evaluator and imports old History254 only for generic
div/rem/numeral facts. It binds actual C222 derivability to a witness for the
same fixed represented formula. Both leaves passed
[independent replay](reviews/arithmetic-history222-nat-root.md), with eight
standard-only reports over120 cached prerequisites. Internal seed and exact
runtime calibration remain open; the represented formula now has its actual
whole-code standard interpretation.

[ArithmeticProofConstructors222](../BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticProofConstructors222.lean)
now supplies all twelve actual rule-node evaluation equations at arbitrary
internal IΣ1 inputs. It uses the new history recurrence, actual growG and
helper-free seed with exactly c≠a,b, including rejected collisions. Its
[independent replay](reviews/arithmetic-proof-constructors222-root.md) passed
both leaves and15 standard-only reports over119 cached prerequisites.
The represented CProv222 logical interface and subsequent seed/calculus
interpretation remain separate work.

[ValidatorProvability222](../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorProvability222.lean)
now provides the fixed Sigma1 represented CProv222 predicate, actual
new-constructor witnesses, and finite Lukasiewicz/Kalmar logic. Its Nat
interpretation is exactly actual C222. The
[independent replay](reviews/validator-provability222-root.md) passed both
leaves and ten standard-only reports over122 cached prerequisites. GrowG
is the actual changed equality rule; rho7 is not assumed. The encoded
calculus's classical logic is separate from HA's intuitionistic proof rules.
The [internal equality core](reviews/validator-equality-core222-root.md)
now derives reflexivity, the helper and specialization, rho7 from growG,
and membership vacuity from the gated seed. Both leaves pass independent
compilation and eight standard-only reports over123 cached prerequisites.
Semantic seed interpretation and runtime remain open.

The [arithmetic translation audit](research/ha-arithmetic-translation-adapter-audit.md)
also fixes the next proof-transfer interface: translate Foundation ordered
arithmetic syntax into the existing conventional PAHF HA, then map actual
intuitionistic proofs. Translated equality/arithmetic axioms and arbitrary
induction require explicit HA derivations. Reuse the existing GG recursion;
do not identify its translated axiom theory with conventional HA by naming.
For the literal universal negative equality, a direct syntax comparison can
remove the translation; arbitrary negative formulas require more than the
already proved double-negation stability.

The syntax portion of that adapter is now checked in
[FoundationPAHFSyntax](Lean/DiophantineConsistency/FoundationPAHFSyntax.lean).
It translates the actual ordered arithmetic symbols into PAHF `0,S,+,*`,
using a capture-avoiding existential definition of strict order. Generic
environment substitution/rewriting and the exact canonical binder,
instantiation, free/open and eigenvariable-shift identities are proved.
Both leaves passed [independent root replay](reviews/foundation-pahf-syntax-root.md)
with15 standard-only reports; all369 source/trace/object pins for the59
Foundation and five PAHF cached prerequisites matched. This is a syntax
checkpoint, separate from arithmetic-axiom transfer.

The logical proof-calculus map is now checked too:
[FoundationPAHFLogic](Lean/DiophantineConsistency/FoundationPAHFLogic.lean)
maps actual intuitionistic Hilbert proof trees to `HA.Derives []`, and actual
finite-context proofs/proof existence to `HA.Derives (Γ.map formula)`.
The concrete intuitionistic endpoint discharges the generic extra-axiom
premise using HA's ex-falso rule; it contains no arithmetic-image assumption.
All shifted quantifier contexts and ordered/duplicate assumptions are
retained. Both leaves passed [independent root replay](reviews/foundation-pahf-logic-root.md)
with14 reports using only `propext` and `Quot.sound`, with67 authenticated
cached prerequisites. Conventional arithmetic axioms, induction and sentence
closure still require their own derivations and comparison.

The first conventional arithmetic derivations are now checked in
[HABasicArithmetic](Lean/DiophantineConsistency/HABasicArithmetic.lean):
equality rules, all six arbitrary-term instances of the actual HA axioms,
safe closure opening/reclosing, and the actual formula-induction rule.
The module uses that induction rule to prove0+t=t and proves t+1=S t
from the addition axioms. Nested/free-parameter checks passed
[independent root replay](reviews/ha-basic-arithmetic-root.md), with19
reports using only `propext` and `Quot.sound`. Seven cached prerequisites
were explicitly reused. Further semiring/order axioms and their translated
induction/parameter closures remain separate work.

The conventional arithmetic library now also includes
[HAAdditiveArithmetic](Lean/DiophantineConsistency/HAAdditiveArithmetic.lean)
and [HAMultiplicativeArithmetic](Lean/DiophantineConsistency/HAMultiplicativeArithmetic.lean).
They derive the semiring identities using HA formula induction and explicit
HA equality chains. Their four-leaf [independent replay](reviews/ha-semiring-arithmetic-root.md)
passed36 reports using only `propext` and `Quot.sound`, with eight/nine cached
prerequisites reused for the two respective pairs. These are actual HA
proofs, not equalities supplied as proof-transfer hypotheses.

[HANaturalCases](Lean/DiophantineConsistency/HANaturalCases.lean) proves
`t=0 ∨ ∃z t=S z` by actual formula induction. Its
[independent replay](reviews/ha-natural-cases-root.md) passed11 reports.
[HAEqualityDecidable](Lean/DiophantineConsistency/HAEqualityDecidable.lean)
then proves `∀x∀y (x=y ∨ ¬x=y)` by one formula induction and the predecessor
split, with arbitrary-term instances and full context shifts through
existential elimination. Its [independent replay](reviews/ha-equality-decidable-root.md)
passed14 reports. Both packets use only `propext` and `Quot.sound` (or no
axioms); equality decidability supplies no general excluded-middle rule.
Translated Foundation arithmetic axioms, induction and the final target
comparison still require explicit derivations.

The first concrete translated-axiom checkpoint is now proved in
[FoundationHAArithmetic](Lean/DiophantineConsistency/FoundationHAArithmetic.lean).
Each of the eight semiring equation axioms has an actual
`HA.Proves (FoundationPAHFSyntax.sentence PeanoMinus.Axiom.<name>ᴺ)` endpoint.
Constructive double-negation introduction precedes universal closure;
the fixed source list's membership and every literal syntax image are
checked. No arithmetic-image predicate or desired-provability hypothesis
is supplied. Its [independent replay](reviews/foundation-ha-arithmetic-root.md)
passed22 reports using only `propext` and `Quot.sound`, with88 cached
prerequisites. All76 Foundation records exactly match the already accepted
arithmetic215 inventory. Equality-theory cases, nine order/geometric axioms,
arbitrary induction and the source's parameter closure remain separate.

[FoundationHAEquality](Lean/DiophantineConsistency/FoundationHAEquality.lean)
now discharges every actual source equality-theory axiom's literal GG image,
including all four functions and both relations. HA's proved equality
decidability supplies equality-specific stability; order congruence transports
the whole double-negated existential formula without order decidability.
The source's implication conversion reuses the actual Foundation theorem and
checked intuitionistic proof map, retaining its metatheoretic choice dependency.
Both leaves passed [independent replay](reviews/foundation-ha-equality-root.md),
with31 reports restricted to the standard three Lean axioms.

[FoundationHAClosure](Lean/DiophantineConsistency/FoundationHAClosure.lean)
proves the exact identity between the actual source `univCl` GG image and
`closeN φ.fvSup (formula φᴺ)`. A proved canonical-environment identity covers
all `fixitr` counts, including counts below a sparse free variable. Its HA
proof constructor closes an actual proof of the open body, using genuine
universal introduction. The [independent peer replay](reviews/foundation-ha-closure-peer.md)
passed both leaves and six standard-only reports. This closes the parameter
closure comparison; the arbitrary induction body, nine order/geometric
axioms and final target equivalence still require proofs.

[FoundationHAInduction](Lean/DiophantineConsistency/FoundationHAInduction.lean)
now proves the actual GG image of every unrestricted Foundation induction
instance. Its open body uses actual HA formula induction, distinct zero
and successor substitutions, full-context shifts and genuine equality
transport for x+1=Sx under arbitrary nested formulas. Exact source closure
then gives the closed schema member. Both leaves passed
[independent replay](reviews/foundation-ha-induction-root.md), with30
standard-only reports; all85 cached Foundation records match the already
accepted arithmetic215 inventory. No image-provability premise remains.

[FoundationHAOrderBase](Lean/DiophantineConsistency/FoundationHAOrderBase.lean)
also proves the literal zeroLtOne and zeroLe GG images, with a constructive
arbitrary-term zero/predecessor proof and the exact negative disjunction
encoding. Its [independent peer replay](reviews/foundation-ha-order-base-lean-peer.md)
passed both leaves and ten reports using only `propext` and `Quot.sound`.
The [Additive and Witnesses packets](reviews/foundation-ha-order-witnesses-root.md)
now discharge addEqOfLt, addLtAdd, oneLeOfZeroLt and ltTrans too. Ordinary
HA derivations construct actual predecessors under fully shifted contexts;
the negative images lift those implications while retaining double-negated
order premises. Four independent fresh leaves passed50 standard-only
reports with byte-identical author objects. The
[final three order cases](reviews/foundation-ha-order-final-root.md)
mulLtMul, ltIrrefl and ltTri now pass six more independent builds and53
standard-only reports, also byte-identical to the author. Thus all nine
source order images are discharged. The exact no-zero/consistency target
comparison remains a separate obligation.

[FoundationHATheoryTransfer](Lean/DiophantineConsistency/FoundationHATheoryTransfer.lean)
now constructs the required finite assumption discharge and actual
intuitionistic-theory proof map. Its classical adapter reuses the existing
GG theorem with explicit HA proofs of the source images. The concrete
eight-semiring-axiom corollary has no image-provability premise. Both leaves
passed author and [independent peer builds](reviews/foundation-ha-theory-transfer-peer.md),
with seven standard-only reports and byte-identical outputs. This supplies
proof composition. [FoundationHAPeano](Lean/DiophantineConsistency/FoundationHAPeano.lean)
now discharges every actual PeanoMinus constructor and every unrestricted
induction axiom, giving HA proofs of literal GG images of all actual PA,
subtheory and IΣk derivations without image-axiom premises. Both leaves pass
[independent replay](reviews/foundation-ha-peano-peer.md), with nine reports
and byte-identical objects over112 cached prerequisites (85 Foundation).
The actual source PA theorem of the equation/Con(ZFC) equivalence, the
consistency-predicate comparison and C222 seed/runtime bridges remain open.

[FoundationHANoZero](Lean/DiophantineConsistency/FoundationHANoZero.lean)
now proves both HA implications between the existing compiled no-zero
sentence and an explicit Foundation negative-equation sentence's GG image,
for every Expr(Fin n). It constructs HA equalities for source add-one versus
successor and retains exactly n binders. Both
[independent root leaves](reviews/foundation-ha-nozero-root.md) pass27
reports using only propext/Quot.sound. The [literal current binding](Lean/DiophantineConsistency/FoundationHACurrentNoZero2011.lean)
now proves both HA implications for exactly the original
ArithmeticCurrentEquation2011.unsolvabilitySentence and a concrete
Foundation source with14 binders. Seven independent fresh leaves pass18
standard-only reports. An exact40-declaration ownership move into five
narrow data/syntax modules avoids the conflicting global Matrix.map
imports while preserving original names, ports, expression bodies and
all remaining proof text. Internal hygienic macro names can change, so
affected native clients require their own refresh. Neither comparison
discharges source PA equivalence or identifies the final consistency
predicate with its translated image.

[FoundationHACurrentTransfer](Lean/DiophantineConsistency/FoundationHACurrentTransfer.lean)
now composes the completed maps: an explicit PA proof of the concrete
source equivalence yields both HA implications for the maintained sentence
and the translated target. Its negative corollary concludes not GG(rho).
Two [independent fresh leaves](reviews/foundation-ha-current-transfer-root.md)
pass10 standard-only reports with byte-identical objects over133 reused
modules (85 Foundation). No source PA proof or independent consistency
predicate comparison is supplied by this conditional adapter.

[CurrentWitnessEquivalence2011](Lean/DiophantineConsistency/CurrentWitnessEquivalence2011.lean)
now proves the external direct equivalence between positive zeros and
the literal `BProv ZFCax_s [] Form.fBot`. Its final negation composition
uses no double-negation elimination; imported calibration and arithmetic
are not thereby internalized. See the
[root replay](reviews/current-witness-equivalence2011-root.md).

Two bounded arithmetic prerequisites are now checked:
[NativeFiniteCarry](Lean/DiophantineConsistency/NativeFiniteCarry.lean)
constructs the actual quotient carries by at most `57*card(ι)` iterations
in the current radix47 setting, retaining wraparound and reset identities;
[BoundedPellDivisibility](Lean/DiophantineConsistency/BoundedPellDivisibility.lean)
finds a positive divisible Pell ordinate at index at most m², including
the actual fresh-seed shape. Both main/check pairs passed independent
[root replay](reviews/finite-carry-bounded-pell-root.md), with21 standard-only
axiom reports. Their bounded algorithms are standard-arithmetic results,
not yet HA derivations. The frozen current witnesses were not replaced.

Remaining arithmetic refactorings include replacing real-valued Pell
estimates by denominator-cleared integer inequalities. Under the
PA/negative-translation route, each
refactoring should be justified by its contribution to PA formalization;
surface elimination of `Classical.choice` is not the goal by itself.

The actual internal C222 [relational/equality packet](reviews/validator-eind222-root.md)
now supplies finite quantifier and existential deductions, membership
vacuity, fixed-binder alpha conversion and the indiscernibility relation
with both membership transports. The proofs retain arbitrary internal
IΣ1 values, legal zero/equal labels and the auxiliary-binder collision.
Four independent leaves pass24 standard-only reports with byte-identical
author objects. The [next seed witness](reviews/validator-seed-witness222-root.md)
normalizes both literal negative universals by explicit finite deductions,
then obtains `CProv222(∃k(p∈k))` with numeric label k=Eind(p+1,p).
The two independent leaves pass11 reports, including actual Nat p=0.
This is membership containment, not the full native container axiom or
CP/GIC. No arbitrary proof interpretation, seed semantic soundness or
counter4 calibration follows merely from this witness.

The [canonical-data refresh](reviews/current-equation-narrow-root.md)
also independently rebuilds130 affected native clients, with92
standard-only reports, over285 unchanged authenticated objects and five
independently fresh narrow owners. Its420 selected modules include the
actual consistency/witness endpoints and selected frontier checks. The
full478-module inventory and58 outside modules are distinguished; no
whole Foundation or umbrella replay is claimed.

The [actual internal seed closure](reviews/validator-seed-closure222-root.md)
now supplies empty objects and singletons up to the fixed Eind relation
uniformly in every IΣ1 model. Its two independent builds pass14 standard-only
reports and retain numeric proof witnesses at p=0, legal zero/equal seed
labels and explicit input-binder vacuity. No self-label vacuity is assumed.
The full native container/GIC axioms, arbitrary proof interpretation and
exact runtime calibration remain open.

The [uniform C222 matrix projection](reviews/validator-seed-image222-root.md)
now retains arbitrary internal matrices, including0, without a matrix-
vacuity premise. Explicit finite congruence handles double-negation padding
at fixed roles1/3. Two independent builds pass14 standard-only reports.
Its subset-indexed coverage deliberately retains a free input label; this
is a resource for the tagged-domain interpretation, not full CP/GIC or
the pending general proof translation and runtime calibration.

The [standard-Nat syntax semantics](reviews/foundation-pahf-nat-semantics-root.md)
now identifies the existing GG/syntax map with the original source
sentence's truth in natural numbers, retaining all binder environments.
Two independent builds pass seven standard-only reports. This is a semantic
comparison in Lean, not an HA derivation. The fixed ZFC proof-convention
comparison still needs its provider-cache audit; available old source and
author build reports are kept separate from authenticated objects.

## Next reviewable checkpoints

The [substitution/opening audit](research/c222-substitution-opening-proposal-20261026.md)
narrows the next actual C222 syntax checkpoint to a Π1/IΣ1 induction,
reusing only unchanged term/vector helpers. Exact opening follows from
source substitution and the accepted shift equation. Numeric equality
needs no fresh-stream premise; later interpreted quantifier transport
retains the explicit IΣ2 alpha and vacuity obligations. Stream selection
and arbitrary proof translation are separately scoped.

The [HA bounded quantifiers](reviews/ha-bounded-quantifiers-root.md) now
have actual HA empty/successor laws and decision proofs from the uniform
object-language premise ∀x.dec a. Genuine simultaneous formula induction
preserves arbitrary nested matrices and all ambient parameters. Two fresh
independent builds pass seventeen propext/Quot.sound-only reports. The
next clients are structural bounded-formula decision and the literal
Foundation/GG bounded-syntax comparison, with actual checker normalization
still separately required.

The [uniform actual C222 alpha theorem](reviews/validator-environment-alpha222-root.md)
is now independently checked for all internal typed source codes, with
an explicit Π2 invariant under IΣ2. Both directions retain the same context,
and both have actual numeric checker witnesses. Two fresh independent
builds pass fifteen standard-only reports. Stream selection and source
substitution/opening precede the later arbitrary proof interpretation.

The [HA interval laws](reviews/ha-strict-intervals-root.md) now prove
the empty interval, s<S s and both actual HA implications for
s<S t iff (s<t∨s=t). Two independent fresh builds pass twelve
propext/Quot.sound-only reports. The
[next bounded-quantifier plan](research/ha-bounded-quantifier-next-leaf-audit.md)
retains arbitrary matrices, bound shifts and a literal uniform decision
formula. It also keeps the actual Δ1 fixed-point proof checker distinct
from a syntactically bounded matrix; that normalization remains unproved.

The [HA strict-order decision](reviews/foundation-ha-order-decidable-root.md)
now proves the actual ordinary decision formula and double-negation
stability for arbitrary terms, with capture-safe transport and finite
contexts. Its independent pair passes twelve reports with only propext
and Quot.sound. Together with the existing equality decision, this supplies
atomic resources for the pending bounded-matrix comparison. A literal
HA proof of the actual checker normalization is still required; classical
Δ1 model equivalences do not provide that proof.

The [finite C222 atomic transport](reviews/validator-atomic-transport222-root.md)
is now independently checked: actual numeric proof witnesses transport
typed equality/membership atoms under the same represented context. Both
fresh leaves pass, with13 standard-only reports. The reverse quantifier
premise explicitly follows weq(t,s)→Eind(t,s)→Eind(s,t); no old-context
exchange is assumed. The next uniform source-formula theorem retains an
explicit Π2 invariant under IΣ2 and all cross-body vacuity resources.

There is now a [closed HA consistency comparison](reviews/foundation-ha-zfc-validator-root.md):
HA proves both implications between fixed GG(Foundation ZFC consistency)
and GG(actual C254 validator consistency). The actual validated PA theorem
supplies the proof, so no source-proof premise remains in this checkpoint.
Two independent fresh builds pass eight standard-only reports. This is an
actual HA proof-existence theorem for those two fixed translated sentences;
the current equation and untranslated-checker comparison remain open.

The [represented Eind-context checkpoint](reviews/validator-eind-context222-root.md)
now provides internal IΣ1 projections, cons equivalences, context vacuity
and binder discharge with actual numeric C222 witnesses. Its independent
pair passes twelve standard-only reports. The primitive equality premise
is composed only in the proved weq-to-Eind direction; all four binder
vacuity resources are retained. Uniform alpha and substitution remain open.

The [fixed ZFC sentence binding](reviews/foundation-zfc-consistency-nat-root.md)
now identifies an explicit GG/PAHF sentence's standard-Nat truth with the
actual syntactic ConZFC proposition, including Choice. Two independent
fresh leaves pass eight standard-only reports over the validated410-module
environment. This semantic comparison is unconditional. HA normalization
to an untranslated checker and the current equation's internal equivalence
remain open.

The actual permuted enumerator now also has independent
[fetch/progress](reviews/arithmetic-command-fetchperm222-peer.md) and
[one-command effect](reviews/arithmetic-command-stepperm222-root.md)
replays. Four fresh commands pass20 standard-only reports. The graphs
range over arbitrary internal IOpen inputs and have all-state/all-raw Nat
adapters. The command permutation, AX order, old-counter dominance, actual
growG/bundle222 and zero-versus-successor result convention are explicit.
Scheduler fairness, internal proof invariants and exact215 simulation
remain open.
The [composed enumerator step](reviews/arithmetic-enum-stepperm222-root.md)
is now independently checked as a total internal IOpen graph, with actual
EnumPerm.enumStep semantics on every ordinary state. Its fresh pair passes
eleven standard-only reports. Full represented recursion, scheduling and
proof invariants remain separate checkpoints.
The subsequent [represented full run](reviews/arithmetic-enum-runperm222-peer.md)
now supplies total/unique recursion at every internal IΣ1 time, the
semigroup law, halt absorption and exact actual EnumPerm.run agreement
for all ordinary states/times. Its independent pair passes thirteen
standard-only reports. The next runtime obligations are a draining bound
for individual candidate words, fair reach from candidate4, proof-state
invariants and exact215 simulation.
The [word-evaluator tick](reviews/arithmetic-command-tickperm222-peer.md)
now proves the required internal remaining-word decrease, retaining
separate halt and successful-completion codes. Its independent pair passes
thirteen standard-only reports and binds every raw Nat command to actual
EnumPerm.cstep. The whole-word draining proof is a separate next checkpoint.
The later [whole-word evaluator](reviews/arithmetic-command-runperm222-peer.md)
now proves the drain bound at all internal IΣ1 word codes, total unique
evaluation, and closed IΣ1/PA totality. Two independent fresh builds pass
twenty-one standard-only reports. Its fixed-word pointwise induction does
not quantify universally over changing work states. Execution composition,
fair reach from candidate4 and the proof invariant remain open.

The [73-module consistency refresh](reviews/fixed-consistency73-root.md)
has now passed, including current R2Native, LSchema and the actual
Foundation consistency equivalence. It retains337 cached prerequisites,
all139 Foundation providers,20 standard-only reports and45 existing linter
warnings. This closes the local provider gap; the fixed standard-Nat
sentence binding and current215/222 arithmetic calibration are separate.

The [uniform typed C222 vacuity theorem](reviews/validator-environment-vacuity222-root.md)
now supplies actual represented proof witnesses for every internal typed
formula under explicit environment/binder avoidance. Its Π2 induction uses
IΣ2 and its independent pair passes11 standard-only reports. This closes
the encoder-vacuity checkpoint while substitution, alpha transport and
general proof interpretation remain open.

The [actual permuted-command parser](reviews/arithmetic-command-wordperm222-peer.md)
now has a represented bounded graph in IOpen and agrees with the literal
Nat decoder on every raw input. Its independent two-leaf replay passes
nine standard-only reports. This respects the0/1/2/AX command layout and
y-then-x packing; shifted fetch, full run simulation and fair reachability
from counter4 remain open.

The owner reaffirmed the **HA target** on26 October after discussing PA.
PA may remain an intermediate theory in the already checked proof
translation; existence of an actual HA derivation is the required endpoint.
The [represented C222 formula encoder](reviews/validator-formula-encoder222-root.md)
now has an independent five-source replay with13 standard-only reports.
Its fixed graph and constructor/SHIFT equations hold for arbitrary internal
IΣ1 inputs. Uniform typed vacuity and arbitrary proof interpretation remain
open. The [fixed consistency cache audit](research/fixed-consistency-nat-cache-gap-audit.md)
has authenticated all139 selected Foundation providers and proposes73
local refreshes; that proposal is not an executed consistency proof.

1. Authentic HA derivability and basic arithmetic/induction interfaces are
   checked, with one-way classical embedding and focused binder checks.
2. The literal equation sentence and a fixed Foundation/GG ZFC consistency
   sentence with its exact standard-Nat proof convention are checked.
   Establish the remaining internal coding comparison to the intended
   untranslated refutation checker.
3. Establish the applicable proof-translation/stability theorem or the two
   direct internal witness transformations. Record which remaining native,
   Pell and machine lemmas need PA/HA proof-existence witnesses.
4. Compose a CLOSED Lean theorem asserting existence of an HA derivation
   of the actual equivalence. A desired-provability hypothesis is not a
   completed endpoint.

No HA proof of the current equation's consistency equivalence is claimed
at this checkpoint.
The decimal equation page and all14 distinct unsubscripted unknowns are
preserved. The goal remains active.


## Actual numeric C222 substitution and opening accepted

The [numeric C222 substitution/opening theorem](reviews/validator-environment-substitution222-root.md)
now passes two independent builds with thirteen standard-only reports and
identical objects. Its actual Π1/IΣ1 induction retains total lookup,
repeated/zero labels and the exact qVec binder shifts. Stream selection,
semantic quantifier rules and the complete HA equivalence remain open.

The exact source replacement vector and label-matching invariant are
internal parameters. Opening inserts the interpreted free label into the
bound stack before encode_shift removes the free-environment head. Neither
step assumes a desired CProv transport theorem. The first checkpoint adds
no fresh-stream choice or arbitrary proof translation. Both remain
subsequent explicit obligations.


## Actual C222 evaluation equations accepted

The [actual C222 evaluation laws](reviews/arithmetic-command-evaluationperm222-peer.md)
now identify terminal with any stopped run and prove the exact head/tail
successor equations. Independent review and two fresh builds pass six
standard-only reports with identical objects. These supply the local laws
for the separately developed fair scheduler reach theorem.

Stopped-time uniqueness applies to the absorbing word evaluator only.
The nonzero step branch subtracts one only after its success guard.
The independent preflight corrected one implicit Init omission in a
metadata import list; the original complete closure already contained
that boundary. No source correction or compiler failure occurred.


## Source construction with actual current endpoint

The [ordinary-source construction](reviews/native-ordinary-source-construction-root.md)
now accepts every positive old-z source zero and rebuilds a Carrier65 zero
with the same scalar fields and rank. Two independent builds pass twelve
standard-only reports and identical objects. Actual current-source
existence is externally equivalent to inconsistency; shifted-z/historical
low-degree transfer and the final HA proof remain separate obligations.

These finite algebraic/number-theoretic Lean results are external. They
are not silently imported as PA/HA proof witnesses. Their later internal
coding and actual proof-existence construction remain explicitly required.


## Concrete C222 stream selection and overlap accepted

The [actual C222 stream theorem](reviews/validator-environment-streams222-root.md)
now selects an explicit safe opposite-parity stream and proves relabelling
between arbitrary free-safe starts, including overlapping s/s+2. Independent
builds pass fifteen standard-only reports with identical objects. Semantic
quantifier inference and arbitrary proof interpretation remain open.

The selector resources do not infer safety for an original unsafe stream.
Its actual formula client invokes accepted IΣ2 alpha transport; it does
not introduce a new induction or a new object-language choice rule. The
next checkpoint binds these resources and numeric substitution/opening
to actual source quantifier inference.


## Source-bound ordinary Δ₀ decisions accepted

The [actual Foundation Δ₀ theorem](reviews/foundation-ha-deltazero-root.md)
now proves HA decidability of the ordinary interpretation with arbitrary
term environments. It uses actual bounded syntax and exact binder shifts,
with twelve independently checked standard-only reports. Literal GG
comparison and the actual delta-one checker normalization remain open.

The theorem requires actual DeltaZero syntax. The consistency checker
currently has a delta-one fixed-point representation; identifying it with
an explicit bounded matrix needs further genuine HA comparison proofs.
The next separate leaf compares ordinaryAux with the literal existing
Foundation negative translation, using only these bounded decisions.


## Actual bounded negative-translation comparison accepted

The [bounded ordinary/GG comparison](reviews/foundation-ha-deltazero-gg-root.md)
now proves both HA implications for actual Foundation Δ₀ formulas and
arbitrary term environments. Two independent builds pass nine standard-only
reports. Existential recovery uses the whole bounded existential's actual
HA decision; the literal consistency-checker comparison remains open.

This comparison uses existing Foundation syntax and actual HA derivations.
The next calibration audit must bind the actual proof checker to applicable
syntax, distinguishing syntactic hierarchy witnesses from delta-one model
representations and negative consistency transport from positive Σ1 DNE.


## Actual counter4 fair reach accepted

The [actual C222 fair scheduler](reviews/arithmetic-enum-fairperm222-peer.md)
now reaches every internal candidate at or above its initial counter,
including a start at4, unless an earlier command halts. Two independent
builds pass fourteen standard-only reports and identical objects. The
proof retains a bounded stopped-time witness before enumeration resumes;
compiler/proof-state invariants and exact215 calibration remain open.

The raw candidate for a nonempty shifted word is word-1. The halting-word
client retains its lower bound relative to the starting counter and its
all-working-state halting premise. This does not prove that a checker
certificate already compiles to such a word. The coupled-time induction
never assumes completed scheduler states are absorbing.


## Actual command-tail replacement accepted

The [actual raw-command replacement](reviews/arithmetic-command-replaceperm222-peer.md)
now preserves the permuted command's meaningful arguments and its complete
working-register effect over internal IOpen inputs. Independent builds
pass thirteen standard-only reports with identical objects, including raw0
and literal AX y/x order. Represented append and execution composition
remain subsequent runtime checkpoints.

The new Σ1 graph retains unbounded reconstruction witnesses. Short-command
unused projections may change, so the effect proof explicitly separates
both short tags before discarding those fields. The independent parser
preflight corrected duplicate import bookkeeping only; no Lean source
correction or peer compiler failure occurred.


## Actual finite ALL and opened-quantifier rules accepted

The [finite actual C222 quantifier rules](reviews/validator-quantifier-rules222-root.md)
now prove ALL inference and both opened ALL/EXS body equivalences, retaining
an explicit vacuity guard for hypotheses and deriving it for a shifted
negative source hypothesis. Independent builds pass thirteen standard-only
reports with identical objects. EXS term introduction and general proof
interpretation remain open.

The object calculus here is actual C222, with numeric checker certificates.
It is a component of the later internal proof translation, not itself an
HA derivation of the equation equivalence. The negative source-hypothesis
client matches the literal free/setShift shape of source ALL inference.


## Actual C222 append representation accepted

The [actual C222 append graph](reviews/arithmetic-command-appendperm222-peer.md)
now has all-internal IΣ1 lookup, identity/associativity and totality proofs,
plus actual finite command-list concatenation. Independent builds pass
sixteen standard-only reports with identical objects. The next runtime
checkpoint proves that evaluation of the concatenated words composes.

History index0 is the fixed right word; raw index z builds shifted left
word z+1. The bounded history invariant covers every internal lookup, with
default0 outside it. Actual closed IΣ1/PA totality proof-existence is
separate from the pending execution and compiler contracts.


## Literal shifted-source adapter accepted externally

The [shifted-z source bridge](reviews/native-shifted-source-adapter-root.md)
now proves all22 unconditional row identities and both positive existence
maps at the current ports, deriving old-z>1 from the supplied source itself.
Four independent fresh builds pass eighteen standard-only reports with
identical objects. The historical lower-degree carrier transfer remains
separate; no equation metric or HA endpoint is promoted.

This closes the variable-convention and positive-domain part of the planned
historical transfer. It does not silently convert external finite algebra
into an internal PA/HA proof; that remains a separate coding obligation.


## Finite bounded double-negation inside actual HA

The [HA finite bounded double-negation theorem](reviews/ha-bounded-double-negation-root.md)
now proves both implications for an arbitrary matrix, with no decision
premise. Independent builds pass eight propext/Quot.sound-only reports and
identical objects. Actual hierarchy-one ordinary/GG comparison and the
full HA equation equivalence remain open.

The proof uses the existing real formula-induction axiom and capture-safe
ambient-parameter shifts. Its arbitrary matrix may contain unbounded
quantifiers; only the outer interval is finite. The next literal Σ1
comparison can use this for bounded universal quantification without
assuming a positive Σ1 decision or Markov principle.


## Actual finite C222 existential term rule

The [actual C222 existential term rule](reviews/validator-existential-rules222-root.md)
now constructs the encoded term-instance implication and composes it under
arbitrary hypotheses. Independent builds pass thirteen standard-only
reports with identical objects, including fallback1 and repeated-zero
checks. General source-proof interpretation and the final HA endpoint
remain open.

This discharges the concrete typed-term freshness and vacuity side conditions
using the original stream. The endpoint is actual internal CProv222, not a
new HA derivation. Full source-proof interpretation still needs its own
induction/context encoding and hypothesis invariants.


## Actual internal C222 append execution accepted

The [actual C222 append execution theorem](reviews/arithmetic-command-compositionperm222-peer.md)
now proves exact evaluation composition over all internal words and states,
using a bounded stopped-pair invariant. Independent builds pass thirteen
standard-only reports and identical objects. Halt0 and positive completion
remain distinct. Proof compiler invariants and exact215 calibration remain
open.

A represented pointwise Σ1 time induction keeps left/right/work fixed and
retains a bounded stopped-pair witness. The proof combines actual raw-tail
replacement, word draining, run addition and terminal uniqueness. It needs
no numerical lower bound on append codes and no least stopping time. It is
an internal IΣ1 runtime theorem, not yet the full represented proof compiler
or an HA equation equivalence.


## Signed adaptive first-carrier bootstrap accepted

The [signed adaptive first-carrier theorem](reviews/native-adaptive-carrier-bootstrap-root.md)
now derives integral positive quotient witnesses and the signed Pell-root
bound directly from literal A0, before source restoration. Independent
builds pass five standard-only reports with identical objects. Main-Pell,
rank and power restoration remain open; no lower-degree endpoint is claimed.

This is an external integer theorem on the full generic signed carrier
domain. It does not assume the desired positive source or promote external
algebra into an internal arithmetic proof.


## Actual syntactic Σ1 ordinary/GG comparison accepted

The [actual Σ1 ordinary/GG theorem](reviews/foundation-ha-sigma-one-gg-root.md)
now proves HA equivalence of the literal GG image with double negation of
the ordinary positive formula, for arbitrary environments. Independent
builds pass eleven standard-only reports and identical objects. Fixed ZFC
consistency specialization and the full equation equivalence remain open.

All fourteen actual hierarchy constructors are covered, with the Π0 base
discharged by existing bounded decisions and the bounded universal by finite
DNS. The ordinary positive conclusion remains double-negated. Next specialize
the actual retained provability predicate and normalize its negation; a
proof of the current equation equivalence in PA still remains separate.


## Free-J factor-three cancellation accepted

The [adaptive factor-three cancellation](reviews/native-adaptive-factor-three-peer.md)
now proves q^4 divides t from q^3 dividing Y and q^5 dividing
(4Y(X+1)+3)t, for all signed integers, including q=0 and3 dividing q.
Independent builds pass four propext/Quot.sound-only reports with identical
objects. Its index-difference client is a main-Pell transfer prerequisite;
no new equation endpoint is claimed.

The literal finite geometric inverse and integer remainder modulo3 proof
avoid a false coprimality premise. The q=3,Y=27,X=1,t=81 control shows
that retaining q^5 divisibility would be incorrect on this generic domain.
This remains an external finite algebra lemma, separate from internal HA
proof-existence obligations.


## Actual C222 fixed command blocks accepted

The [actual C222 finite blocks](reviews/arithmetic-command-blockperm222-root.md)
now prove exact cons execution, finite NIP popping, discard, zero-safe
counter loading and AX setup with its real old-counter arguments.
Independent builds pass eighteen standard-only reports and identical
objects. Selection/rule contracts and unrestricted rho8 compilation remain
separate.

The physical AX setup retains u≤a explicitly. The actual checker accepts
unrestricted rho8 parameters, so its later represented uniform compiler
must implement the finite dominated-implication derivation instead of
assuming this guard. No old C254 runtime semantics is imported.


## Four literal adaptive factors exclude negative units

The [adaptive unit-factor theorem](reviews/native-adaptive-unit-factors-peer.md)
now extracts all four factor equalities from the literal signed product1.
Finite modulo4 proofs exclude negative units without assuming factor
positivity. Independent builds pass five standard-only reports and identical
objects. Binding the full historical graph and the final HA endpoint remain
separate.

The generic signed factors retain q^3(q-1) and discriminant a^2+4a+3.
Kernel-checked finite ZMod4 proofs establish each exclusion. The packet
assumes neither A0/A1 nor a restored source, and supplies only the upstream
algebra required by the separate adaptive bootstrap.


## Fixed Foundation ZFC consistency normalization accepted

The [fixed HA consistency normalization](reviews/foundation-ha-consistency-normalization-peer.md)
now proves both HA implications between the retained fixed GG consistency
sentence and HA negation of the ordinary actual positive ZFC-refutation
predicate. Independent builds pass eight standard-only reports and identical
objects. This does not supply the equation/source PA theorem or an internal
comparison with an independently encoded checker.

The literal source is NNF negation of the actual positive Foundation
provability predicate at falsity. Its real Σ1 certificate and exact
empty-environment syntax equality permit the accepted generic comparison
and GG-negation duality to compose inside HA. No positive Σ1 witness is
extracted and no ordinary NNF-negation identity is assumed. Generic closed
free-variable support and ordinary standard-Nat semantics remain separate
support obligations. The decisive current-equation PA derivation is still
a premise of FoundationHACurrentTransfer, not a consequence of this result.

Both first author and independent builds pass, with eight standard-only
reports and identical objects. The independent replay checks455 cached
modules,139 Foundation modules,872 artifacts,57 boundaries and2118 unique
pins before/after; it compiles only the new main/check pair. No full closure
rebuild is claimed. Sources, drivers, input observations, logs, timings and
object hashes are frozen in the linked author/peer records.


## Positive integral adaptive main Pell root accepted

The [adaptive main-carrier bootstrap](reviews/native-adaptive-main-bootstrap-root.md)
now derives a positive integral main Pell root and q^4 dividing the signed
index difference from literal A1 and preceding first-carrier divisibility.
Independent builds pass nine standard-only reports and identical objects.
No restored-source or rank-window premise is assumed. Index bounds, power
recovery and the full lower-degree transfer remain separate.

The exact signed transport is retained; the positive root is derived,
not imposed by absolute value. Free-J factor3 handling is explicit. These
external integer deductions advance the low-degree transfer but are not
automatically proofs about nonstandard internal arithmetic.


## Actual C222 finite leaf contracts accepted

The [actual C222 finite command leaves](reviews/arithmetic-command-leafperm222-root.md)
now construct all nine physical AX selections, exact gate/bundle outputs
and conditional false-target termination under all-top/all-stack contracts.
Independent builds pass eighteen standard-only reports with identical
objects. Direct rho8 retains u≤a; GEN/MP and represented unrestricted rho8
compilation remain subsequent obligations.

No false1 axiom is introduced. The terminator is conditional on an existing
false-target contract, and exact saved-stack restoration supports the later
MP major-premise call at top0 with its minor formula saved.


## Actual C222 GEN/MP execution contracts accepted

The [actual C222 GEN/MP rules](reviews/arithmetic-command-ruleperm222-root.md)
now preserve all-top/all-stack contracts, including GEN at zero/code1 and
both MP false-cache halt branches. Independent builds pass seven standard-only
reports and identical objects. Uniform circuit compilation, unrestricted
rho8 and proof-history correctness remain open.

The major MP call retains its precise saved-stack input; the physical AX
old-counter arguments are derived from execution. These finite runtime
contracts do not by themselves construct a represented proof-word history.


## Generic ordinary support and Nat semantics accepted

The [ordinary predicate syntax/semantics theorem](reviews/foundation-pahf-ordinary-semantics-root.md)
now proves actual closedness and arbitrary-premodel valuation independence,
plus exact ordinary interpretation over Nat. Independent builds pass eight
standard-only reports and identical objects. The fixed consistency specialization is accepted below; the
equation/source arithmetic proof remains open.

Free-variable support is proved for arbitrary environments, with capture-safe
lowering under both quantifiers. The standard-Nat theorem is a separate
semantic induction and does not turn external truth into HA derivability.


## Fixed finite C222 circuit graphs accepted

The [actual C222 finite circuit graphs](reviews/arithmetic-command-circuitperm222-peer.md)
now represent every fixed numeric circuit by a parameter-free five-slot Σ1
graph and bind current word/leaf expressions exactly. Independent builds
pass nine standard-only reports and identical objects. The unrestricted
rho8 compiler still needs one circuit chosen outside all model/input
quantifiers; pointwise word existence alone does not discharge it.

The syntax includes truncated subtraction and the zero-safe counter loader.
Its graph is fixed before a model or its four inputs is supplied. Actual
MP and AX tags, y/x payload order and the direct-leaf guard remain explicit.
No internal circuit-code interpreter or proof history is assumed.

## Adaptive target window and early Pell indices accepted

The [adaptive rank-window theorem](reviews/native-adaptive-rank-window-root.md)
now derives the target window, both Pell classifications, n>=25, n<p,
p>=6, a positive main ordinate, the large-c bound and both 2p<c/2R<c
bounds from the literal A0/A1 equations and stated port/positivity data.
Two independent builds pass five standard-only reports and identical
objects. Signed divisibility needs no assumed nonnegative quotient.
Strong-index restoration, power recovery, the converse and internal HA
formalization remain open.

The theorem obtains q^3|Y from A0, the window from actual transport
and the port box, then q^4|(k-R-1) and positive classification from A1.
Its first-index modular argument works over signed integers. Classification
and index comparison are consequences, not source assumptions. The full
low-degree graph still needs strong-index identification and a converse;
these external native arithmetic results also need internal arithmetic
formalization before contributing an actual HA proof-existence endpoint.

## Retained ordinary consistency target semantics accepted

The [fixed ordinary consistency semantics](reviews/foundation-ha-consistency-semantics-peer.md)
now proves actual closedness, arbitrary-premodel valuation independence and
exact standard-Nat meaning of the retained formulas. The negative formula
means precisely absence of an actual repository ZFC refutation. Independent
builds pass seven standard-only reports and identical objects. This binds
the normalized HA target semantically; the equation/source arithmetic
proof and internal checker comparison remain separate obligations.

The positive predicate is the actual source rho; outer HA negation
has the negative consistency meaning. The proof uses actual closed support
and a separate Nat interpretation induction, then the previously accepted
fixed-source semantics. It does not identify ordinary NNF negation with
outer HA negation syntactically or turn standard-model truth into an HA
derivation. Arbitrary-premodel generality applies only to valuation
independence. No broad machine Bridge import or independent checker
reflection is introduced. Root reauthenticated the complete independent
replay, all 3612 checked evidence observations, seven axiom reports and both
objects after reading the full sources, checks, driver and peer receipt.

## Uniform unrestricted rho8 circuit accepted

The [uniform unrestricted rho8 circuit](reviews/arithmetic-command-rho8-circuitperm222-root.md)
now supplies one finite circuit before every internal model/input quantifier,
with no residual dominance condition. Actual guarded leaves and minor-first
MP implement the finite generic implication derivation. Independent builds
pass five standard-only reports and identical objects. This closes the
uniform finite rho8 step; internal proof-history compilation and the full
HA equivalence remain open.

The witness is uniform over every model in each fixed universe parameter,
with the existential outside all four input and saved-stack quantifiers.
Its graph is literal parameter-free Sigma1 arithmetic syntax. The generic
restricted rule uses actual u<=a dominance only at the leaf sites of the
finite derivation. The exact actual MP composition eliminates any outer
guard. This is the finite row needed by the subsequent represented proof
history, not already the internal history or source interpretation. A
Type0 fixed choice suffices for the PA completeness route, without claiming
one circuit across all universe levels from the current theorem.

## Actual C222 twelve-branch compiler row accepted

The [actual C222 compiler row](reviews/arithmetic-proof-word-rowperm222-root.md)
now has a total fixed arithmetic graph for all twelve branches and invalid
tags. Actual row acceptance and local child contracts imply its exact
all-top/all-stack execution contract. Independent builds pass six
standard-only reports and identical objects. The unrestricted rho8 choice
is fixed before Type0 models; internal proof-history induction remains open.

The actual new growG and helper-free gated bundle replace the historical
row9/row11 meanings. GEN's whole-tail child is selected by the subsequent
history,not silently confused with MP's minor child. The row has no supplied
global compiler theorem or source axiom validity premise. The next step is
the represented generic SequenceHistory construction and a genuine Pi1
prefix induction for all internal proof codes; the read-only
[history proposal](research/c222-proof-word-history-proposal-20261026.md)
records the exact recurrence,cache delta and Type0 completeness boundary.

## Literal adaptive strong-index recovery accepted

The [literal adaptive strong-index theorem](reviews/native-adaptive-strong-index-root.md)
now recovers the actual main Pell coordinates at target R from literal
A0/A1 and Fs/Fa, preserving unrestricted positive J. It derives square
divisibility and both auxiliary congruences before index identification,
with positive actual V/y and quotient witnesses. Independent builds pass
three standard-only reports and identical objects. First-index/power
recovery, source transfer, converse and internal HA arithmetic remain open.

The crucial adapter derives c^2|f^2-1 from relaxed Pell classification
and ordinate divisibility,then rewrites the graph's actual auxiliary value
as jc-R and of-c. It does not cancel the discriminant from the norm.
RankWindow supplies main classification and both strict half bounds;
Fs/Fa supply the signed strong norms. This advances native soundness of
the lower-degree carrier. It neither assumes nor supplies the still-missing
internal PA proof of the displayed equation/consistency equivalence.

## Represented actual C222 proof-word compiler accepted

The [all-internal C222 compiler](reviews/arithmetic-proof-word-perm222-root.md)
now maps every accepted internal proof code to a represented command word
with its exact conclusion and arbitrary initial top/saved stack. Genuine
Pi1 prefix induction proves correctness,with no supplied global invariant.
Its conditional false1 word halts from state(top,S,0,0). Independent builds
pass eleven standard-only reports and identical objects. Universal reset,
scheduler integration,source calibration and the HA equivalence remain open.

The history uses generic SequenceHistory and actual C222 child bounds.
Good and bounded PrefixGood have explicit Pi1 definitions over Delta1
checker and raw-word graphs. Genuine IΣ1 induction proves the actual row
successor and all accepted-code contracts,including nonstandard proof codes.
The false1 execution endpoint appends the actual conditional terminator.
It currently starts at state(top,S,0,0),so arbitrary scheduler work states
still require a reset prefix and a candidate bound. These are not inferred
from top/stack quantification alone.

## Source-proof interpretation audit and next kernel

The source-only [C222 interpretation audit](research/c222-source-proof-interpretation-plan.md)
records48 current source pins and3 provider-summary leads. Root rehashed
all51 records and read the full plan. The leads are not claimed as fresh
object authentication. The next actual C222 context calculus uses internally
sized vectors,followed by NNF-negation compatibility,context quantifiers and
a ten-case derivation induction. Existing EindContext is a bound-equality
context,not that sequent calculus.

The set-theory axiom images are a further substantial obligation. The actual
C222 seed image supplies subset-indexed coverage;it does not already give
raw Container/GIC. The external lower proof uses a tagged-domain/quotient
route. A represented seed/tagged interpretation or proved alternative raw
axiom deductions is needed. Old C254 R2Native cannot be renamed into this
step. The accepted word compiler does not discharge source-calculus
calibration or the missing actual equation/source PA proof.

## Actual C222 refutation to enumerator halt is proved in IΣ1

The [actual C222 refutation-execution theorem](reviews/arithmetic-proof-word-enumperm222-root.md)
now proves that an accepted internal C222 refutation forces the actual
permuted enumerator to halt from candidate4 and any working state. A real
AX reset and candidate bound discharge the scheduler premises. Independent
builds pass eight standard-only reports and identical objects. The literal
closed conditional has actual IΣ1 and PA derivations. Reverse soundness,
source/215 calibration and the final HA equivalence remain open.

The initial cache can contain false1 and the counter may be arbitrary.
The prefix AX c=1,x=y=0 resets both controls without inspecting their logical
meaning. Its candidate starts with tag4,so the actual fair scheduler reaches
it from4. The closed sentence quantifies actual checker codes and arbitrary
working states,and uses only actual represented check/live/run syntax.
Completeness over all Type0 IΣ1 models yields the internal theorem;it does
not promote mere standard-Nat truth to provability. The reverse direction
will carry bounded actual proof witnesses in each live working state.

## Actual C222 internally sized source contexts accepted

The [actual C222 context calculus](reviews/validator-proof-context222-root.md)
now proves rules for internally sized implication contexts,including actual
history witnesses,deduction,subsumption,source-list shifting and enumeration
independence. Two independent builds pass sixteen standard-only reports
and identical objects. The independent inventory explicitly repairs one
omitted Aesop meta-import boundary. NNF compatibility,source derivation
induction and source axiom interpretation remain open.

The context representation is an actual arithmetic vector fold,not a
standard finite Lean hypothesis list. Every public Der statement contains
an actual checker witness for its implication chain. Fixed finite
propositional certificates use the already accepted C222 classical calculus;
this does not add classical rules to HA. Internal context enumeration may
contain duplicates or any order. The source proof interpreter and actual
set-theory schema images are subsequent substantive obligations.
The next source-negation plan uses the corrected encoder-only40-boundary
inventory and explicit Pi2 syntax induction under IΣ2.

## Bounded actual C222 stack certificates accepted

The [actual C222 bounded-stack certificate](reviews/arithmetic-stack-certificate222-root.md)
now retains one internal bound on actual proof witnesses for all theorem
stack entries. Its Delta1 stack predicate gives Sigma1 working-state
certification;push/pop and cached-falsity extraction are checked. Independent
three-file builds pass ten standard-only reports and identical objects,
including an explicitly rebuilt numeric tail prerequisite. Command and
reverse scheduler preservation remain open.

The witness bound is on actual checker proof codes,not formula values.
It bounds each internal stack offset through the stream's numerical drain;
all later zeros use the fixed truth witness. This keeps the runtime
invariant Sigma1 without an unbounded forall-exists witness oracle.
The reused old-named Tail254 module is numeric only and is rebuilt over the
current dependencies. Actual command preservation must still use NIP0,
DROP1,MP2,physical rho6(a,c),growG,old-d GEN and the current bundle gate.

## Literal adaptive first index and power recovered

The [literal adaptive power recovery](reviews/native-adaptive-power-recovery-root.md)
now derives X=2^R,the exact first index2n=R+1,and the required signed
divisibility from the actual positive carrier tuple. Its projection retains
3|q and its growth uses the actual eta/zeta split. Four independent builds
pass fourteen standard-only reports and identical objects. Mersenne
factor-three exclusion,whole-product/source transfer,the converse and
internal HA arithmetic remain open.

All source/index/oddness/coprimality/power assumptions are absent from
the public literal wrapper. The projection proves q|3X before any growth
argument. The correct first index is2n=R+1,not n=R. The next Mersenne
stage should exclude q=3*2^u using beta=2^94517-1,then derive q|X and a
binary cell base without a restriction on J modulo3. Canonical source
restoration/converse and actual internal PA arithmetic still remain.

## Source and polynomial bridges proved internally (2026-10-27/28)

The HA endpoint is assembled in
[`HACurrentPolynomialBridge2011`](Lean/DiophantineConsistency/HACurrentPolynomialBridge2011.lean):

```
ha_current_iff_consistency_of_local (hL : ArithmeticPackingCells.LocalNormalization) :
  ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence
    FoundationHAConsistencyNormalization.ordinaryConsistency
```

This is an actual HA derivation of "the literal current equation has no positive
zero ↔ ZFC proves no contradiction". Its single premise, a finite statement about
standard natural numbers, is discharged in the next section.

**How the derivation is obtained.** `HACurrentAssembly2011` chains three
equivalences in every Type0 model `V` of `𝗜𝚺₂`, then applies completeness to get
an actual `𝗜𝚺₂`/PA proof and the existing GG transfer to HA.

- **Polynomial bridge.** The no-zero sentence holds in `V` iff the represented
  decimal215 run never halts in `V`.
- **Checker/machine theorem** (`ArithmeticCheckerMachine215`). This link was
  already closed.
- **Source bridge.** ZFC consistency holds in `V` iff no internal History222
  refutation exists.

No step promotes standard-model truth to provability.

**Source bridge** (`HACurrentAssembly2011.sourceBridge`, via
`ZFCinPA.ValidatorConsistency222`).

- *Upper direction* (8356b0e959). An accepted C222 code decodes to an internal
  ZF theorem. Tags 9/11 are new: growG comes from equality alone, and the
  helper-free seed bundle comes from Glazer's seed property in template
  theories.
- *Lower direction* (8f9ca10d95). The chain is
  ZFC⊥ → ZF⊥ (L) → qTheory⊥ (well-founded quotient) → C222 seed theory⊥ (the
  moving-marker tagged interpretation, `ValidatorSeedFixedImages222`,
  `ValidatorSeedQTheory222`) → an actual value-two witness.

**Polynomial bridge** (plan: `research/ha-polynomial-bridge-plan-20261027.md`).
Facts about values below standard bounds are transferred from ℕ through
`Nat.cast`: tiles < 942, digits < 2^47, carries ≤ 57. Every argument over the
nonstandard cell count, length, or time is re-proved by internal IΣ1 induction.

- *Soundness* (unconditional, f79467f544,
  `ArithmeticSoundness2011.zero_halts`). The chain is: positive zero → window
  interface → cell decoding (S9–S12) → marked cyclic Wang word → halt (S13–S14).
- *Construction* (16bbf50270,
  `ArithmeticCurrentConstruction2011.halt_positive_zero`). It runs from a
  halting time T to the 14 coordinates, all positive, through these stages:
  - run trace;
  - band and helical tiling word;
  - packing;
  - rank forcing;
  - controller (Hensel lifting, Γ a unit modulo d·p^{m+1});
  - outer and auxiliary Pell seeds.

**The remaining premise.** `LocalNormalization` is the finite Local
Normalization Lemma. It covers admissible triples of the 942-tile table and the
fixed 94517-bit kernel and masks, plus per-cell mask facts. It is a statement
about standard naturals and is proved in ℕ by the legacy `CurrentWord*`
modules. Those modules cannot be imported next to Foundation:
- the reason is their path to Mathlib's `Matrix`;
- the auto-realized `Matrix.map.eq_1` collides with
  `Foundation.Vorspiel.Matrix`.

A Matrix-free port (`MF*` clones with verbatim proof bodies, plus a per-cell
bridge to `lnlD`) is in progress.

`#print axioms` of `ha_current_iff_consistency`, `sourceBridge` and
`sentence_of_no_halt` gives `propext`, `Classical.choice`, `Quot.sound`. No
module in these chains uses `sorry` or `native_decide`.

## The HA endpoint is unconditional (2026-10-28, 447801b6e4)

[`HACurrentEquation2011`](Lean/DiophantineConsistency/HACurrentEquation2011.lean)
proves, with no premises:

```
ha_current_iff_consistency :
  ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence
    FoundationHAConsistencyNormalization.ordinaryConsistency
```

It also exports `isigma2_proves_current_iff_consistency`,
`peano_proves_current_iff_consistency` and `polynomialBridge`.

The last premise, the finite Local Normalization Lemma, is now
`ArithmeticLocalNormalization.localNormalization`. It rests on 37 Matrix-free
`MF*` clones of the accepted ℕ proofs, with verbatim bodies written by a
scripted closure pass, plus five new modules (about 1k lines). These new
modules restate the per-digit mask tests for a single cell and place each
admissible triple in a three-cell world, which forces the normalized block to
equal `lnlD`.

`HA.Derives` is intuitionistic natural deduction with equality, and it has no
excluded-middle or double-negation rule. `HA.Proves` adds the six arithmetic
axioms and the induction instances.

`#print axioms` of the endpoint gives `propext`, `Classical.choice` and
`Quot.sound`, and no `sorry`, `admit` or `native_decide` occurs in the chains.
Because every link is internal to arbitrary models of `𝗜𝚺₂`, the
derivation does not use Lean's proof of Con(ZFC). The same theorem for a
trivially unsolvable equation would therefore make HA prove Con(ZFC).

## IΣ₁ suffices: the equivalence is finitist (2026-10-28, 009a470554)

```
HACurrentEquation2011.isigma1_proves_current_iff_consistency :
  𝗜𝚺₁ ⊢ classicalSentence 🡘 sourceSentence
```

IΣ₂ entered only through six Π₂ order inductions in the C222 source-proof
interpreter. These covered vacuity, alpha transport, negation, the
quantifier context, the derivation translation, and the seed closure.

The inductions had quantified environments, binder stacks and streams without
bounds. Foundation's `bounded_all_sigma1_order_induction`, an IΣ₁ theorem,
bounds those parameters by Σ₁ functions of the recursive calls. That makes
each invariant Σ₁.

Two inductions needed a different repair:
- `cProv_gen_context` inducts over sublists of a fixed context.
- `translate` puts its context enumeration under an existential and reads it
  back by enumeration independence.

Both bridges now range over models of `𝗜𝚺₁`. The IΣ₂, PA and HA statements
follow by weakening and by the GG transfer.

Both sides are Π₁, so the equivalence is a Π₂ sentence. By Parsons' theorem
(IΣ₁ is Π₂-conservative over PRA), it is provable in primitive recursive
arithmetic. That is the standard formal reading of "finitary"; the repository
has no PRA formalization, so the PRA step is the cited theorem.

## Explicit elementary witness transfers (2026-10-28, iteration 3)

The finitist content is made explicit as bounded Π₁ statements. Each is proved
in every model of IΣ₁. In each, the witness map is a bounded search below an
explicit tower of `Exp.exp`/`power`, so the map is elementary recursive.

| Transfer | Theorem | Bound |
|---|---|---|
| positive zero `u` ⇒ halting time | `ArithmeticSoundness2011.zero_halts_below` | `t < β·u₀ + 1` |
| halting time `T` ⇒ positive zero | `ArithmeticConstructionBound.halt_positive_zero_below` | every coordinate ≤ `zeroBound T` (exp/power depth 7) |
| halting time `t` ⇒ C222 refutation | `ArithmeticRuntimeBound215.refutation_bound_of_blank_halts` | `proof ≤ 2^(2^(700t+8))` |
| C222 refutation ⇒ halting time | `ArithmeticRefutationHaltBound.blank_halts_le_of_refutation` | `t ≤ Btape (7·Bdag (Bword code²))` |

The last row composes four bounded layers:
- `Bword`, the size of the compiled refutation word, a double exponential;
- `Bdag n = n·2^(2^(100n+23609))` for the DAG macros;
- a factor-7 bisimulation hop;
- the quadratic tape bound `Btape`.

`Bword` contains one unevaluated fixed constant, `cb rho8Circuit`, because the
rho8 circuit is chosen with `Classical.choose`.

The C222 ⇄ Foundation-ZFC link needs
proof-size bounds for the source-bridge proof transformations; its scope is
the next section.

## C222 ⇄ Foundation-ZFC witness bounds: scope (2026-10-28)

**Target.** Two bounded Π₁ theorems, each proved in every model of IΣ₁.

```
upper : value code = 2 → ∃ d ≤ Bup code, Proof 𝗭𝗙𝗖 d ⊥
lower : Proof 𝗭𝗙𝗖 d ⊥ → ∃ code ≤ Blow d, value code = 2
```

With the four rows above, they make every witness map between Foundation
ZFC-refutations and positive zeros of the current equation elementary.

**Where the witnesses are lost.** Foundation's typed derivations
(`TDerivation`, `T ⊢!ᵈᵉʳ Γ`) are data: they carry their code `val : V`.
The ten rule constructors (`axL … axm`, `Proof/Basic.lean`) are explicit
pairing terms `⟪s, k, …⟫ + 1`, and `pair_polybound` bounds them. So any proof
assembled from typed combinators builds an explicit code. Witnesses vanish
only where a step returns the Prop-level `Provable`/`Derivable` (`∃ d, …`).
The decisive places are the inductions whose invariant is "∃ derivation";
`InternalRelativization.derivable_relSet` is one.

**ZF → ZFC is free.** `ValidatorConsistencyForward254.zfc_provable_of_zf`
reuses the same code `d` (`Derivation.of_ss`), so the bound is the identity.

**Measured cone** (Python audit of the import closures; "internal" means the
module works over models of IΣ₁):

| Direction | Modules / lines | Internal modules / lines | Derivation-producing inductions |
|---|---|---|---|
| upper (C222 ⇒ ZF) | 136 / 40.0k | 76 / 24.0k | 9 |
| lower (ZFC ⇒ C222) | 219 / 60.5k | 102 / 35.9k | 18 |
| shared by both | 94 / 33.1k | | 6 of the above |

That is 21 distinct inductions. The remaining derivation-producing
declarations (about 230 upper and 400 lower, an overcount) do not induct: each
is a fixed composition of rules, typed combinators and standard `compiled`
derivations. They need bounded statements but no new bound design.

Purely semantic modules (the `L`-step set-structure arguments, the Tarski
calculus, `TaggedValid` model checks) feed `compiled` meta-proofs. Those
proofs are fixed standard numerals, constants inside V, so they need no
change.

The 21 inductions:
- *shared:* `derivable_relSet`, `derivable_of_domSet` (InternalRelativization),
  `replace_aux`, `term_replace_aux` (SetCongruence),
  `provable_numChainOmegaCode`, `zfcProofSelectorIn_of_package`;
- *upper:* `rejected_or_decoded_provable` (decoders 254 and 222),
  `derivable_rename_bounded`;
- *lower, ZFC → ZF (L):* `peel`, `glue`, `fun_MT`, `slot_MT`, `numOK`;
- *lower, ZF → qTheory:* `derivable_iSet`, `NativePeel.peel`;
- *lower, qTheory → seed:* `derivable_tagged_bounded`, `discharge_all`,
  `fixed_image_all`, `close_guarded`;
- *lower, seed → C222:* `translate_main`. Iteration 2 already gave its
  context parameter a Σ₁ bound; the output word still needs one.

**Bound shape.** Use `E k x = 2^(2^(k·(x+1)))`. A node of a tree-shaped
derivation adds a pairing polynomial of fixed degree (≤ 2⁵ for six-tuples),
and `E k (x+1) = E k x ^ (2^k)` absorbs it. So one height-2 tower per
transformation survives the induction step.

The C222 decoder is the exception. It reuses earlier rows as a DAG, so the
tree it decodes to can be exponentially larger. That adds one more
exponential, which is still elementary. Composing the four lower stages gives
a fixed tower height, an estimated 8–10. The bound shape is a design estimate
and has not been checked in Lean.

**Work, staged by leverage.**

| Stage | Content | Estimated size |
|---|---|---|
| 0 | `SizedDerivation`: `DerivableLe`/`ProvableLe`, bounded twins of the ten rules and of the typed combinators the cone uses (`⨀`, `K!_intro`, …), size lemmas for the set/formula operations (`insert`, `∪`, `setShift`, `neg`, `substs`, `relativize`), and `E`-closure lemmas | 2 modules, ~1.5k lines |
| 1 | the shared inductions, starting with the generic relativization engine `derivable_relSet` + `derivable_of_domSet` | 3–4 modules, ~2k lines |
| 2 | upper: both decoder inductions, row soundness (rho1/6, container, collection, equality, growG, bundle), proof renaming; gives `upper` | ~8 modules, ~3–4k lines |
| 3 | lower, ZFC → ZF: the L obligations (`peel`, `glue`, `driverT`, `numOK`) | ~6 modules, ~3k lines |
| 4 | lower, ZF → qTheory → seed: interpretation engine, marker relativization, discharge, axiom images | ~6 modules, ~3k lines |
| 5 | lower, seed → C222: bounded `translate_main`; gives `lower` | ~3 modules, ~1.5k lines |

The total is about 30 new modules and 14k lines, written as bounded twins
beside the accepted modules. As in iteration 3, the accepted modules stay
untouched, because the peer actively edits this tree.

Stage 2 alone closes the upper row. Stages 0–1 are prerequisites for both
directions and are reusable Foundation-level infrastructure.

**Main risks.**
1. Set-coded sequents are exponential in their largest formula, so bounds must
   be stated on `fstIdx` sizes as well as on derivation codes.
2. Lemmas that end in `Provable` and are reused through `.get`
   (`Classical.choose`) are opaque. Each one on the path needs a typed or
   bounded restatement, not a wrapper.
3. `Classical.choose`-picked fixed objects, such as the rho8 circuit in
   `Bword`, leave constants unevaluated but still fixed.

## Stage 0–1: sized derivations and the bounded relativization engine (2026-10-28)

Both new modules are in `Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/`.
They hold in every model of IΣ₁. `#print axioms` gives `propext`,
`Classical.choice` and `Quot.sound`
(`InternalRelativizationBoundAudit.lean`).

**`SizedDerivation`** (372 lines).
- It defines `DerivableLe T s b := ∃ d ≤ b, DerivationOf T d s`.
- Bounded twins of `em`, `verum`, `and_m`, `or_m`, `all_m`, `ex_m`, `wk`,
  `shift`, `cut`, `by_axm`, `ofSetEq` and `of_ss`. The derived `and`/`or`
  are bounded by a member bound.
- The single arithmetic engine is `pair_succ_le_exp`: `⟪a,b⟫+1 ≤ 2^(4e)` when
  `a, b ≤ 2^e` and `e ≥ 3`. As a result, every rule whose entries are at most
  `2^e` (`e ≥ 4`) has code at most `2^(1024e)`.

**`InternalRelativizationBound`** (978 lines). All bounds take one numeric
parameter `a`, which bounds `d`, `¬d`, and the side formulas
`¬δ(&i)`/`δ(&i) ≤ 2^(2^(a(i+1)))` (widened in Stage 3a).
- `relativize_le`: `relativize L d p ≤ relB a p = 2^(2^((a+12)(p+1)))`, by
  formula induction.
- `derivableLe_relSet`: a `T`-derivation with code `n` yields the relativized
  `U`-derivation. It has at most `n + a` side formulas and code at most
  `towerB a n = 2^(2^(2^(ac a·(n+1))))`, with `ac a = 2(a²+2a+12)+40`. The
  proof is the same `Derivation.induction1` as the unbounded engine, with
  three bounds:
  - all members of all sequents built at node `n` lie below one bound
    `memB a n`;
  - each input node costs at most four bounded rule applications;
  - the resulting factor `2^40` in the exponent is absorbed by `stage4_le`.
- `derivableLe_of_domSet`: discharging `m` side formulas multiplies the
  exponent by `2^(30m)`.
- `provableLe_relativize` / `provableLe_falsum_of_relativize`: a `T`-proof
  with code `n` gives a `U`-proof with code at most
  `provB a n = 2^(2^(30(n+a)) · 2^(2^(ac a·(n+1))))`. That bound is explicit
  and elementary.

**Scope correction.** The ZF/ZFC `L` step goes through
`SetRelativization.provable_falsum_of_relativize_set`. That is a thin wrapper
around this engine, so the scope stands: one engine serves `L`, and the
quotient chain reuses `derivable_of_domSet`.

**Still to do for Stage 1.** The other shared inductions:
- `SetCongruence.replace_aux`/`term_replace_aux`;
- `NumeralOmega.provable_numChainOmegaCode`;
- `PackageInduction`.

**Risks for the applications** (Stage 3 onward).
- *Triple-exponential axiom obligations.* The bounded engine assumes axiom
  obligations within `2^(2^(2^(a(p+1))))`. If the `L` obligations (`glue`,
  `peel`, `driverT`) come out taller, the engine's tower needs more height.
  That change is mechanical: `towerB` gets another exponential, and so does
  `ax_le`.
- *Substitution bounds for `⌜domL⌝`.* The side-formula hypotheses
  `domF L d i ≤ 2^(2^(a(i+1)))` needed a substitution-size lemma (done in Stage 3a, `ShiftBound`) for the fixed
  domain formula. This is a polynomial bound for a standard formula, but it
  is not yet proved.

## Stage 3a: bounded ZFC → ZF transport, up to the schemata (2026-10-28)

```
ConstructibleInterpretationBound.provableLe_falsum_ZF_of_ZFC
  (hSchema : bounded separation/replacement obligations)
  (h : Proof 𝗭𝗙𝗖 n ⊥) : ProvableLe 𝗭𝗙 ⊥ (provB aL n)
```

This holds in every model of IΣ₁. It mirrors the original
`ConstructibleInterpretation.provable_falsum_ZF_of_ZFC`, which also takes
the schema obligations as its one premise. `#print axioms` gives `propext`,
`Classical.choice` and `Quot.sound`.

**Discharged here, all at one standard numeral `aL`:**
- *Standard obligations.* The equality axioms, the seven fixed axioms and
  `𝗔𝗖` are fixed meta-level proofs. Under D1 their internal codes are the
  numerals `⌜b⌝` (`proof_of_quote_proof`, `coe_quote_proof_eq`).
  `stdN = sup` over the finite set bounds all of them.
- *`𝗭𝗙 ⊢ ∃x (x ∈ L)`.* Its code is likewise a numeral.
- *Domain-formula constants.* `⌜domL⌝`, `¬⌜domL⌝`, `δ(&0)` and `¬δ(&0)` are
  numerals computed in ℕ, by Σ₁ absoluteness of `neg` and `substs1`
  (`DefinedFunction.shigmaOne_absolute_func`).
- *Side formulas* `¬δ(&i)` and `δ(&i)` are below `2^(2^(aL(i+1)))`. The new
  generic module **`ShiftBound`** proves `shift q ≤ q²` for every internal
  term and formula, because Cantor pairing preserves "each entry ≤ its
  square". Since `¬δ(&(i+1)) = shift (¬δ(&i))`, `domF_le` and
  `substs1_fvar_le` follow by induction on `i`. For this, the engine's
  side-formula hypotheses were widened to this double-exponential shape;
  `bat` still absorbs it.

`aL` is defined from these codes and is not evaluated, the same situation as
`cb rho8Circuit`.

**Stage 3b, remaining: the schema obligations** (`LSepBase.sep_obligation`,
`LReplBase.repl_obligation`).
- *Template compilation.* Both obligations go through
  `LTemplate.compileT`, which is `compileOpenTemplate`, a **meta-level**
  recursion over a fixed template derivation. Its size bound is a Lean
  induction on that standard derivation.
- *Congruence proofs.* Its axiom leaves include the `SetCongruence`
  congruence proofs. These are internal inductions (`replace_aux`,
  `term_replace_aux`), already on the Stage 1 list.
- *The `L` inductions* chain these with typed `⊢`-combinators: `glue`
  (formula complexity), `peel` (opened variables), `driverT`, `numOK`,
  `fun_MT` and `slot_MT`. Two things are needed:
  - sized twins of the combinators they use (`⨀`, `K!_intro`, `K!_left/right`,
    `all_iff_self`, …);
  - bounded twins of each induction.
- *Risk.* The engine accepts obligations up to `2^(2^(2^(aL(p+1))))`. If the
  glue tower is taller, the engine needs one more exponential, which is a
  mechanical change.

## Stage 3b in progress: sized Hilbert combinators (2026-10-28)

**Scope correction.** The scope section said that typed internal proofs
"already build explicit codes". That holds only for Foundation's *primitive*
typed constructors (`TDerivation.em`, `and'`, `or'`, `all'`, `exs'`, `wk`,
`shift`, `cut`, `byAxm`). The derived `TDerivation.and`/`or`/`all`/`exs` go
through `Derivable.toTDerivation`, which picks the code with
`Classical.choose`. So do the operations built from them:
- `TProof.modusPonens` (`⨀`);
- every Hilbert axiom of the internal `Entailment.Minimal` instance;
- `TProof.all` and `specialize`;
- `ModelCodedShiftCancellation.cancelShift`.

Their codes are unconstrained, so each such step must be re-derived from the
bounded primitive rules.

**`SizedProof`** (new, generic over the language) does this for the six
combinators the `L` schema obligations use: `mdp` (`⨀`), `K_intro`, `K_left`,
`K_right`, `C_id`, `E_id`. Each costs at most four bounded rule applications
under one member bound. The usage count over the 48 `L*` modules plus the
template compiler is: `⨀` 51, `K!_intro` 50, `K!_left`/`K!_right` 10 each,
`E!_id` 2, `C!_id` 1. The module also proves
`neg_code_le : neg L q ≤ 2^(2^(12(q+1)))`, so callers can supply member bounds for
negated formulas.

**Roadmap for the rest of Stage 3b:**
1. A generic substitution size bound. Placeholder atoms translate to
   `K.subst (translated terms)`, and under binders `qVec` bShifts the
   substituted terms, which is bounded by squaring as in `ShiftBound`.
2. Sized template compilation: translated-formula codes by meta induction on
   the template formula, `compileDerivation` by meta induction on the fixed
   template derivation, and a sized `cancelShift`.
3. The axiom leaves of the templates, among them the `SetCongruence`
   congruence proofs.
4. The `L` inductions `glue`, `peel`, `driverT`, `numOK`, `fun_MT` and
   `slot_MT`.
5. `sep_obligation`/`repl_obligation` → `hSchema` → an unconditional bounded
   ZFC → ZF transport.

## Stage 3b: substitution and code levels (2026-10-28)

**Generic substitution bound** (`BoundedPAConsistency.SubstBound`). If the
entries of `w` are variables at most `2^c`, then
`subst L w p ≤ 2^(2^((c+12)(p+1)))`.

**Why value bounds are not enough.** `LMatch.mVal j`, the matching code for
`j` free variables, is an internal recursion of length `j`: each step
substitutes into `shift (mVal (j-1))`. A bound that is double exponential in
the previous code turns `j` steps into a tower of height `≈ 2j`, which is not
elementary. Iterated constructions therefore need **level** bounds:
- write `lvB u = 2^(2^u)`;
- a code `x` has level `u` when `x ≤ lvB u`;
- the operations must multiply the level by a constant, not the value.

**`ZFCinPA.SetCodeLevels`** proves these for `ℒₛₑₜ`, in every model of IΣ₁:

| Lemma | Effect on the level |
|---|---|
| `shift_level` | `u ↦ u+1` |
| `neg_level` | `u ↦ 10(u+1)` |
| `subst_level` | `u ↦ 10(u+1)+c₀`, for variable entries at level `c₀` |

The proofs are inductions on the level, not on formula structure:
- a Cantor pair at least squares each entry (`sq_le_pair_left/right`), so
  the subformulas of a level-`(u+1)` code have level `u` (`pair_children`);
- rebuilding a node with at most five pairings costs at most `+10` levels
  (`pair_lvB`);
- no `ℒₛₑₜ` formula has code below `3` (`three_le_formula`), so level `0` is
  vacuous.

**First payoff** (`ZFCinPA.LMatchLevel.mVal_le`).

```
mVal j ≤ lvB (Cm · 16^j) = 2^(2^(Cm·16^j))
```

Here `Cm = ⌜funcS⌝ + zT + eT + 40` is a fixed standard code. This is a
fixed-height tower in `j`, the first internal iteration of the `L`
obligations with an explicit elementary bound. `#print axioms` gives
`propext`, `Classical.choice` and `Quot.sound` (`SetCodeLevelsAudit`,
`SubstBoundAudit`).

**Consequence for the engine.** A glue step composes level bounds a fixed
number of times, and the induction over formula complexity `C` multiplies
levels `C` times. So the obligations should be about triple exponential in
the schema code `p`, followed by the `exp`s of the derivation codes. The
engine's axiom-bound shape `2^(2^(2^(a(p+1))))` will need one or two more
exponentials (a mechanical change to `towerB` and `ax_le`).

**Still to do in Stage 3b:**
- level bounds for `envForm`, `relativize`, `gVal` and the other `L` formula
  families;
- sized template compilation (`compileDerivation` by meta induction;
  translated-formula levels through `subst_level`);
- the template axiom leaves, including `SetCongruence`;
- the `L` inductions (`glue`, `peel`, `driverT`, `numOK`, `fun_MT`,
  `slot_MT`) restated with `SizedProof`;
- the `sep`/`repl` assembly.

## Stage 3b: sized template compilation pieces (2026-10-28)

All of the following hold in every model of IΣ₁; `#print axioms` gives
`propext`, `Classical.choice` and `Quot.sound` (`SizedTemplateCompilerAudit`).

- **`ZFCinPA.SizedTemplateCompiler.sized_compile`.** Fix a buffered
  translation and a meta-level derivation `d`. Suppose every translated
  formula of every sequent of `d` (at buffers `≤ B`) is below `F`, the
  translated terms and axiom leaves are below `2^e`, and `F ≤ e`. Then the
  translated conclusion has a derivation with code at most
  `2^(1024^(height d)·e)`. It is proved by meta induction on `d` from the
  bounded primitive rules, so it never uses `compileDerivation`'s chosen
  axiom codes.
- **`ZFCinPA.SizedShiftCancel`.** `cancelShiftLe` re-derives
  `⊢ shift φ ⇒ ⊢ φ` from the bounded rules: generalize, then specialize at
  `&0`, in four rule stages. `cancelShiftNLe` iterates it along `shiftN`.
  This replaces `cancelShift`, whose `TProof.all`/`specialize` codes are
  chosen.
- **`ZFCinPA.TemplateTranslateLevel.translate_level`.** For each fixed
  template formula `φ` there is a meta-level constant `tA φ : ℕ`, uniform
  across models, such that placeholders at level `u` give a translation at
  level `tA φ·(u+1)`. Placeholder atoms go through `subst_level`, negated
  ones through `neg_level`, and set atoms are bounded directly.

**Next.**
1. Instantiate `Good` for `openTranslation Ks`. The formula bound is
   `F = lvB(Amax·(u+B+1)) + 1` with `Amax` the meta maximum of `tA` over the
   formulas of `d`; `shiftedPredicates Ks b` is at level `u + b` by
   `shift_level`.
2. Bound the template axiom leaves:
   - `liftedZFProof` is `byAxm`, so its code is explicit;
   - `separationProof`/`replacementProof` go through `openAxiomProofCode`,
     an explicit code function whose `specializedProofCode` recursion needs
     level bounds;
   - the `SetCongruence` congruence proofs are internal inductions that need
     bounded twins.
3. With those, `compiled`/`compiledG` get explicit bounds, and the `L`
   inductions can be restated on top of `SizedProof`.

## Stage 3b status after the 2026-10-28 autonomous run

**Proved** (all in every model of IΣ₁, axioms `propext`/`Classical.choice`/
`Quot.sound`):

| Module | Result |
|---|---|
| `BoundedPAConsistency.SizedProof` | the six Hilbert combinators with bounds; `neg_code_le` |
| `BoundedPAConsistency.SubstBound` | value bound for variable substitution |
| `ZFCinPA.SetCodeLevels` | level calculus: shift `+1`, neg `×10`, subst `×10 + c₀` |
| `ZFCinPA.LMatchLevel` | `mVal j ≤ 2^(2^(Cm·16^j))` |
| `ZFCinPA.SizedTemplateCompiler` | bounded buffered compiler (meta induction on `d`) |
| `ZFCinPA.SizedShiftCancel` | bounded shift cancellation and its iteration |
| `ZFCinPA.TemplateTranslateLevel` | `translate_level`, with meta constants `tA` |
| `ZFCinPA.SizedOpenTemplate` | `sized_open_compile`: end to end, up to the axiom leaves |

**Remaining for an unconditional bounded ZFC → ZF transport.**

1. *Template axiom leaves*, i.e. the `translated_axiom` cases.
   - **Lifted ZF axioms and equality axioms** are `byAxm`, so the code is
     explicit. `DerivableLe.by_axm` plus `translate_level` is enough; this
     is a small lemma.
   - **Placeholder congruence** (`SetCongruence.congruenceProof₀..₃`) gives
     Prop-level proofs. Their internal inductions (`replace_aux`,
     `term_replace_aux`) need bounded twins with level bounds.
   - **Separation/replacement template instances** go through
     `OpenTemplateClosure.closeTemplate` and
     `ModelCodedOpenSchemaAxioms.openAxiomProofCode`.
     - `closeTemplate` uses `generalizeAll`, whose codes are chosen.
     - `openAxiomProofCode` is explicit, but its `specializedProofCode` runs
       an internal state machine (`runState`/`advance`) for `binders`
       steps; a level analysis of one `advance` step is needed.
2. *The `L` inductions*: `glue` (`LGlue1–4`), `peel` (`LPeel`), `driverT`
   (`LDriver`), `numOK` (`LNumOK`), `fun_MT`/`slot_MT`. Each must be restated
   as a `DerivableLe` induction, using:
   - `SizedProof` for `⨀`/`K!_intro`/…;
   - `sized_open_compile` for every `compiled`/`compiledG` template;
   - level bounds for the formula families (`mVal` done; `envForm`, `rel`,
     `gVal`, `pVal`, … to do).
3. *Assembly*:
   `sep_obligation`/`repl_obligation` → `hSchema` →
   `ConstructibleInterpretationBound.provableLe_falsum_ZF_of_ZFC`.

**Required change to the engine.** The obligations will be about triple
exponential in `p`, followed by derivation exponentials. So `towerB`/`ax_le`
in `InternalRelativizationBound` need one or two more exponentials before
the assembly.

## Stage 3b: template axiom leaves (2026-10-29)

**Proved** (every model of IΣ₁; audit `ZFCinPA.SizedCongruenceAudit`, axioms
`propext`/`Classical.choice`/`Quot.sound`):

| Module | Result |
|---|---|
| `ZFCinPA.SizedTemplateAxioms` | lifted `𝗭𝗙` and non-congruence equality leaves: one `axm` rule, code bound via `translate_level`, at every buffer |
| `ZFCinPA.LevelDerivation` | the scale `DLv T s w := DerivableLe T s (2^(lvB w))`: one level per primitive rule once `w ≥ 4`; bounded `spec` |
| `ZFCinPA.SizedCongruence` | bounded equality replacement for internal formulas, parameterized by the atom case (`AtomOK`); induction on `formulaComplexity` |
| `ZFCinPA.SizedCongruenceAtoms` | `AtomOK` from fixed `𝗭𝗙` theorems with numeral proofs; `replace_le` unconditional |
| `ZFCinPA.SizedPlaceholderCongruence` | `cong_leaf`: `congruenceFormula a K` (a ≤ 3) at level `congL u`, linear in the level `u` of `K` |

Three design points:

- **The measure is formula complexity, not the code.** The `∀` premise of
  replacement concerns `shift p`, whose code is larger than that of `∀ p`
  when `p` has free variables. Foundation's `formulaComplexity` is invariant
  under shift, substitution and negation. So the code level `v` stays fixed
  through the induction, and the variable level `c` grows by one per binder.
- **Fixed theorems enter as numerals.** The atom, reflexivity and symmetry
  cases use meta-level `𝗭𝗙` proofs, quoted as standard numerals
  (`proof_of_quote_proof`) and specialized by bounded `spec_step`s.
- **No compounding of levels.** Each intermediate formula is a *fixed*
  formula under one substitution of closed variable terms (`tsubst_le`), so
  its level is linear in `c`. Iterating `subst_level` would multiply the
  level by 10 at each step instead.

**Remaining leaf: separation/replacement instances.**
- *The issue.* `OpenSchemaTemplates.separationProof` uses `closeTemplate`,
  which is `generalizeAll` with chosen codes. It then uses
  `zfSeparationProof K = openAxiomProofCode (sepBody K)`.
- *What is explicit.* `openAxiomProofCode` is an explicit code:
  `specializedProofCode` runs `specializeCode` (cut, wk, ∃, axL)
  `bv (bindFreeAt 0 p)` times.
- *Plan.*
  1. Bound `specializeCode` (+3 levels).
  2. Prove a Π₁ induction on the remaining binders for `subst W body₀`, with
     `W` ranging over vectors of variable terms of level ≤ `c`. This avoids
     compounding: `subst v (subst W body₀) = subst (termSubstVec v W) body₀`,
     and the result is again a vector of variable terms.
  3. Bound `closeFormulaCode` by a level bound for `bindFreeAt`.
  4. Generalize `strip` (currently `n ≤ 6`) to the template's `fvSup` binders.
- *Expected cost.* The closure over `m` free variables costs `+2m` levels,
  and `m` can be as large as the code. For placeholders without free
  variables, `m` is the template's `fvSup`, a meta-level constant.

**Update (2026-10-29, later).** The separation/replacement leaf did not need
the plan above. For shift-fixed placeholders, the translated closed instance
`∀^N T` contains the recognized `𝗭𝗙` axiom `∀^m T`, with `m = bv T`
(`SchemaRecognizer`; `subst_congr` moves the opening from `N` to `m`). So
the leaf is one `axm` rule plus `N − m` vacuous generalizations
(`ZFCinPA.SizedSchemaLeaves`).

`ZFCinPA.SizedLTemplate.sized_compileT` is the bounded twin of
`LTemplate.compileT`: every fixed derivation over `templTheory` compiles at
shift-fixed placeholders (arity ≤ 3, level `u ≥ 2`) within
`2^(stg (4b₀) (stg h (cE A B u)))`, with no conditional leaves.

**Remaining:**
- the `L` inductions (item 2), now on top of `sized_compileT`, `SizedProof`
  and `DLv`;
- the assembly (item 3);
- the engine change.

Each `L` induction must also check that its placeholder families are
shift-fixed and bounded in level. `envForm` is shift-fixed (`LGlue2`).

**Update (2026-10-29, evening): template compilation is bounded at
arbitrary placeholders.** The `L` application compiles at placeholders that
are *not* shift-fixed: `LSepBase.sep_base` uses `rel K`, whose free
variables are the separation parameters. So the schema leaves now go through
the explicit open axioms:
- `ZFCinPA.SizedOpenAxiom` bounds `specializeCode`, the `specializedProofCode`
  iterator (`spc_le`) and `bindFreeAt` (`bindFreeAt_level`), and proves
  `open_sep_le`/`open_rep_le`;
- `ZFCinPA.SizedOpenTemplateLeaves` proves `strip_gen`, `oschema_leaf`,
  `templ_leaf_gen` and `sized_compileT_gen`.

`sized_compileT_gen` is the bounded twin of `compileT` with no premise on the
placeholders (arity ≤ 3). Its leaf level `leafG` is exponential in the
placeholder level `u`, because closing over `m` free variables costs `3m`
levels and `m` can be as large as the code. The bound remains a fixed-height
tower.

**Next: the `L` inductions**, in dependency order:
- `fun_MT`/`slot_MT` and `LMatch` (`mVal`);
- `LNumOK`;
- the driver steps (`LDriverSteps`: `compiled` + Hilbert combinators) and
  `driverT` (induction over formula structure);
- `glue` (`LGlue1–4`, induction on complexity) and `qPremise`;
- `peel`/`peel_close`;
- `sep_base`/`repl_base` and the obligations.

The pattern for each: replace `compiled` by `sized_compileT_gen` at an
explicit placeholder level, and `⨀`/`K!_intro` by the `SizedProof`
combinators.

**Drop-in for the L inductions.** `ZFCinPA.SizedLPlumbing.compiledLe` is the bounded replacement for `LDriverSteps.compiled`/`LGlue1.compiledG`. A template `h : templTheory ⊢ σ` compiles at arbitrary placeholders of level `u ≥ 2` within level `cExpG (tmA h) (tmB h) u + tmK h + 1` on the `DLv` scale. The constants are read off `h.get.toProof2`. `stg_lvB` collapses the compiler's stage tower into one level per stage.

## Stage 3b: the first bounded `L` inductions (2026-10-29)

Three internal inductions of the constructible-universe interpretation now
have bounded twins on the `DLv` scale, axioms `propext`, `Classical.choice`,
`Quot.sound` (`ZFCinPA.SizedLAudit`):

| Bounded twin | Source | Level |
| --- | --- | --- |
| `SizedLGlue1.fun_MT_leJ` | `LGlue1.fun_MT` | `wF J + 10 i` for `i ≤ J` |
| `SizedLNumOK.numOK_leJ` | `LNumOK.numOK` | `wN J + 10 i` for `i ≤ J` |
| `SizedLNumOK.numOK_right_leJ` | `LGlue1.numOK_right` | `wN J + 10 a + 3` |
| `SizedLSlot.slot_MT_leJ` | `LGlue1.slot_MT` | `wSl J + 20 j` for `a < j ≤ J` |

**The fixed-target pattern.** Each induction fixes its target `J` first and
bounds every placeholder up to `J` by one level: `uM J = Cm·2^(4J) + Cm + 2`
for the matching codes, `uN J = Cn + 6J` for numeral chains
(`numChain_le`: one chain step is three pairings, six levels), and
`uS J = uM J + uN J + Ce + J + 6` for the slot tuples, which also hold
`x = &a` (`xT_le`, linear in `a`). The templates then compile at one fixed
level, `compiledLe` at `u J`, and each induction step adds a constant number
of levels. The motive is a `Σ₁` predicate with the base level abstracted as
a variable `W0`.

**Combinators driven by levels** (`SizedLNumOK`): `imp_ante_le` (the
antecedent of an implication of level `m` has level `10(m+1)`), `dmdpL`,
`dk_introL`, `dk_rightL` (∧-elimination by a cut on the conjunction; its
negation costs the factor `10`), `K6_le`, `top_le`, and `K8_le`
(`SizedLSlot`).

**Definability trap.** `definability` (aesop) fails with "goal was not
normalised" on a motive applying the two-argument `slotVal`, whether or not a
bounded quantifier is present. `slot_MT_leJ` therefore inducts along the
diagonal `j = b + 1 + d` for each fixed `d`, the recursion `slot_MT` actually
uses (slot `b+1` of `M_{j+1}` from slot `b` of `M_j`), with the sequent
packaged as the unary `diagSeq d` whose definability instance is an explicit
composition.

**Next:** the driver steps (`LDriverSteps`) and `driverT`; then `glue`
(`LGlue1–4`) and `qPremise`; `peel`/`peel_close`; `sep_base`/`repl_base` and
the obligations.

## Stage 3b: the bounded `hSchema` driver (2026-10-29)

`SizedDriver.driver_le` is the bounded twin of `LDriver.driver`: for a target
`M` and every semiformula `p` of level `n` with `n + p ≤ M`, a function code
`F` with `F.val ≤ lvB (Gd M p)` makes the reflection invariant of
`envForm n p` derivable within `Wd M + 60 + 40 p` on the `DLv` scale. The
axioms are `propext`, `Classical.choice`, `Quot.sound` (`SizedLAudit`).

**Levels.** The placeholders are environment transforms
(`SizedEnvForm.envForm_le`: `envForm n p ≤ lvB (Eb + 100 n + 200 p)`) and
numeral chains, all at level `A0 M`. A compound function code is a fixed
translation of the codes of its parts, which multiplies the level by `tB`, so
the codes live at `Gd M q = Ad M · 2^(Kd q)` with `Kd = 2 tB + 2`;
`Gd_grow` (`tB (Gd x + 1) ≤ Gd (x + 1)`) absorbs one compound step. Every
step therefore compiles at the single level `uD M = Gd M M`, and each of the
eight step lemmas (`and/or/neg/top_base/bot_base/atom/ex/all_step_le`; the
atom lemma covers both the membership and the equality template) adds 30
derivation levels above the working level `wD (uD M)`.

**The swapped premise.** The function-code definitions `maxDefF`, `eqDefF`,
`succDefF` translate to `∀∀(F₅[swap] ↔ G[swap])`, so the closing premise of a
step is `∀∀(A[swap] ↔ A[swap])`, not `∀∀(A ↔ A)`. The unbounded proof's
generic `all₂_iff_self _` hid this; the bounded `dall2_swap` (level
`10000 a + 16000`) bounds `A.subst swapV` by `tsubst_le_n`.

**Module split.** The driver is split for memory: `SizedDriverComb`
(combinators, `dall2_iff`), `SizedDriverLevels` (`tD`, `cD`, `wD`,
`invT_le`, `dall2_swap`), `SizedStepConn/Neg/Atom/Quant` (the steps, facade
`SizedDriverSteps`), `SizedDriverBase` (constants, the predicate `ΘB` and its
definability), `SizedDriverAtoms/Conn/Quant` (the eight induction cases as
standalone lemmas about `ΘB (Ad M) Kd (Wd M + 60) M`), and `SizedDriver`
(the induction itself). Every module elaborates at the import baseline
(about 3.4 GB here) within 30 s.

**Trap: never let `Nat` defeq see `tA (emb template)`.** The first version
summed eleven `tA (Rewriting.emb σ)` terms into `tD` and proved
`tA (emb σ) ≤ tD` by `unfold tD; omega`. One declaration passed 28 GB. Both
`omega`'s atom lookup (`isDefEq` against every earlier atom) and plain
unification of `tA X + ?k =?= tD` make the elaborator `whnf` a summand while
looking for a numeral, which evaluates the translation size of a whole
template. The fix is `irreducible_def` summands (`sD_*`, `sB_*`) in a
right-nested sum, with each bound proved as
`rw [← sD_x_def]; unfold tD; exact sumR (… (Nat.le_add_right _ _))`. The same
pattern with three or four summands in `SizedLGlue1`, `SizedLNumOK` and
`SizedLSlot` was cheap enough to go unnoticed.

**Next:** `glue` (`LGlue1–4`) and `qPremise`; `peel`/`peel_close`;
`sep_base`/`repl_base` and the obligations; the assembly into
`ConstructibleInterpretationBound.provableLe_falsum_ZF_of_ZFC`.

## Internal rank window for the smaller adaptive equation

The [rank-window client](reviews/adaptive-rank-window2011-root.md) derives
`24 ≤ R` and `R+q³+q+1 ≤ q⁴` in arbitrary IΣ₁ models directly from a zero
of the actual current 13-variable expression. The first-carrier gap and
current mask bounds are discharged; no index relationship or input power is
assumed. Strong-index recovery, full internal converse and the HA transfer
for this smaller equation remain open.

The companion [main-root congruence](reviews/adaptive-main-congruence2011-root.md)
uses the actual positive `q³` quotient for Y and the oriented main root to
establish an exact additive congruence modulo `q⁵`, with the same canonical
rank. It does not cancel the variable factor or establish an index relation;
those remain necessary for the smaller equation's internal equivalence.

The generic [factor-three cancellation](reviews/adaptive-factor-three2011-root.md)
now works in every selected IΣ₁ model even when three divides the modulus:
from `q³ | Y` and `q⁵ | (3+4Y(X+1))t` it derives `q⁴ | t`. Applying
this to the literal rank difference requires a separate client.

The [literal rank congruence](reviews/adaptive-rank-congruence2011-root.md)
now binds factor-three cancellation to an actual current adaptive zero and
derives `q⁴ | magnitude(R+1,k)` in arbitrary IΣ₁ models, without assuming
a sign for the difference or coprimality with three. Exact index recovery,
the converse, and the HA transfer remain open.

The [first Pell-index residue](reviews/adaptive-early-index2011-root.md)
now follows from the literal adaptive zero: `(2n) mod q⁴ = R+1`, with
explicit lower bounds and the original classified-root coordinates. The
exact first/main index comparison and the full internal equivalence remain
open.

The [first/main Pell-index comparison](reviews/adaptive-index-comparison2011-root.md)
now derives `13 ≤ n < m`, `14 ≤ m`, and `2R < c` from the literal adaptive
zero, retaining the rank residue and both root representations. The exact
index equality and full internal equivalence still require proof.

The [adaptive strong norm](reviews/adaptive-strong-norm2011-root.md) now
derives `I²+Δ=Δf²` from the literal zero, matching the generic half-index
theorem’s normalized strong equation. The auxiliary norm, signed residues
and full half-index application are separate obligations.

The [adaptive auxiliary norm](reviews/adaptive-aux-norm2011-root.md) now
derives `I²z²+y²=1+I²y²` from the literal zero, using the magnitudes of
the actual signed auxiliary pair. The signed congruences and generic
half-index application remain separate obligations.

The [exact adaptive Pell-index theorem](reviews/adaptive-exact-indices2011-root.md)
now derives `m=R`, `2n=R+1`, and `k=R+1+4Q·t` from the literal current
zero in arbitrary IΣ₁ models, retaining both actual root representations.
Its half-index prerequisite chain was independently rebuilt from current
source. Power recovery, internal converse and HA transfer remain open.

The [adaptive power projection](reviews/adaptive-power-projection2011-root.md)
now derives `q | 3X` and `q ≤ 3X` from the literal current zero. Power
recovery itself and the internal converse remain open.

The [current adaptive X bound](reviews/adaptive-power-lower2011-root.md)
now derives `16 ≤ X` from the literal zero and fixed radix-47 port. This
supplies a growth-theorem premise, not the power representation itself.

The [adaptive Pell growth theorem](reviews/adaptive-power-growth2011-root.md)
now derives `Exp.exp R < Y` from an actual current zero, using the exact
indices and X bound. Its two current-source prerequisites were independently
rebuilt; power identity and radix alignment are separate clients.

The [adaptive power recovery](reviews/adaptive-power-finish2011-root.md)
now derives `X = Exp.exp R` from the actual current natural zero in every
selected IΣ₁ model. It does not assume `q | X`; radix alignment, full
soundness, the converse and the HA/PRA transfers remain open.

The [adaptive Mersenne cancellation](reviews/adaptive-mersenne2011-root.md)
now removes the factor three from `q | 3·2^R` for the actual Mersenne-port
shape, including arbitrary internal exponents. The actual radix client is
a separate binding.

The [actual adaptive radix theorem](reviews/adaptive-radix2011-root.md)
now derives positive internal `N` and `w` with `q=2^(width·N)`,
`width·N≤R`, `w=2^(R−width·N)`, and `X=q·w` from the literal current
zero, retaining both exponential graphs. Transport/window soundness,
the internal converse and the HA/PRA transfers remain open.
