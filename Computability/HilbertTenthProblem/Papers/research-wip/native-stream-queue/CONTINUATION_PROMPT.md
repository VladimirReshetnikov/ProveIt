# Continuation: universal straight-line certificates

> Historical handoff below. The current comparison frontier is
> **75=41M+34A**: see [the complete proof](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
> and [consolidated checker](../../verification/explore_fixed_raw_universal_75.py).
> The original source has30 positive witnesses and19 equations; the
> [signed projection](complete75_signed_projection_elimination101.md) retains75
> with20 positive witnesses and nine equations.
>
> The current single-polynomial frontier is **88=47M+41A**, with19 positive
> witnesses and exact degree151: see [the coupled-unit proof](complete75_coupled_index_linear88.md).
> It has the same positive zeros as [positive-root89](complete75_positive_root89.md)
> under the full compiler mask contract. The [linear input modulus](complete75_linear_input_modulus89.md)
> gives89/degree135, superseding89/148. The positive-root coordinate gives a bijection with the
> [reversed auxiliary degree160 source](complete75_reversed_auxiliary89.md).
> It builds on the [bounded projection99](complete75_bounded_projection_elimination99.md),
> [norm product91](complete75_norm_product91.md), and
> [shifted transport90](complete75_norm_product90.md). The proofs recover
> auxiliary signs and the original positive quotient in a specific order;
> do not assume intermediate computed coordinates are positive off the zero set.
> The [positive-root partitions](complete75_positive_root_degree_tradeoffs.md)
> give the earlier94/degree84 and92/degree122. The [coupled-unit partitions](complete75_coupled88_degree_tradeoffs.md)
> add91/degree130 and93/degree90, superseding93/118. The new
> [linear-modulus partitions](complete75_linear_input_degree_tradeoffs.md)
> add90/132,92/114,94/80,95/72,96/62 and97/56. The
> [positive auxiliary gap](complete75_auxiliary_gap_degree_tradeoffs.md)
> further gives90/131,91/128,98/54 and99/52. All retain19 positive
> witnesses. Preserve the paid strong equation and both ratio slacks;
> the coupled linear unit is recovered by the complete sign proof.
> The comparison bound75 and
> polynomial bound88 are separate measures.
>
> The README indexes the four-row queue simulator, binaryFIFO58 and
> ternaryFIFO66, row-local controller obstruction, residue-affine pumping,
> PCP/matrix continuations and rejected shortcuts. Controller arithmetic
> and ordinary-input loading remain unpaid for the coded queue simulator.
> In the nonabsorbing63 binary family, all read-only cases are decidable;
> width is bounded outside the cone and on the additional c=-b,a/b<1
> boundary. The [odd-controller orbit analysis](binary_odd_controller_orbit.md)
> gives exact guarded duration cutoffs at each fixed width. Other cases
> inside the cone remain open; nonzero terminal states forbid free padding.
> The [factored counter map](residue_affine_factored_counter_step.md) escapes
> unit-slope pumping and pays10B+8 scalar guards, but its prime-power input
> loading and history remain unpaid.
>
> The [two-stack substrate](two_stack_affine_input_step.md) has a two-operation
> ordinary-input prefix. [Factored selectors](two_stack_factored_selector_step.md)
> lower its exact scalar step to8B+18 for a full B=9K table, with eight
> positive witnesses and seven equations. A fixed-t polynomial costs
> (8B+39)t+1. The [typed-history audit](two_stack_polycyclic_history_obstruction.md)
> retains stack guards with prefix maps and identifies their loss in direct
> inverse-group products. Exact bounded-depth linear encodings need dimension
> N=2^(H+1)-1 and a paid2N positive basis loader. A
> [typed prefix merge](typed_prefix_normal_form_merge25.md) costs25 operations,
> four auxiliary witnesses and seven equations. Fixed trees cost25(t-1);
> output typing is proved. The [singleton extension](typed_prefix_singleton_merge31.md)
> costs31 and supplies exact binary empty tests plus a typed ordinary-input
> endpoint in two affine operations. Fixed flags admit cheaper schedules.
> Variable leaf selection, synchronized control and arbitrary duration
> remain unpaid.
>
> Next targets are below75 comparisons or below88 polynomial operations,
> with degree and positivity counted. These are reviewed mathematical
> proofs with exact source audits, not Lean formalizations.

The previous cone/singleton proposal is now implemented and proved in
merge31: positive flags avoid their two explicit decodings. Its root
condition V=1,U=kappa*x+lambda uses the root's already proved power typing.
Keep the fixed-word and uniform-history scopes separate. Precomputed
subtree flags are legitimate only when the leaf flags are source constants;
variable selected branches need a paid replacement. The next substantive
history task is a uniform synchronized selected-word/tree certificate,
rather than another unchecked input or empty-test conversion.

For algebraic work, the strong factor1+T^2-K cannot be-1 modulo4, so any
integer product zero forces T^2=K before substitutions. The one-gate
[degree162 reduction](complete75_strong_reduction89.md) preserves even the
full integer zero set. The degree160 successor also uses V=of-c and reverses
the linear unit; keeping the old orientation admits a formal kernel sign
collision. Preserve the strengthened R+2 bounds and the order of index
recovery when attempting further rewrites.

The [positive first-root coordinate](complete75_positive_root89.md) then
replaces tau_old by tau_gap=tau_old-XY^2*k. This gap is strictly positive
on every parent zero. The exact first factor is now
`tau_gap^2+XY^2*k*(2*tau_gap-k)`, degree14 instead of26, at the same
six operations. Do not replace the computed signed difference by an
unconstrained positive witness: both original ratio slacks remain needed.

The [coupled88 successor](complete75_coupled_index_linear88.md) shares
k-hE between Nk and Lnew=V-jc+k-hE. Its product initially leaves
Nk=Nt=-1 as an extra branch. Restore the entire half-binomial42 kernel
at p=R-2 before using its population threshold; the true compiler masks
then imply popcount(p)<=3t+1 instead of the required3t+2. Both low-bit
mask congruences and popcount(MC)+popcount(MF)=d are essential here.
Do not claim equivalence for arbitrary masks with only size bounds.
With the strong comparison separated, the remaining factor degrees are
(14,22,42,28,9,5,9), with78 paid definition operations. Grouping as
(14+42+9,22+28+5+9) gives91/130; grouping as(42,14+28,22+9+5+9)
gives93/90. Their sums of squares preserve the same positive zeros.
Exhaustive partitions of these factors give no further displayed tradeoff;
this is a scope restriction, not an optimality theorem for other circuits.

The [linear-modulus successor](complete75_linear_input_modulus89.md) adds
one gate to coupled88 and replaces kappa=u+delta*Delta by
kappa=u+delta*(a+1), reducing the input norm degree from42 to26.
The coupled sign proof uses that norm only to exclude its negative unit
modulo4. After the main kernel and transport bounds are restored, recover
the positive input Pell index v<R and use psi_A(v)=v modulo a+1 to obtain
v=u. The odd-index congruence then reconstructs the old positive delta.
The exact coordinate map is delta_new=(a+3)delta_old; it preserves all
positive solutions. The new seven-factor weights are(14,22,26,28,9,5,9),
with79 paid definitions. The degree-tradeoff packet enumerates five fixed
partition families and proves each displayed exact degree; its scope is
not an arithmetic lower bound. Preserve the complete strong comparison
when moving it outside the unit product.

The [auxiliary-gap successor](complete75_auxiliary_gap_degree_tradeoffs.md)
replaces supplied y by e=y-V, reconstructing y=V+e with one addition.
Computed y can be signed away from zeros. First exclude negative norm
units by the retained first-norm descent and modulo4 arguments (the
auxiliary norm exclusion does not need y positive). Then use
main/first/strong norms and weak transport/index bounds to obtain
f>2c and V=of-c>c>1. Only then invoke the old positive-y theorem.
Its inverse gap is positive because (K-1)(y²-V²)=V²-1>0. The auxiliary
norm degree drops28 to24; four new points are90/131,91/128,98/54,99/52.
The five-family partition search is exhaustive only within its stated
factor schedules, not a global lower bound.

The [group-commutator route](group_commutator_universal_substrate.md) is now
proved as a universal computational substrate. For an r.e. positive set S,
`G_S=<a,b | [b^-n*a*b^n,a]=1 for n in S>` recognizes exactly S via the
input commutator. Its proof identifies G_S with the semidirect product
of the graph group on a_i, edges |i-j| in S, by simultaneous shift.
A missing-edge retraction proves the converse in the graph-group kernel.

An explicitly cited effective Higman embedding, with two-generator finite
output, followed by fresh named a,b gives a four-generator presentation H.
The finite fibre-product subgroup M(H) has diagonal and relator generators.
Conjugate it once to `(a,1) M(H) (a^-1,1)`: then the repeated pair
`(b^-x*a*b^x,b^-x*a*b^x)` is a member exactly for x in S. All presentation
and subgroup matrices are program constants. The general embedding compiler
has not been run to produce a universal finite presentation here.

The [faithful matrix loader](group_unipotent_input_loaders.md) uses the
Schreier basis U^3,B,UBU^-1,U^2BU^-2 for U=[[1,4],[0,1]],B=[[1,0],[1,1]].
The fixed quadratic target consists of two copies of
`[[1+12x,12],[-12x^2,1-12x]]`, with **5=2M+3A** paid scalar operations,
no witnesses, and nonnegative literal numerals. Elementary proofs cover
freeness; a6-operation alternative handles arbitrary ranks with the same
named matrices. The complete matrix compiler below now supplies a positive
Diophantine certificate for their variable-length selected products.
One fixed subgroup/finite matrix alphabet can serve every program:
choose U={2^p*(2x+1):x in S_p}, then precompute kappa=2^(p+1),lambda=2^p.
Use the swapped free basis a=[[1,1],[0,1]], b=[[1,0],[12,1]] and
fold the program prefix into q=(12*kappa)*x+12*lambda. The target has
two copies of [[1+q,1],[-q^2,1-q]], computed in **6=2M+4A** operations.
The alphabet is independent ofp andx; these powers and products are
fixed program numerals, not free runtime exponentiation.
The [affine obstruction](group_affine_input_obstruction.md) proves that two
entrywise affine SL2 target blocks can produce only cosets of subgroups
ofZ (or empty sets), even in a general SL4 subgroup. Thus degree2 is sharp
for this interface, but there is no arithmetic-operation lower bound.
An affine SL3 counterexample accepts exactly{1,2}, bounding the theorem.
The loader alone supplies no complete Diophantine bound.
The [four-register history](group_four_register_history.md) evaluates each
block on (q,1), q=2^t. The length-t shear bound and determinant one recover
the whole target matrix from that vector; no input-height bound is needed.
Shift by D=q^2 for positive fields. The paid boundary costs10, and the
conditional four-lane packed interface costs43 with20 positive history
fields, excluding q and P. The [canonical-history successor47](group_four_register_canonical_history47.md)
changes B to8q^2 and pays sum_i H_i+beta=P. Every H_i then has canonical
digits in[0,B). A simultaneous first-disagreement induction recovers the
actual small digits from the recurrence; no separate digit-range predicate
is required. Its21 positive history fields exclude q and P.

The [selected-source successor63](native_binary_masked_selection63.md)
implements the checksum-defined scale and shares the F1+F3 port with it.
The unrestricted AND costs63, prescribed AND64, and eight-product batches
117/119. The exclusive prescribed119 has23 auxiliaries and17 equations.
Soundness allows canonical history digits to be zero; its positive global
bound needs the actual small digits and mutual exclusion for completeness.
Do not confuse any selector kernel scale with the physical height q.

The [regular macro controller](group_regular_macro_controller.md) pays
one Boolean edge per cell, ordered state adjacency and eight selectors in
7m+3h+p+60 operations,25 equations,m+22 auxiliaries. Here m=2^h is the
padded edge count and p the literal output-sum cost. It assumes dyadic B,P;
P dyadic and the repunit alone do not type B. Computed F1 is positive only
after the paid edge checksum, which must precede the binary theorem.

The [geometry47](group_linked_binary_geometry47.md) uses the unchanged
binary43 core with r=J, s odd, X>J and J>B, sharing B=8q^2. It proves
q=2^popcount(J) before any repunit or selector semantics. Its pre-power
bootstrap is J>=9, X>J,Y>=3, followed by Y>=X^J from the lower Pell ratio.
Only then use the small-error estimate to recover X and the central
binomial valuation. The proof includes every positive converse coordinate;
standalone computation of B costs two extra products.

The [complete compiler](group_complete_matrix_compiler.md) combines all
four actual DAGs at7m+3h+p+273 operations,60 equations,m+87 witnesses.
The single polynomial costs7m+3h+p+452 and has exact degree
max(112,12m+16). Its soundness order avoids circular typing:
geometry makes q and B dyadic; prescribed selection independently types P;
the repunit gives P=B^t,J with popcount(J)=t, hence q=2^t; controller
types the path and selectors; the selection and canonical-history theorems
then recover the actual trace and target matrices. Completeness pads with
hub idle steps until t>=2 and B>m. The three Pell cores have separate
namespaces, and B,J,H,Shat,Zhat,q,P are explicitly shared.

The [shared-typing successor](group_shared_typing_matrix_compiler.md) replaces
the controller's57-gate kernel with upper lanes in the selected-source AND.
It adds7 gates, removes13 equations and20 witnesses, and costs50 fewer
certificate operations. Before decoding the joined regions, scalar edge
checksum and port equations give0<=S_i<=J, hence (B-1)S_i<=P-1 and Mb<P^8.
That pretyping bound is essential; without it a low mask carry can fake the
upper subset test. The retained AND scale is16P^(m+8), independent of the
height q. Its positive core is reconstructed afresh, not copied from an
incompatible old scale.

[Sparse macro flow](group_sparse_macro_flow.md) groups the paid checksum
sum and shares internal-edge state weights. Its exact table-dependent cost
f_flow is at most twice total macro length. The [combined source](group_shared_sparse_matrix_compiler.md)
also shares3min(h,3) literal powers/repunits/B-1 gates. Every residual
remains identical to the shared-typing parent. Finally, [computed selector
ports](group_computed_selector_ports.md) substitute the eight positive port
definitions and remove their supplied witnesses and comparisons. Positivity
is unconditional from positive edge hats; a stable topological reorder
puts the existing port gates before their history/AND consumers.

The previous matrix-equality comparison count is
C=3m+3h+p+222+f_flow-3min(h,3), with39 equations andm+59 witnesses.
Its polynomial costsC+116 and has exact degree12m+112. This trades degree
against the original separate-kernel compiler. A fixed universal alphabet
is supplied by the effective group theorem but has not been numerically
materialized. Do not infer a numerical universal bound below75/88.

The [Gram scalar-zero/mortality route](group_gram_zero_mortality.md) is a
new endpoint alternative. The symmetric-square action on two Gram triples
and one constant coordinate gives a fixed7D alphabet; torsion-free Γ is
essential to turning the minimum Frobenius norm into exact matrix equality.
Its positive quartic input column costs12. The rank-one sentinel can repeat
freely; a fixed conjugation gives a nonnegative single-column input matrix
at13=5M8A. Other fixed generators remain signed, as finite Boolean support
closure would make an entirely nonnegative fixed-alphabet problem decidable.
A fixed-word positive certificate costs4t+17; its polynomial costs10t+19
at exact degree8. Its variable word, macro control and uniform history are
still unpaid. Preserve this distinction from the completed four-register
compiler. Next targets are cheaper complete kernels or computational
substrates, with ordinary input and all typing obligations accounted for.

The new [projective endpoint](group_projective_zero_mortality6.md) is the
preferred subgroup interface. For the swapped rank-four Schreier group,
Gamma is the kernel of the lower4 shear exponent modulo3. Mod4 diagonal
congruences exclude negative triangular elements, giving lower stabilizer
exactly<b>. Thus P(-1,r+1)=e2 iff P=b^n L_r. For a pair in the conjugated
Mihailova subgroup, pull its equality into the embedded original G_U;
the b-exponent gives equal ambiguities, and graph-kernel abelianization
forces that common index zero. Do not assume these homomorphisms extend
to the finite presentation H. The vector loader is2 operations using
u=alpha*x+(beta+1); the6D scalar/mortality sentinel loader is3=2M1A.

The [range-typed compiler](group_range_projective_compiler.md) removes the
entire geometry47 kernel. Set D=u+height_slack, B=8D; retain the repunit,
controller and selected-source tests. Join two more AND regions:
Hb subset (2D-1)J*K8 in eight lanes, and B AND(B-1)=0 in two lanes.
The new scale is16P^(m+18). Before typing, the scalar checksum/port and
history/output bounds give all region bounds, including B<=P<P².
Native AND then types P; the high region types B; repunit givesP=B^t
for t>=1. The range region gives history digits in[0,2D). Successive
modulo-B recurrence coefficients have absolute value<3D<B, proving the
exact signed trace without a duration-height relation. Completeness chooses
D dyadic above the finite trace and the macro table; no length-height
link or free digit condition remains.

Its certificate costs C=3m+3h+p+185+f_flow-3min(h,3), with26 equations,
m+40 witnesses; the polynomial isC+77,degree12m+232. The [computed kernel
fields](group_projective_computed_kernel_fields.md) give two exact positive
bijections. Eliminating a,d,k,s yields22 equations,m+36 witnesses,C+65,
same degree. Adding c,r gives20 equations,m+34 witnesses,C+59, with
exact degree24m+444. The source certificate cost staysC. In particular
computed r has degree4(m+18)-2, so do not claim its substitution preserves
degree. All expressions are positive before using any comparison; whole
source and SOS identities also hold on signed assignments.

The [shifted boundary](group_projective_shifted_boundary.md) reflects every
fixed shear sign, starts at(1,u), and uses origin D-1. It saves one addition
without changing the exact degrees. The [unit product](group_projective_unit_product.md)
merges main norm, auxiliary norm and checksum into one comparison: both
norms exclude-1 modulo4 on arbitrary integer assignments. The certificate
adds2M, but two fewer equations save four polynomial operations. Optional
controller-mask reuse (epsilon=1,m>=8) saves1M by replacing J*K8 with the
already paid J*K_m and expanding the range region from8 to m lanes.
Its scale is16P^L, L=m+18 normally or2m+10 with reuse; fresh native
extension must use this actual scale.

The [scalar projections](group_projective_scalar_projections.md) then
compute J from the edge checksum and remove the radix-margin coordinate.
Use D=u+height_slack+m so B>m without its old comparison. Before typing,
J>=0; the history bound givesP>=5 and the retained repunit forcesJ>0.
Optional chi=1 computes P=(B-1)J+1 too. It saves another comparison and
witness at unchanged certificate cost, but makes P degree2. Keep this
positivity argument before invoking native typing.

The [padded-program specialization](group_projective_padded_program_margin.md)
restores D=u+height_slack and saves1A whenever fixed alpha+beta+1>=m.
It is a positive solution bijection with the unit-product parent after
restoring J,B-m and optionalP. Its signed identity with the general
scalar parent translates height_slack by-m; do not call that translation
a positive bijection. To supply the fixed margin uniformly, define
S_p=T_v2(p+1), construct the alphabet for U_pad={2^p(2x+1):x in S_p}
once, determine m, then choose p_e=2^e(2m+1)-1 for the requested program.
The affine constants alpha=12*2^(p_e+1),beta=12*2^p_e supply the margin.
No runtime gate is added. This specifies a new padded enumeration and
does not claim an unchanged alphabet for an earlier unspecified one.

The resulting cost is C=3m+3h+p+185+f_flow-3min(h,3)-epsilon. Four computed
fields give18-chi equations,m+34-chi witnesses,C+53-3chi polynomial gates;
six give16-chi equations,m+32-chi witnesses,C+47-3chi gates. With nu=1+chi,
exact degrees are12nu*L+16 (four) andnu*(32L+4m+60)+38 (six).
For the illustrative ten-letter table, epsilon=chi=1 gives258/302,
15 equations,47 witnesses and degree2974. It is not a numerical universal
alphabet. Root and independent proof/source reviewers passed these packets.
Next targets include reducing the one AND kernel, replacing its packing,
or a smaller effective macro table; no separate duration-height kernel
is needed.

The [positive first-root unit](group_projective_first_norm_unit.md) uses
V=XY², k=eta+zeta and g=2tau+1-2Vk>0. Its six-gate norm
N0=g²+4Vk(g-k) costs4M2A like the old triangular norm. N0=-1 is impossible
modulo4. Joining N0 to the three-unit product adds1M and removes one
comparison, saving2A in SOS. Restore tau=Vk+(g-1)/2 after N0=1 proves
g odd; both ratio slacks stay positive and unchanged. Offzero identities
use a rational parent root if g is even. Keeping N0 separate costs the
same as the parent but lowers four-field degree to10nu L+32.

The [joint bound](group_projective_joint_bound.md) changes B=8D to16D at
the same gate cost and retains Hsum+Zsum+b=P+1. Restore the positive
parent bounds P-Hsum=Zsum+b-1 and Hsum+b before any native typing.
On every typed parent zero, Hsum+sum Zi<=5(2D-1)J, so its inverse
b=P-Hsum-sum Zi-7 is at least(6D+4)J-6>0. It saves another comparison,
positive witness and3SOS gates, with unchanged degrees. Computed P now
has highest part16*(alpha*x+height_slack)*sum Ehat, not coefficient8.

The [complete composition](group_projective_joint_first_norm.md) keeps
certificate base C as defined above and costs C+1 with the norm merged.
Four fields give16-chi equations,m+33-chi witnesses,C+48-3chi polynomial
gates,degree16nu L+42; six give14-chi equations,m+31-chi witnesses,
C+42-3chi gates,degree nu*(38L+4m+60)+48. The separate option costs C
in the certificate and two more SOS gates, at degrees10nu L+32 (four)
or nu*(32L+4m+60)+38 (six). Both rewrites compose without losing a
positivity hypothesis. The ten-letter example with epsilon=chi=1 is
259/297,13 equations,46 witnesses,degree3488; separate-root258/299 has
degree2974. These are illustrative fixed-table counts.

The [index-unit successor](group_projective_index_unit.md) merges
Nk=k-hE-r with the product, saving1SOS addition. Initially Nk=Q=+/-1.
With four positive native fields and q>=16, their signed checksum still
gives r>=q^3+q^2+q+1 and r<q^4. X>r and Y>=q implyE>2r+1.
First k=psi_(2XY²+1)(n) gives n>=r-1; c>kY and the larger first base
give main p>n, hence c>A*Delta²,c>2p,c>2(2r+1). The independent
strong-rank and half-index lemmas now recover p=2r+1 without assuming
Q=1. Then n=r+/-1 exactly, and the negative case p=2n+3 contradicts
psi_A(2n)=2A*psi_(2A²-1)(n)>k(Y+1). Both unit signs become positive
before applying the parent typing theorem.

The [coupled-linear successor](group_projective_coupled_linear_unit.md)
uses K=k-hE and V=of-c, replaces the auxiliary norm's ordinate by V,
and merges Lunit=V-jc+2K. Deleting r+1,2r+1,jc-(2r+1) pays for its
three additions; one new product removes another comparison and saves
2SOS additions. Initially Nk=epsilon_k,Lunit=lambda,Q=epsilon_k*lambda.
Recover main p=2K-lambda and first n=K using the same weak-checksum
rank argument with targets up to2r+3. The upper ratio forceslambda=1.
If epsilon_k=1, restore the parent directly. If epsilon_k=-1, restore
F0_old=F0-2,r_old=r-2,bound_beta_old=bound_beta+2. The padded ports and
q divisible by16 give F0=3 mod16, so every restored supplied coordinate
is positive. Packed r changes by exactly-2; both input ports and every
outer history/controller field stay fixed. This is same-input equivalence,
not equality of positive witness sets. Keep these branches separate.

Composed with the joint bound, the coupled certificate costs C+4.
Four fields give14-chi equations,m+33-chi witnesses,C+45-3chi polynomial
gates,degree24nu L+54. Six give12-chi equations,m+31-chi witnesses,
C+39-3chi gates,degree nu*(40L+2m+30)+60. The ten-letter epsilon=chi=1
example is262/294,11 equations,46 witnesses,degree3544; with epsilon=0
its polynomial is295 at degree2904. No numerical universal alphabet is
instantiated. The unconditional negative-norm exclusions still precede
all rank and typing arguments, and the full strong equality remains.

Do not remove the output bound instead of combining it. The
[exact carry counterexample](group_projective_output_bound_obstruction.md)
uses fixed macros3..8, whose first block preserves first coordinate1
and can never reach e2. A true word8^(u-1),6,4^u ends at(1,0,0,1).
With Omega=P/B and G=Omega*P*(P-1), replacing true output fields by
Z0=G,Z1=G+Omega,Z2=0,Z3=T3-Omega preserves packed Z, but changes the
two paired differences by-Omega,+Omega. All claimed endpoint residuals
then vanish. The exact scalar AND supplies a positive native extension
for every input, while the omitted output slack is negative. This
refutes generic fixed-table soundness; even Zb<P^8 remains true.

The [four-dimensional reset construction](group_two_reset_mortality4.md)
uses a two-operation affine nonnegative rank-two idempotent reset R.
A word with exactly two resets has zero product iff both blocks vanish
at its common bridge word. Such a zero product exists iff the input
belongs to the universal set. Unrestricted resets destroy synchronization: two different bridges
kill the two blocks, and every input has a three-reset zero product.
The minimum is two for members and three for nonmembers. The restriction
R F*R is regular but its uniform selected-word certificate remains unpaid.

The primary75/88 frontier remains unchanged. An [exact input-translation
obstruction](complete75_input_bound_absorption_obstruction.md) rejects the
specific apparent87 shortcut that absorbs2d*x into alpha: x shifts by
M/gcd(2d,M), delta drops by2d/gcd(2d,M), and all eight units are invariant.
The odd Pell expansion proves the new delta stays positive at every old
zero, so every nonempty finite language acquires a false input.
The [first-norm ratio obstruction](complete75_first_norm_ratio_obstruction.md)
rejects a different apparent87 source that replaces zeta by k-2*tau_gap.
It loses c<k(Y+1). An explicit CRT construction gives full positive zeros
at every input for every fixed compiled constant tuple. It chooses
q=2^ell, R congruent to a bounded e moduloell, C>2^u, F=(K0+2^e)C,
and zplus=1+C*(2^R-2^e)/(q-1), then restores fresh main, strong auxiliary
and input Pell witnesses. The +1 in zplus is essential for transport
unit1. This is a proved all-input projection, stronger than its initial
same-input coordinate-bijection failure. Preserve the upper ratio slack.

The [Heisenberg audit](heisenberg_two_generator_membership.md) proves a
uniform four-witness representation for any two fixed H^r generators,
with graph cost18r+10 and polynomial cost27r+12, degree at most4. The
entire family is decidable, so it cannot by itself be universal. For
three letters, even strict pair bounds and strict weighted-triangle
bounds miss realizability: counts (m,2,2), pair data (1,1,2m-2), m>=3
are impossible. Preserve the global order obligation. Roman'kov's cited
universal compiler starts from H10 and is used only on a fixed positive
parameter slice; its unqualified signed statement needs an orientation
qualification.

This WIP snapshot is on ProveIt's branch `codex/diophantine-native-stream-wip`.
It preserves the unfinished end of the former Diophantine research session.
All paths and executable imports below are relative to this repository; no
access to the originating Windows machine or old repository is required.

Continue reducing the size of a complete straight-line arithmetic certificate
for universal Diophantine representation, starting from Jones's 1980 Theorem 5.
The original target was 129 operations. The established complete bound is now
**76 = 41 multiplications + 35 additions/subtractions**, with 30 positive
witnesses and 19 equations. This WIP branch does not claim a smaller complete
bound. Its new six/eight-operation results are conditional components.

## Contract and accounting

Fixed numerals have no cost. Each binary addition, subtraction or multiplication
costs one operation, including multiplication by a numeral. Register reuse and
equality comparisons are free. Exponentiation, divisibility, digit extraction
and radix conversion are not free primitives.

Preserve soundness and completeness for the full representation theorem.
Compiler/program numerals must be fixed independently of the varying ordinary
numerical input x. All existential coordinates must satisfy the stated strict
positivity convention. Do not replace ordinary input by a convenient coded
input without paying for the bridge. The established 76 construction treats
positive raw input; the queue components also cover zero, with explicit proofs.

Read applicable repository instructions and the nearest project README. Inspect
Git state and concurrent work. Continue in ProveIt, preserving unrelated work.
The old Diophantine repository has been merged into this one and is being
retired. Its historical `current/` directory is now
`Computability/HilbertTenthProblem/Papers/`.

## Reading order and preserved files

Start with the project README and these files under
`Computability/HilbertTenthProblem/Papers/`:

1. `1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` and
   `verification/explore_fixed_raw_universal_76.py/.json`.
2. `1980/ALTERNATIVE_UNIVERSAL_MACHINERY.md`, a large research map whose
   older paragraphs retain historical milestone counts.
3. `1980/EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md` and
   `1980/EXPLORATION_DYADIC_BALANCED_WRONG_INDEX.md`.
4. `1980/EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md` and
   `1980/EXPLORATION_DELAYED_BLANK_RAW_QUEUE.md`.
5. The new `1980/EXPLORATION_NATIVE_STREAM_RAW_QUEUE.md` and
   `verification/explore_native_stream_raw_queue.py/.json`.

The original task started from `1980/jones1980_theorem5_operations.tex`.
At the previous research audit, the operation-count TeX/PDF still presented
89 and its corresponding Lean milestone was 90. The 76 result is a constructive
mathematical proof with symbolic, sparse and modular checks, not a completed
Lean formalization of that optimized count. Recheck those publication and
formalization statuses before reporting them as current.

This directory also preserves:
- `audit_queue_base_three_streams.py`: independent scalar and genuine-history audit.
- `audit_delayed_blank_loader.py`: independently implemented delayed loader.
- `native_ternary_controller_encoding.md`: a correct conditional controller
  baseline, carry counterexamples, and a narrowly scoped encoding limitation.
- `COMPLETE76_BRIDGE_REWRITES.md` and
  `explore_complete76_bridge_rewrites.py/.json`: exact full-schedule rewrites
  that tie 76 or cost 77. They found no saving and are not a lower bound.

The other 66 untracked research files from the old current/ tree are preserved
in legacy-untracked/ with a hash manifest. They retain their historical WIP
status. Unselected tmp/ build products and miscellaneous scratch data are not
part of this handoff.

## Established 76 and open 75

The 76 ledger is 19 outer-encoding operations, 43 Pell-kernel operations and
14 input-bridge operations. Its important recent idea reuses the already
computed Pell power X=2^(2r+1) for temporal rotation. A fixed helical compiler,
power-of-five padded dimensions, and ignored Boolean bits arrange the required
alignment congruence at the actual packed index. The represented machine
recognizes the doubled set {2x : x in S}, while the certificate still takes
the original ordinary parameter x. See the proof for all compiler hypotheses.

A 75-operation candidate replaces the auxiliary expression (i*c^2)^2 by i*c^2.
Its exact schedule and positive completeness map are established; its full
soundness is **open**. The weakened 42-operation kernel admits wrong-index
solutions. A latest family has q=16, r=269, actual main index329 instead of539,
X=2^329 and Y=2^91, escaping a residue restriction that excluded an earlier
family. The compiler, transport and raw-input equations have not been assigned
in those counterexamples. Thus the kernel is refuted, but the full75 candidate
is neither proved nor refuted. Do not claim otherwise.

## New machine and native stream component

The new finite-state queue has nine symbols, exactly all ordered pairs of
ternary digits. Every transition removes one symbol and appends one symbol;
physical length is constant. Existential padding supplies enough space for
an accepting computation. A fixed normalizer establishes the canonical input
independently of padding, and genuine acceptance erases every symbol to zero.

Published predecessors give a 14-operation initialization/transport component
and a 13-operation delayed-loader successor. The latter turns a verified high
padding zero into a genuine blank. Both have complete machine contracts, but
their controller arithmetic and geometry remain unpaid. The last corresponding
old-repository milestone was 7e72a44142c9b3116422e3fd0d121474a68f9742; its sources
are already migrated and need no old-repository access.

The new formulation records only removed and appended trits in native base3:
D_i=sum_j d_(i,j)*3^j and A_i=sum_j a_(i,j)*3^j. If W=3^m is the queue-length
power, I_i the initial coordinate and F_i the final coordinate after t steps,

    D_i + 3^t F_i = I_i + W A_i.

At a zero endpoint this is D_i=I_i+W A_i. Conversely, with bounded streams and
the correct powers, the identity forces exactly the queue's actual heads.
A single synchronized controller path on the paired trits therefore proves
the actual queue run.

For initial I0=x, I1=L, L=3^ell, the arithmetic source is

    W=3L
    x+alpha=L
    D0=x+W*A0
    D1=L+W*A1

with positive alpha. It costs **6=3M+3A**. Adding the positive common bound

    D0+D1+beta=q

costs two additions, giving **8=3M+5A**. Power geometry L=3^ell, q=3^t and
the synchronized controller remain external hypotheses. The appended-word
bounds follow from the equations and removed-word bounds. All four streams
have strictly positive witnesses on genuine accepting runs, including x=0.

The author checker verifies 31,980 arbitrary scalar tuples, 131,160 forward
FIFO runs, and 463 genuine accepting histories totaling43,665 transitions.
It handles t=0 and t<m, paired-controller replay, zero endpoints, positive
streams and the common bound. The last erased symbol is #(0,1), which already
makes the joint bound strict without an extra step. Accepting zero loops also
permit extensions without changing the stream integers.

Fresh default receipt replay passed during the handoff. Earlier independent
conceptual/scalar/history audits passed. The final artifact's independent
review status is recorded in the adjacent README; do not substitute executable
checks for a complete proof review.

## Immediate bottleneck

The controller must be certified at the SAME native base-three time positions.
A fixed-numeral convolution compiler operating on wider cells cannot consume
these integers without a proved, paid conversion. Removing content histories
does not make that conversion free.

A sound baseline uses Boolean transition-selector streams and trit planes for
state codes, with true one-hot typing. This is expensive. Naive sums can carry
between positions: four unit selectors equal the ternary repunit11. Likewise,
huge free scalar state codes do not provide injective encodings of arbitrary
state words at all lengths. These are scoped obstructions, not lower bounds
on every controller verifier. Specialized controllers, nonlinear checks,
redundancy or different representations remain open.

A useful unfinished local observation is that Boolean ternary streams satisfy
A+B+C=H, H=(q-1)/2, exactly when they are coefficientwise exactly-one: residual
digits lie in[-1,2], so the first nonzero residual cannot be divisible by3.
Booleanity and the common word geometry still need to be paid. This observation
has not produced a competitive complete compiler.

## Unverified five-operation successor

This is only a proposal, with no completed implementation, proof or receipt.
Move the initial marker to the units position, I0=x,I1=1, and attempt

    x+alpha=W
    D0=x+W*A0
    D1=1+W*A1.

These expressions cost five operations before bounds, power geometry and
controller certification. A loader delaying two cells might convert two high
padding zeros to a genuine blank and a delimiter without changing x:
emit provisional delimiters in its first two steps, retain two raw cells,
then emit held predecessors while reading raw trits; at the provisional
delimiter boundary require the final two held raw digits to be zero and
finish with blank and delimiter. This needs a complete finite transition
definition, short-queue analysis, normalization and positivity proofs.

In particular W=1 is not excluded by an assumed power alone. One possible
argument uses the initial read and first append second coordinates both
equal1: modulo3, D1=1+W*A1 would then imply W=0 modulo3. This argument is
conditional on the proposed controller actually having those first-step
properties. Do not treat it or the loader as verified.

## Promising directions

- Co-design the machine and its arithmetic verifier. Queue/lag systems, cyclic
  tags, cellular automata, counters and rewriting calculi are candidates.
  Few states or short rules do not automatically mean few arithmetic operations.
- Reduce or replace the43-operation Pell kernel, while testing weakened index
  claims against existing counterexample families and the full compiler.
- Share registers across input, geometry, masks, transport and acceptance;
  such cross-interface reuse produced the largest established savings.
- Improve the14-operation input bridge or design a machine that directly uses
  ordinary x. Avoid silently outsourcing variable input conversion.
- Settle full75 soundness, or build an actual false raw-input instance satisfying
  every equation. A kernel counterexample alone does not settle that question.
- Use the research overview to avoid repeating already refuted deletions, while
  respecting the exact scope of every negative result.

Work autonomously with independent review/counterexample lanes when useful.
Keep the objective a complete bound below76. For each achievement, preserve
the theorem, exact acyclic schedule, independently constructed source
polynomials, positive-witness maps and focused checks. Commit stable milestones,
update the nearest project documentation, and follow ProveIt's integration
workflow. Publish through the ProveIt remote, with no force pushes or unrelated
staging. This WIP snapshot itself is not a request to merge unfinished claims
into main or to change the maintained universal bound.
