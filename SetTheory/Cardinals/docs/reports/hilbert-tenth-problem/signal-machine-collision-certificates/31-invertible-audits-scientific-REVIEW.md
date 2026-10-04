# Independent audit: fixed-word invertibility and the seven-event reversal

Date: 4 October 2026 (UTC).

## Verdict and source binding

**The mathematical claims A–C and Corollary D are supported under their stated hypotheses. No required mathematical correction was found.** The determinant-negative realization is on exactly the stationary-marker, initial messenger-speed +1 section used by the frozen positive compiler. Its fourth event really is marker-only. The extra guard y<4x is both sufficient and necessary for the specified complete word, not merely a convenient safe region.

The reviewed frozen root is `/workspace/shared/fixed-word-invertibility61-20261004`.

* `PROOF.md`: SHA-256 `dc97e30c56817370138d6be760d44a5df031743a0ee1011cca39381b67bb0cec`
* `MANIFEST.json`: SHA-256 `715bbbc817188a1a4d90ea7ad673fe4c69a9df105e202828c1835ae308e6f7eb`
* Frozen positive-compiler proof: SHA-256 `e0ddd64cdbbb5c7f448266ab58f1dfeb2868892ac0f230632b2337e4d0bed065`

All files in that root were read as inert data, including the author checker and its stored evidence. No author checker, upstream program, machine simulator, stored collision schedule, or constructor was executed. The positive-compiler dependency was reviewed from its frozen mathematical proof only. Its companion spectral-classification theorem is not needed for the present GL2 realizability criterion and was not re-audited here.

`frozen_before.json` records hashes, byte sizes, permission modes and nanosecond modification times. The later `frozen_after.json` and `preservation.json` record the read-only preservation comparison. All new artifacts are in this separate audit directory.

## 1. Full-section invertibility

This checks PROOF.md §§1–2 independently of the construction.

Let H_a=ker h_a and H_b=ker h_b be the source and target collision hyperplanes in R^n. Let v be the fixed velocity vector for the intervening flight. Distinct outgoing speeds imply h_a v≠0, and distinct incoming speeds imply h_b v≠0. Each line parallel to v intersects each hyperplane at one point. Consequently the correspondence between the two intersections is already geometrically a linear isomorphism.

Algebraically, set P_b=I−v h_b/(h_b v). The flight is P_b restricted to H_a. Its inverse is P_a restricted to H_b. For q∈H_a, write r=q−v h_bq/(h_bv). Then h_ar=−(h_av)h_bq/(h_bv), so P_ar=q. The opposite composition is identical with a,b exchanged. This proves both inverse identities on the full hyperplanes, not only on realized trajectories.

The following scope points are essential and are correctly handled in the packet:

1. At a binary collision, both input slots and both output slots share the same positional coordinate. Either fixed input/output matching therefore induces an invertible positional identification. Labels need not carry persistent particle identities.
2. Sorted slot identities are well-defined between events. A binary contact occupies adjacent slots, with output slots ordered by increasing output speed. Swapping the two coincident coordinates is the identity on the collision hyperplane, so it introduces no unaccounted determinant sign.
3. Repeated instances of one label at distinct positions are separated by the sorted chart. Equal-label instances have equal speed and cannot themselves be one of the distinct-speed colliding input/output pairs. A word that fails to distinguish occurrences must be refined into its ordered charts; the packet makes this limitation explicit.
4. Positive flights and absence of remote simultaneous collisions ensure that each section is exactly one collision hyperplane, not an intersection of additional collision constraints. A multiple-contact boundary is excluded rather than silently treated as full-dimensional.
5. Full-dimensional openness is needed to identify any proposed formula with the unique ambient linear isomorphism. Equality on an invariant line or other proper slice would not justify the singular obstruction.
6. The common-translation vector e=(1,…,1) lies in both collision hyperplanes and satisfies P_be=e. Every collision identification fixes e too. An invertible map preserving this line induces an invertible quotient map. Subtracting a final anchor coordinate is a quotient chart, even if that anchor moved.

Rational speeds and integer collision rows give rational matrix entries; absence of fixed external locations/times gives homogeneity. On the actual chamber the image is open in the target section, but need not be the whole target chamber. Neither label-rule injectivity nor global reversibility follows or is needed.

For n=5 the full collision hyperplane has dimension 4, the translation quotient dimension 3, and positive scale normalization leaves dimension 2. These counts agree with the supplied (D,x,y) and centered (D,X_c,Y_c) charts. Removing the untouched R from the reversal reduces the translation quotient to dimension 2 and normalized shape dimension to 1. It does not by itself construct a four-live-signal normalized planar compiler.

## 2. Determinant and parity: an independent exterior-form derivation

This checks PROOF.md §3. Put d=n−1 and let g=(g_1,…,g_d) be sorted gaps. A flight maps E_a={g_a=0} to E_b={g_b=0} by P(g)=g−w g_b/w_b. Here w_a>0 and w_b<0 on an actual positive flight.

Let Ω=dg_1∧…∧dg_d and let α=ι_wΩ. For u_1,…,u_(d−1) tangent to E_a, replacing any u_i by P u_i changes it only by a multiple of w, which does not change Ω(w,u_1,…,u_(d−1)). Thus P*α=α on E_a. On the omitted-coordinate chart of E_a,

    α|E_a = (−1)^(a−1) w_a dg_1∧…∧omit(dg_a)∧…∧dg_d.

Comparing with E_b gives

    (−1)^(b−1) w_b det(P:E_a→E_b) = (−1)^(a−1) w_a,
    det(P:E_a→E_b) = (−1)^(a+b) w_a/w_b.

This independently establishes the packet's complementary-minor formula. Its cofactor proof is also correct: adj(I−w e_b^T/w_b)=w e_b^T/w_b, and the minor deleting row b and column a is the relevant chart determinant. The algebraic a=b case gives identity; it cannot describe a nontrivial positive flight with simultaneous w_a>0 and w_a<0.

For consecutive faces a_0,…,a_m, the coordinate signs telescope and each denominator is negative. Hence sign det=(−1)^(m+a_0+a_m). A literal return has a_m=a_0, yielding (−1)^m. Its source opening speeds consist of the initial opening speed and the outputs of events 1,…,m−1. Literal phase closure identifies the initial opening with the final output opening, so the absolute determinant is exactly the cyclic product of all event output/input speed ratios.

This argument explicitly avoids an ambient label-permutation sign. Different initial/end identifications require their own induced face-chart factors. For a literal same-chart return the conversion between gaps and (D,x,y), and then centering, is conjugation and preserves determinant. There is no general orientation-preservation obstruction.

## 3. Seven-event reversal derived from global ballistic lines

This checks PROOF.md §§5.1–5.2 and RULES.json. L=0, Y=y and R=D are stationary throughout. Write q(t) for messenger position and z(t) for the moving X marker. The initial velocities are q'=1 and z'=0.

The following line equations follow directly from the stated velocities and continuity at a contact; they are useful independently of the supplied event table:

| Open flight | q(t) | z(t) |
|---|---|---|
| 0→1 | t | x |
| 1→2 | 5x/2−3t/2 | 3x/2−t/2 |
| 2→3 | t−5x/3 | 3x/2−t/2 |
| 3→4 | 35x/36−t/4 | 2t−34x/9 |
| 4→5 | 35x/36−t/4 | 5y/4+17x/18−t/2 |
| 5→6 | t−35x/9 | 5y/4+17x/18−t/2 |
| 6→7 | 23x/9+5y/3−t | −2x/3+5y/6 |

In particular q(t) is the very same line before and after event 4. Its speed and Q_middle label do not change there.

Solving q=z at events 1,3,6; q=0 at events 2,5,7; and z=y at event 4 gives, respectively,

    t1=x, t2=5x/3, t3=19x/9,
    t4=17x/9+y/2, t5=35x/9,
    t6=29x/9+5y/6, t7=23x/9+5y/3.

The contact positions follow by substitution. The event-4 messenger is (4x−y)/8; the event-5 marker is ξ=5y/4−x; and the final marker is F=5y/6−2x/3. Therefore t6=t5+F and t7=t5+2F. All entries in the packet's table agree.

Successive differences give precisely

    x, 2x/3, 4x/9, (9y−4x)/18, (4x−y)/2, F, F.

These identities include all seven actual flights, with no implicit initial zero-time collision or marker phase switch.

### 3.1 Whole-chamber positivity by interval endpoints

An independent alternative to the author's three-ray cone certificate is to divide by y>0, put k=x/y, and retain d=D/y−1>0. The proposed exact chamber is simply

    1/4<k<1, d>0, y>0.

Let f=5/6−2k/3. The four gaps at the eight successive sections, divided by y, are

| Section | Gaps in spatial order L,q,z,Y,R |
|---|---|
| 0 | (0,k,1−k,d) |
| 1 | (k,0,1−k,d) |
| 2 | (0,2k/3,1−2k/3,d) |
| 3 | (4k/9,0,1−4k/9,d) |
| 4 | ((4k−1)/8,(9−4k)/8,0,d) |
| 5 | (0,5/4−k,k−1/4,d) |
| 6 | (f,0,1−f,d) |
| 7 | (0,f,1−f,d) |

Every noncontact entry is an affine function of k that is nonnegative at k=1/4 and k=1 and not zero at both. It is consequently strictly positive at every k in the open interval. The same test certifies all seven positive flight durations divided by y. This proves the entire chamber, without a finite-point inference or numerical trajectory.

On each flight each gap is affine in time, with positive endpoint values except for the one departure zero and one arrival zero. The departure gap has positive outgoing speed difference; the arrival gap has negative incoming difference. Thus no gap vanishes in an open flight, and no nonadjacent contact can occur without an adjacent gap vanishing. This also excludes the apparently plausible X_post/Q_middle collision after event 4: their gap is positive at both endpoints and affine throughout. R remains strictly to the right of Y.

### 3.2 Exactness, including the first failure

Under only 0<x<y<D, events 1–3 have the displayed order. After event 3 the messenger moves left toward L and X_fast moves right toward Y, so they separate. The two possible next contacts are exactly q/L and X_fast/Y. Their prospective absolute times satisfy

    t5−t4 = (4x−y)/2.

For y=4x they are simultaneous at distinct positions. For y>4x the messenger reaches L first. Either case invalidates the claimed globally separated complete word before its fourth event. No formulas after that first obstruction are needed for necessity. Combining this with the sufficiency proof gives exactly 0<x<y<D and y<4x.

On D=1 this is the bounded open rational triangle 0<y<1, y/4<x<y. The standard center (1/3,2/3) is strict. Its centered normalized image has the four guard rows stated in SECTION_AND_GUARDS.json (some inequalities are redundant).

### 3.3 Counts, speeds, closure and return

The standalone label count is four messenger labels, four X-phase labels, and L,Y,R, hence eleven. The seven listed input sets are distinct. The two X labels of speed −1/2 are distinguished by phase and never constitute a same-speed collision pair. All rules have two inputs and two outputs with distinct speeds within each side.

The incoming closing speeds are (1,3/2,3/2,2,1/4,3/2,1); the outgoing separating speeds are (1,1,9/4,1/2,1,1,1). Their ratios are (1,2/3,3/2,1/4,4,2/3,1), with product 2/3. Seven-event parity therefore gives determinant −2/3, independently matching the return matrix.

Event 6 restores X_0 with speed zero and emits Q_cleanup at speed −1. Event 7 restores Q_+ with speed +1 at stationary L. Y and R were unchanged, so every section role, label and outgoing phase is literal. The position map is

    (D,x,y) ↦ (D,−2x/3+5y/6,y).

It fixes (D,D/3,2D/3), so centering produces J=[[-2/3,5/6],[0,1]] without an affine remainder. J^−1=[[-3/2,5/4],[0,1]]. Identity completion on every other finite distinct-speed input set is deterministic and number-preserving. It does not turn omitted contacts into members of this selected complete word, and need not be globally reversible.

## 4. Positive-compiler dependency and GL2 composition

This checks PROOF.md §7 against the frozen dependency, not against executed compiler outputs.

The dependency's mathematical ingredients are consistent: anchor scaling uses h=(u−1)/(u+1) with |h|<1; the reflector homothety gives t'=vt+(1−v)z; and their composition gives t→t+ez with the internal endpoint between the two guarded endpoints. Its small centered shear subdivision retains exact neighbor-interval guards. Reflection about the right anchor gives the same shear-parameter sign for the y block. The three displayed SL2 factorization branches multiply correctly, include zero-pivot and identity cases, and return the messenger to L after an even number of full transfers. Its rational centered-dilation factors telescope to any positive rational determinant without introducing a square root. The final ordered anchor scales supply any rational λ>0. These arguments preserve five live signals and the stationary-marker section with initial messenger +1.

Only this positive-determinant existence theorem is imported for Corollary D. For det A<0, setting B=J^−1A gives det B>0. Running its positive compiler for (B,λ), then J, yields

    diag(1,J) · λ diag(1,B) = λ diag(1,A).

The shape entering J is B times the initial normalized centered shape, since the positive factor λ cancels on normalization. Thus the exact composite chamber is P_B∩B^−1P_J. Each constituent condition is a strict rational affine inequality; both sets contain 0 as an interior point. The intersection is consequently full-dimensional and contains 0, while boundedness follows from its containment in P_B. First-failure exactness follows blockwise, not from continuing a failed hypothetical word.

The label interface is important and the packet correctly warns about it. A fully explicit existence argument is: reserve fresh messenger labels for J, replace the positive block's final output Q_0 by J's entry Q_+, and replace J's final output Q_+ by the whole macro's original Q_0. Keep J's intermediate occurrences of its private Q_+ separate from the positive compiler's labels. Give its moving-X labels fresh names. The only marker-only rule has the fresh X_fast label in its input, hence cannot conflict with a positive-block rule. Q_middle remains unchanged at that rule. No extra signal or zero-time event is necessary. All initial and final section labels of the whole macro then agree.

The positive event count 18K+3T+14H+24ε is even because T is even. Appending seven gives the required odd count. No eleven-label bound is claimed for the composite machine; eleven applies only to the standalone reversal.

The infinite-word identity K(A,P)=⋂_(n≥0)A^−nP follows from the literal phase closure and this exact chamber. The positive block's duration has a positive lower bound 2D. The appended duration satisfies T_J=(23/9)x+(5/3)y<(38/9)D on its entrance section, so contributes less than (38λ/9)D after the scaled positive block. Therefore the claimed positive upper/lower bounds proportional to entrance D persist. The Zeno criterion λ<1 follows by comparison with the geometric series; the rational accumulation-time argument on the rational cyclic subspace remains applicable. No continuation at the accumulation point is supplied.

## 5. Singular obstruction and its exact boundary

The full translation-quotiented five-signal section has all three coordinates (D,X_c,Y_c). Theorem A makes its homogeneous return N invertible. Under the specified fixed-scale law,

    N=λ diag(1,A), det N=λ^3 det A, λ>0.

Hence det A≠0. For normalized affine output w'=Aw+b, the homogeneous matrix is λ[[1,0],[b,A]], with the same determinant, so the affine variant is correct too. A claimed singular formula on a full-dimensional open chamber would equal the true linear return globally and contradict its invertibility.

If the scale row varies with shape, the induced normalized map is projective. On a positive-scale affine chart, its two-dimensional Jacobian determinant is det N divided by the cube of the scale row. It remains locally nonsingular, although it need not be a linear planar map. By contrast, dropping an independent continuous coordinate, restricting to a lower-dimensional set, allowing population change/multicollisions, or declaring a limiting accumulation configuration to be a new event is outside this proof. None of those exclusions is used to assert a stronger impossibility than the packet states.

Combining this obstruction with the positive compiler and reversal proves precisely the promised if-and-only-if criterion for rational A and rational λ>0.

## 6. Primary-literature check and claim boundary

The three §8 sources were checked independently. They are contextual precedents, not dependencies of the packet's direct proof.

* **Becker et al., AGC 10**, Definitions 1–2, PDF pp.4–5: the speed function is attached to meta-signals and distinct speeds are required within collision input/output sets. A finite-support configuration need not be injective as a map from positions, so repeated labels are allowed. Example 5 on p.6 explicitly assigns equal speeds to two different labels. The operational definition uses the smallest positive meeting time. The cited page range is correct. [Primary manuscript](https://arxiv.org/pdf/1804.09018), [version metadata](https://arxiv.org/abs/1804.09018).
* **Durand-Lose, Reversible conservative rational abstract geometrical computation is Turing-universal**, Definitions 1,3–4, PDF pp.3–5: its rational convention includes rational positions (and p.2 restricts the time framework to rationals). Conservativeness uses positive integer energies; equal energies yield number preservation. Reversibility requires injective collision rules with outputs of size at least two, and the subsequent paragraph excludes accumulations from the reversibility assertion. The packet correctly distinguishes this from chartwise positional invertibility and identifies its open real chamber framework as a geometric extension. CiE 2006, LNCS 3988, pp.163–172 is correct. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf), [publisher record](https://link.springer.com/chapter/10.1007/11780342_18).
* **Alishah–Duarte–Peixe, Asymptotic Poincaré Maps along the edges of Polytopes**, §5, PDF pp.21–24: equation (5.2) is the constant-direction oblique section projection; Proposition 5.4 describes its trajectory sector; Definition 5.7 and (5.5) compose fixed-itinerary maps. The proof of Proposition 5.10 invokes local linear isomorphisms. More directly, p.22 just after (5.3) identifies the inverse with the reversed-flow section map. This is substantial geometric precedent for Theorem A, but does not prove the present signal-machine parity or seven-event realization. The Nonlinearity 33(1), 2020 bibliographic information matches. [Primary manuscript](https://arxiv.org/pdf/1411.6227), [publication metadata](https://arxiv.org/abs/1411.6227).

Limited additional searches did not find a matching combined A–C statement, but cannot establish novelty, priority, or completeness of prior-art coverage. The source's explicit refusal to claim any of those should be retained.

Optional editorial improvements only: cite Becker Example 5 for an explicit equal-speed/different-label instance; cite the reverse-flow inverse paragraph on p.22 of Alishah–Duarte–Peixe for the most direct antecedent of the transverse inverse. Neither is a correction to the mathematics or bibliography.

## 7. Independent arithmetic evidence and limitations

`independent_affine_checks.py` was newly written in this audit directory and displayed in full for inspection before execution. It imports only the Python standard library. It never reads source rule JSON, author code, source evidence, a saved collision schedule, or an upstream module. It checks static global affine-line identities, continuity, velocities, contacts, all-chamber endpoint positivity, the first-failure time difference, centering, inverse and speed products. It does not select a next event, advance a machine state, numerically sample trajectories, or execute the machine word.

Its whole-interval certificates are a mathematical finite proof: an affine function nonnegative at both interval endpoints and positive at at least one is strictly positive throughout the open interval. They are not random tests. The generic section-isomorphism, determinant formula, chamber exactness and compiler composition are established above symbolically, independent of these arithmetic receipts.

The resulting receipt is `independent_affine_evidence.json`. A passing run is recorded in `execution_receipt.txt`. The source packet's own 90 determinant fixtures and prior compiler's 75 fixtures were neither executed nor relied upon as proofs of general claims. This audit is conventional mathematical review with exact arithmetic support, not proof-assistant formalization, exhaustive machine search, a minimum-length result, or a universal unchanged-machine construction.
