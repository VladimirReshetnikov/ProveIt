# Primary-source and scope audit: fixed-center projective returns

4 October 2026. This audit read the preceding fixed-word-invertibility proof and the primary sources linked below. It did not execute an upstream program, simulator, or saved collision schedule. The algebra in §§2–5 is a direct derivation, not a claim attributed to the cited authors. The five-live-signal compiler itself must be justified by this packet's construction and chronology proof. No novelty, priority, or exhaustive-search claim is made.

## 1. Verified primary precedents

1. **Fractional-linear return maps with itinerary restrictions.** Thomas Mestl, Chris Lemay and Leon Glass, *Chaos in high-dimensional neural and gene networks*, **Physica D 98** (1996), 33–52. [Author/institution-hosted article](https://www.mcgill.ca/physiological-dynamics/sites/physiological-dynamics/files/chaosinhigh_1996.pdf). Section 2, printed p.35 (PDF p.3), equations (2.3)–(2.4), derives an exit-wall map `x -> Cx/(1+c^T x)` and specifies its exit-dependent domain. Section 4.1, printed p.40 (PDF p.8), equation (4.2), gives the corresponding cycle map. This is the same algebraic fixed-origin fractional-linear form as `Aw/(s+bw)` after dividing numerator and denominator by `s`. It is a close precedent in Glass networks; it does not establish the present five-signal realization theorem. Its fixed-point and timing conclusions depend on its own flow and admissibility assumptions.

2. **Constant-flow section maps and exact itinerary domains.** Hassan Najafi Alishah, Pedro Duarte and Telmo Peixe, *Asymptotic Poincaré Maps along the edges of Polytopes*, **Nonlinearity 33(1)** (2020). [Primary manuscript, arXiv:1411.6227v3](https://arxiv.org/pdf/1411.6227). Section 5, manuscript pp.21–24: equation (5.2) is an oblique constant-flow projection; Proposition 5.4 identifies its trajectory domain; the paragraph after equation (5.3) identifies the inverse using reversed flow; Definition 5.7 and equation (5.5) compose maps along an itinerary with pulled-back domain conditions. This supports the geometric positioning of fixed-word homogeneous maps and their strict cone guards, but is not a signal-machine compiler.

3. **Signal arithmetic and scale encodings.** Jérôme Durand-Lose, *Abstract geometrical computation and the linear Blum, Shub and Smale model*, **CiE 2007, LNCS 4497**, 238–247. [Author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2007_CiE.pdf). Sections 3.1–3.2, manuscript pp.4–8, encode register values as distances relative to a scale pair and implement addition and multiplication by constants; Figure 6 gives multiplication speeds. Section 5, manuscript p.10, records the rational-speed/rational-position version of the simulation. These are genuine arithmetic-construction precedents. Their additional registers/signals and population-changing operations do not supply a five-live-signal, number-preserving, full-section return theorem.

4. **Signal-machine definitions.** Florent Becker et al., *Abstract Geometrical Computation 10: An Intrinsically Universal Family of Signal Machines*. [Primary manuscript, arXiv:1804.09018v2](https://arxiv.org/pdf/1804.09018). Section 2, manuscript pp.4–5, Definitions 1–2, gives finite meta-signals, constant label-dependent speeds, deterministic collision rules, distinct speeds within each incoming/outgoing set, and positive-next-meeting-time dynamics. It distinguishes label types from their occurrences; five live signals is not five meta-signals.

5. **Which affine transformations of machines are actually established.** Florent Becker, Mathieu Chapelle, Jérôme Durand-Lose, Vincent Levorato and Maxime Senot, *Abstract Geometrical Computation 8: Small Machines, Accumulations & Rationality*. [Primary manuscript, arXiv:1307.6468v1](https://arxiv.org/pdf/1307.6468). Section 2.3, manuscript pp.11–12, Lemmas 1–2, concerns affine changes of all speed values and common positive affine changes of the spatial coordinate. These are transformations of space-time diagrams. They do **not** justify applying an arbitrary affine transformation to the two-dimensional shape coordinates of a marker section while claiming the resulting machine physically realizes that shape conjugacy.

6. **A recent explicit account of positive denominators and exact cones.** Ismail Belgacem, Roderick Edwards and Etienne Farcot, *Computer-aided analysis of high-dimensional Glass networks: periodicity, chaos, and bifurcations in a ring circuit*. [Primary manuscript, arXiv:2411.10451v1](https://arxiv.org/pdf/2411.10451). Section III, manuscript pp.6–9: equations (6)–(10) derive fractional-linear wall maps and their compositions; equations (11)–(12) give strict linear inequalities defining the itinerary cone. The derivation explicitly uses positive denominators to pull inequalities back. This is a useful domain-audit precedent, not evidence for the present compiler. No accompanying code was run.

## 2. Exact fixed-center scope

Use centered coordinates `q=(D,ξ,η)`, with `x=D/3+ξ` and `y=2D/3+η`. The physical ordered-section cone is

    C = {D>0, D/3+ξ>0, D/3+η−ξ>0, D/3−η>0}.

For

    N = [[s,b],[0,A]],    s∈Q, s>0, b∈Q^(1×2), A∈GL₂(Q),

the ray through `e₀=(1,0,0)` is fixed with positive multiplier `s`. On `D>0`, write `w=(ξ,η)/D` and

    h(w)=s+bw,       f(w)=Aw/h(w).

Then `f(0)=0`, `Df(0)=A/s`, and `det N=s det A`. The projective map forgets a common nonzero scalar on `N`; the prescribed full homogeneous return does not. In particular, replacing a negative lift by its negative may fix a projective sign issue but changes the requested homogeneous map.

The proposed realization theorem covers this fixed-center subgroup, with the stated positive lift and on the construction's verified open chamber. It does not by itself classify arbitrary rational invertible three-coordinate returns.

## 3. Positive ordered-section compatibility

Every one-pass physical domain `U` must obey

    U ⊂ C ∩ N⁻¹C,

in addition to the complete collision-word conditions. In normalized coordinates, put `z=Aw`. Endpoint compatibility is precisely the initial triangle inequalities together with

    h(w)>0,
    z₁+h(w)/3>0,
    z₂−z₁+h(w)/3>0,
    h(w)/3−z₂>0.

All are strict rational affine inequalities. They are strict at `w=0` because `s>0`, so endpoint compatibility holds on some neighborhood of the center. It is unnecessary, and generally false, to require that `N` preserve the entire ordered cone. Conversely, endpoint compatibility does not prove a collision word: every flight must be positive and every nonprescribed contact excluded, including simultaneous remote contacts.

A useful general map-level necessary condition is `C∩M⁻¹C≠∅`. It is also sufficient for the existence of an open neighborhood of admissible input/output pairs, but not sufficient for a signal-machine construction. If a rational positive eigenray `r` lies in `C` and `Mr=λr` with `λ>0`, this map-level condition is automatically strict near `r`.

For repeated execution, every iterate must stay in the actual word chamber. A one-pass chamber is not an invariant set. Additional chart guards or an intentionally shrunken neighborhood yield a subchamber; they must not be silently relabeled as the original word's exact chamber. Likewise, variable scale `D'=Dh(w)` prevents importing a universal clock criterion based on `s` alone.

## 4. When rational affine conjugation is enough, and when it is not

Write an arbitrary rational matrix in blocks

    M = [[a,c],[d,B]].

A finite rational fixed point `p∈Q²` satisfies

    d+Bp = λp,       λ=a+cp ≠0.

For the rational affine chart change

    T = [[1,0],[p,I]],

direct multiplication gives

    T⁻¹MT = [[λ,c],[0,B−pc]].

Thus a finite rational eigenray is algebraically sufficient for this fixed-center form, and `det(B−pc)=det(M)/λ≠0`. To use the positive-lift compiler for the specified homogeneous matrix, require `λ>0`. A nonzero rational eigenvector necessarily has a rational eigenvalue: choose any nonzero coordinate and take the corresponding quotient in `Mr=λr`.

Important qualifications:

- An affine chart change preserving the `D` coordinate only handles eigenrays with `D≠0`; a ray at infinity cannot be moved to a finite center by such a change
- Any rational eigenray can be made the first column of a rational invertible basis change, but that is a general projective re-encoding; its normalization functional, sign, and domain must be specified and checked
- If the finite fixed point is meant to represent ordered physical markers in the same section, require `(1,p)∈C`; an exterior or boundary fixed point does not give an interior center chamber
- Realizing `T⁻¹MT` and declaring the represented state to be `Tq` realizes `M` in that changed encoding. It does **not**, by coordinate algebra alone, produce a machine whose original marker coordinates undergo the literal map `M`. That stronger claim needs an explicit physical implementation of the conjugating maps, or a separately verified adaptation of the construction
- Restricting around an interior positive eigenray provides compatible chart neighborhoods; it cannot prove the implementation of a missing physical coordinate conversion

Accordingly, “all rational projective maps with a compatible finite rational fixed point, in an explicitly stated rational affine encoding” is an algebraic consequence of a verified fixed-center compiler. “All `GL₃(Q)` maps in the original marker coordinates” is not.

## 5. Positive-cone preservation does not imply a rational fixed ray

Here is a direct exact counterexample to that possible inference. In positive gap coordinates `g=(x,y−x,D−y)`, let

    P = [[1,1,1],[1,2,1],[1,1,3]].

Every matrix entry is positive, so `P` sends every strictly positive gap vector to a strictly positive gap vector. Its characteristic polynomial is

    χ_P(t)=t³−6t²+8t−2.

Its determinant is `2`. By the rational-root theorem, a rational root could only be `±1` or `±2`; substitution rules out all four. The cubic is therefore irreducible over `Q`, and `P` has no rational eigenray.

The rational coordinate relation is

    D=g₁+g₂+g₃,
    ξ=(2g₁−g₂−g₃)/3,
    η=(g₁+g₂−2g₃)/3.

In `(D,ξ,η)` the same matrix is

    M = [[4,−1,−1],
         [−1/3,1/3,1/3],
         [−1/3,−1/3,5/3]].

It preserves `C` globally but cannot be rationally conjugated into a block form fixing a rational ray. This is a limitation of the fixed-center compiler and rational-conjugacy argument, not an impossibility theorem for other signal-machine constructions realizing `M`.

## Recommended positioning

The primary literature already contains signal-based arithmetic, homogeneous constant-flow section maps, and fixed-itinerary fractional-linear return maps with explicit domain restrictions. The construction-specific claim in this packet is the exact five-live-signal, rational-speed, number-preserving realization with literal phase closure and a proved full-dimensional chamber. Its generalization beyond a compatible rational fixed center requires an additional construction or argument; neither familiar projective algebra nor a positive output denominator supplies one.
