# Priority audit: common-nilpotent components, intervals, and decision truncation

Research notes for the ProveIt continuation, checked 7 October 2026. This is an internal source ledger and mathematical audit, not a claim of priority. The scanner under discussion forgets the quantum grading and retains the homological grading. The precise algebraic statements below are consequently ungraded in the coefficient algebra.

## 1. The interval theorem is classical

**Primary reference.** Gunnar Carlsson and Vin de Silva, *Zigzag Persistence*, Foundations of Computational Mathematics **10** (2010), 367–405, DOI 10.1007/s10208-010-9066-0; [arXiv:0812.0197](https://arxiv.org/abs/0812.0197), [PDF](https://arxiv.org/pdf/0812.0197).

Theorem 2.5 explicitly attributes the interval classification to Gabriel. It says that finite-dimensional representations of an arbitrarily oriented finite path are direct sums of interval representations. Proposition 2.2 supplies Krull–Schmidt uniqueness; §4 gives a constructive proof and a matrix-input algorithm. In the equioriented case needed here, the classification also follows from the structure theorem for finitely generated graded modules over a one-variable polynomial ring. The original reference listed there is Peter Gabriel, *Unzerlegbare Darstellungen I*, Manuscripta Mathematica **6** (1972), 71–103. A correct attribution is “an application of the classical type-A interval decomposition,” not “a new barcode theorem.”

### Application to a common-nilpotent block

Let an additive category over a field k contain an object M and an endomorphism theta with theta^2=0. Suppose a finite complex supported on copies of M has differential d_h=theta A_h, with A_h a scalar matrix. The condition d_{h+1}d_h=0 follows from theta^2=0; it does **not** impose A_{h+1}A_h=0. Thus the A_h form an ordinary equioriented quiver representation rather than an ordinary scalar chain complex.

A degreewise scalar change of basis P_h acts by A_h -> P_{h+1} A_h P_h^{-1}. Scalar matrices commute with theta, so each such transformation lifts to a chain isomorphism of the original complex. Applying the interval theorem gives finite strings

    M --theta--> M --theta--> ... --theta--> M

and isolated copies of M. This also follows by extension of scalars along k[epsilon]/epsilon^2 -> End(M), epsilon -> theta. The barcode is canonical for the scalar representation with its chosen theta and fixed degree indexing; the basis that exhibits it need not be canonical. A statement about classification under all End(M)-linear changes of basis needs an additional argument and is unnecessary for the scanner optimization.

This reduction is a self-contained elementary consequence of a classical theorem. Its potentially useful contribution here is the explicitly detectable checkpoint condition, its certified implementation inside the existing scanner, and the resulting representation-size bound.

## 2. The matching corner algebra and the future-gluing interface

**Primary reference.** Mikhail Khovanov, *A functor-valued invariant of tangles*, Algebraic & Geometric Topology **2** (2002), 665–741; [arXiv:math/0103190](https://arxiv.org/abs/math/0103190), [PDF](https://arxiv.org/pdf/math/0103190).

Sections 2.4–2.5, PDF pp. 15–17, identify the matching corner a(H^m)a, and the endomorphism algebra of the corresponding projective, with the m-fold tensor power of the rank-two Frobenius algebra A. After base change to F2 and forgetting the conventional grading shift, this is

    R_m = F2[x_1,...,x_m]/(x_1^2,...,x_m^2).

The generator x_i is a dot on the i-th matching arc. The tensor factors arise by closing a matching against its reflection. This is a primary arc-algebra reference; the dotted-cobordism interpretation can also be proved directly by neck cutting and evaluation of the dotted-disc basis.

In R_m every augmentation-ideal element theta squares to zero: write theta as a sum of nonconstant squarefree monomials. In characteristic two all cross terms disappear from theta^2, and the square of each monomial contains some x_i^2. Nonzero theta is needed for a uniquely recovered scalar matrix A_h over F2; theta=0 is handled as a zero-differential component.

**Primary gluing reference.** Dror Bar-Natan, *Khovanov's homology for tangles and cobordisms*, Geometry & Topology **9** (2005), 1443–1499; [arXiv:math/0410495](https://arxiv.org/abs/math/0410495), [PDF](https://arxiv.org/pdf/math/0410495).

Theorem 2 (§5, PDF p. 24) extends planar gluing to complexes by the total tensor differential and states that gluing preserves homotopy equivalence. Section 11.2 applies the same construction to the dotted quotient and recovers ordinary Khovanov homology via the Frobenius functor. These statements give the required interface for a fixed future suffix and closure: E=F(M) is a bounded finite-dimensional complex; epsilon acts by the chain map F(theta), which squares to zero. Consequently the image of an l-term theta-string is the ordinary total tensor product I_l tensor_A E, where A=k[epsilon]/epsilon^2 and I_l is the l-term free epsilon-string. Because I_l is bounded free, this also computes the derived tensor product, without any flatness assumption on E.

For a quantum-graded extension, scalar basis changes must respect the internal shifts and theta must have a compatible homogeneous degree. That extra claim is not needed for an ungraded total-rank recognizer.

## 3. Stronger classical classification: bounded derived complexes over dual numbers

**Primary reference.** Bernhard Keller, Dong Yang, and Guodong Zhou, *The Hall algebra of a spherical object*, Journal of the London Mathematical Society **80** (2009), 771–784, DOI 10.1112/jlms/jdp054; [arXiv:0810.5546](https://arxiv.org/abs/0810.5546), [PDF](https://arxiv.org/pdf/0810.5546).

Example 3.7(b), PDF p. 7, takes B=R/(pi^2) for a discrete valuation ring R. All indecomposables of D^b(mod B) are finite rank-one pi-strings X[a,b] and left-infinite rank-one pi-strings X]-infinity,b]. Taking R=k[[epsilon]], the latter represent shifts of the simple A-module k. The paper credits earlier work of Künzer; its published version also credits Burban's thesis. This is an established classification, not a new claim of the present project.

**Convenient corroborating reference.** Francesco Amodeo and Riccardo Moschetti, *Fourier–Mukai functors and perfect complexes on dual numbers*, Journal of Algebra (2015), DOI 10.1016/j.jalgebra.2015.04.020; [arXiv:1309.7215](https://arxiv.org/abs/1309.7215), [PDF](https://arxiv.org/pdf/1309.7215).

Section 2, immediately after Definition 2.5, states precisely that shifts of finite free epsilon-strings are the indecomposables of Perf(A), and shifts of the left-infinite resolution are the indecomposables of D^b(A) outside Perf(A). Theorem 2.2 and Proposition 2.3 justify finite Krull–Schmidt decompositions. The classification is attributed to Keller–Yang–Zhou, Example 3.7, and Künzer, §3.

### Derived consequence proposed for the scanner

Write a bounded finite-dimensional A-complex in the derived category as

    E ≃ (direct sum_j I_{m_j}[s_j]) ⊕ (direct sum_{t=1}^a k[u_t]).

Since I_l is bounded free, tensoring preserves this derived decomposition. Direct calculation gives

    dim_k H^*(I_l tensor_A I_m) = 2 min(l,m),
    dim_k H^*(I_l tensor_A k) = l.

Therefore

    dim_k H^*(I_l tensor_A E) = sum_j 2 min(l,m_j) + a l.

For any integer threshold c>=1, replacing l by min(l,c) preserves this quantity after saturation at c. Each term with m_j<c is unchanged once l>=c; each term with m_j>=c already contributes at least c; and any simple summand contributes at least c. In particular c=3 gives a replacement relevant to the distinction between total Khovanov ranks 2 and >=3.

This is a **decision-equivalent replacement for the stated family of continuation functors**. Strings of different lengths are not generally homotopy equivalent; they are distinct indecomposables. The replacement should not be described as preserving the full Khovanov complex, homological degrees, quantum degrees, or exact total rank. Its proof requires both the classical derived classification and the genuine A-linear gluing interface above. The theory agent is supplying a self-contained proof of the tensor-rank formula and integrating this into the main argument.

The argument is not merely a late-stage homology shortcut: because it holds for every bounded A-complex E, it applies before the actual suffix is expanded. Future exact changes of basis, cancellation, and planar gluing preserve the eventual total rank. Sums of independently replaced direct summands remain valid because saturation at c commutes with addition of nonnegative integers. This supplies a robust proof boundary for the proposed local operation.

### Geometric refinement: length two suffices at total-rank threshold three

**Primary parity reference.** Alexander N. Shumakovitch, *Torsion of Khovanov homology*, Fundamenta Mathematicae **225** (2014), 343–364, DOI 10.4064/fm225-1-16; [arXiv:math/0405474](https://arxiv.org/abs/math/0405474), [PDF](https://arxiv.org/pdf/math/0405474). Corollary 3.2.C, PDF p. 12, gives the reduced/unreduced F2 splitting for every nonempty link L. Its proof in Theorem 3.2.A uses a link basepoint and the identity nu X+X nu=id; it does not assume that L is a knot. In particular the total unreduced rank is even.

For E obtained by applying the actual unprocessed tangle suffix and closure to a crossingless matching M, E is the ordinary Khovanov complex of a nonempty link. Nonzero theta excludes the empty matching corner R_0=F2. The derived decomposition formula at l=1 gives dim H(E)=2(number of finite strings)+a, so a is even. For l>=2, any nonzero simple contribution is therefore at least 4; any finite string with m_j>=2 contributes at least 4; and finite strings with m_j=1 contribute the constant 2. Thus replacing every l>=2 by 2 preserves the rank after saturation at 3. This is a geometric refinement of the universal cap-three theorem, not a statement for arbitrary A-complexes. For example E=k distinguishes l=2 and l=3 at threshold three, which shows exactly why the parity hypothesis matters.

An even simpler proof of the needed parity avoids the reduced/unreduced theorem: use the **raw** suffix cube before cancellation. Every completed resolution of a nonempty matching contains at least one circle and contributes a vector space of dimension 2^c, which is even. For a finite complex over F2, the total homology dimension is the total chain dimension minus twice the sum of differential ranks. Thus dim H(E) is even directly. This argument also avoids unnecessary assumptions about orientations or realizability of a particular intermediate matching as a prefix tangle. Shumakovitch remains useful background, but is not required by the cap-two proof.

The length bound two is sharp for this family of closure observations. Take M with two arcs, theta=x_1+x_2, and the other crossingless closure pairing, so that both arcs belong to one circle. Both dot actions become the same x on the closed circle, so F(theta)=0 in characteristic two. The circle space has dimension two, and the closure of I_l(theta) therefore has total rank 2l. Replacing a length of at least two by one would turn a rank of at least four into two. This example concerns an admissible formal block and actual closure; no realization claim about the block as a complete tangle invariant is needed.

### Adversarial proof-interface audit

No mathematical gap was found in the stated ungraded construction. A multiobject suffix does not obstruct the argument: totalize all suffix degrees in E=F(M), and functorial interchange makes F(theta) commute strictly with its differential. The desired bicomplex has one copy of E per string position and horizontal map F(theta), so it is exactly I_l tensor_A E. Use a raw suffix functor for this proof, rather than a rank-only summary or an action transported only up to homotopy. Subsequent exact simplification of the actual computation is harmless. If the implementation normalizes homological shifts of separate summands, distinguish that total-rank-preserving step from the degreewise chain isomorphism proving the barcode decomposition.

## 4. Existing Khovanov compression and normal forms

**Bar-Natan 2007.** *Fast Khovanov Homology Computations*, Journal of Knot Theory and Its Ramifications **16** (2007), 243–255; [arXiv:math/0606318](https://arxiv.org/abs/math/0606318). Local cancellation and delooping, before expansion into a global complex, are the foundation of the scanner. The article explicitly says that its basic reduction does not a priori guarantee a smaller resulting complex. The proposed work extends this framework; it does not originate local Khovanov simplification.

**Naot 2006.** Gad Naot, *The universal Khovanov link homology theory*, Algebraic & Geometric Topology **6** (2006), 1863–1892, DOI 10.2140/agt.2006.6.1863; [arXiv:math/0603347](https://arxiv.org/abs/math/0603347). The published title differs from the original preprint title. The article reduces the universal geometric complex for a marked link to one object with matrices over a one-variable polynomial ring, and discusses its role in efficient crossing-by-crossing computations. This is relevant prior work on simpler coefficient-algebra models, although its polynomial parameter and universal theory differ from the present square-zero decision quotient.

**Cohen 2024.** Jesse Cohen, *An exceptional splitting of Khovanov's arc algebras in characteristic 2*, Fundamenta Mathematicae **264** (2024), 69–84, DOI 10.4064/fm230712-2-12; [arXiv:2209.01705](https://arxiv.org/abs/2209.01705), [PDF](https://arxiv.org/pdf/2209.01705). Theorem 3.2 proves H_n ≅ Htilde_n tensor R[x]/x^2 in characteristic two. Proposition 3.3 gives related maps for crossingless tangle modules, but only one chosen module action is intertwined in general: the paper explicitly says these are not necessarily bimodule isomorphisms and supplies a counterexample. This is relevant to a future reduced-arc implementation, but it does not by itself solve compatibility under arbitrary gluing.

**Thompson 2018.** Benjamin Thompson, *Khovanov complexes of rational tangles*; [arXiv:1701.07525](https://arxiv.org/abs/1701.07525), [PDF](https://arxiv.org/pdf/1701.07525). Theorem 4.4 gives minimal zigzag complexes; Theorem 5.1 packages the bigraded object counts in 2-by-2 matrices, with a Burau connection in Corollary 5.3. Thus sparse string-like tangle normal forms and matrix encodings predate this project. Their existence does not imply polynomial size of the explicitly expanded minimal complex. As an elementary consequence of the displayed matrices, specializing q=t=1 gives the two unitriangular integer matrices; alternating their products produces Fibonacci growth.

**Kotelskiy–Watson–Zibrowius.** *Immersed curves in Khovanov homology*, [arXiv:1910.14584](https://arxiv.org/abs/1910.14584), encodes four-ended tangle complexes by immersed multicurves with local systems and supplies a gluing interpretation. The recent *On mutation invariance in Khovanov homology*, [arXiv:2602.23442](https://arxiv.org/abs/2602.23442), restates the classification in Theorem 2.30: over a field, bigraded complexes over its four-ended algebra B, up to homotopy, correspond to multicurves. Section 2.6 identifies this as a special case of earlier Haiden–Katzarkov–Kontsevich work and their own 2019 theorem. It also describes direct-summing local systems on repeated compact curves. These results establish a much broader prior normal-form theory; they do not provide a general polynomial bit-complexity bound for constructing or manipulating the relevant curves. Quantum-forgetting may also enlarge the category, so a direct transfer requires care.

**Kelomäki–Schütz 2026.** *On computational complexity of Khovanov homology*, [arXiv:2601.02119](https://arxiv.org/abs/2601.02119). Theorem 1.2 proves exponential behavior of the standard explicit scanning/divide-and-conquer approach even for certain 3-braids. Theorem 1.3 gives a separate polynomial algorithm for integral Khovanov homology of 3-braids, and Theorem 1.4 computes fixed extremal-degree ranges polynomially at fixed strand number. Their latter truncation is a homological-window argument, distinct from the universal continuation rank-threshold replacement proposed here. This is a preprint as of the audit date.

No claim that “barcode compression of Khovanov homology is new” is supportable from this audit. A narrow, reviewable contribution can be stated as the common-nilpotent detector, its explicit decision-threshold quotient under all suffixes, its integration with the repository's continuation-sharing architecture, and the precise checkpoint-parameter theorem. Even this narrow claim should be phrased as “the construction developed here,” not an assertion of first priority.

## 5. Exact scope of the openai/math family-116 inspiration

Repository sources inspected directly through the GitHub connector:

- [OpenAI, One Rational Matrix Hitting Point for Noncommutative Formulas, September 24, 2026](https://github.com/openai/math/tree/main/preprints/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026).
- [The introduction and theorem statements](https://github.com/openai/math/blob/main/preprints/One-Rational-Matrix-Hitting-Point-for-Noncommutative-Formulas-September-24-2026/build/introduction.tex).
- [The declared Lean formalization scope for family 116](https://github.com/openai/math/blob/main/lean/docs/116.md).

The paper constructs a rational matrix tuple detecting every nonzero division-free noncommutative formula of size at most s in n variables over characteristic-zero fields. It states dimension at most 2ns^2 and polynomial bit construction. Its compression uses an acyclic path representation with at most 2s states, an iterated-integral differential system, and a multiplicity bound proving that a finite Taylor truncation retains nonzeroness. The scope document explicitly says that the selected division-free formal theorem asserts the hitting property but does not separately assert the O(ns^2) dimension or polynomial bit-construction claims. The companion rational-formula theorem has a different, stronger formalized output/complexity scope.

The useful methodological analogy is **small exact representation plus a proved finite observation bound**. Here the dual-number decomposition and tensor-rank formula play the role of proving which finite observation preserves the decision. There is no direct theorem transfer: a Bar-Natan complex is over a cobordism quotient rather than a free noncommutative algebra; arbitrary shared circuits are not the same as formulas; and an identity test is not a rank oracle or a Khovanov homology algorithm. The present scanner remains a finite-field construction, whereas the cited division-free hitting point is a characteristic-zero result.

## 6. Focused research questions arising from this audit

1. Can direct summands with a common theta be found through a larger class of exact basis changes, beyond recognizing equal entries in the current basis, without creating exponential intermediate matrices?
2. What is the exact decision equivalence on four-ended curve components and local systems when the only requested observation is total rank below a fixed threshold? Can slope and local-system data be kept in binary throughout gluing?
3. Can the dual-number threshold lemma be extended to several independent nilpotent actions, or does the representation theory of the resulting algebra force genuinely unbounded decision-state information?
4. Which geometric diagram classes guarantee frequent common-nilpotent checkpoints? A detection routine alone does not bound how long or how large the ineligible components become.
5. Can a rigorous dichotomy force either a small continuation state or an inexpensive certificate of nontriviality? The width obstruction and explicit-chain blowup show why a simple boundary-type count is insufficient.
6. Can normal-surface hierarchy certificates interact with the scanner so that one method certifies the hard cases of the other, while preserving a proved total running-time bound?
7. Can Cohen's exceptional arc-algebra splitting be made computationally compatible with the actual planar decomposition by explicitly tracking marked components and the second module action? The failure of naïve bimodule compatibility is a concrete obstacle rather than a generic implementation detail.

The global quasi-polynomial conclusion still requires an input-independent bound on the number and bit size of surviving ineligible components, on the cost of their transformations, and on the chosen diagram/decomposition search. None of the cited classifications supplies that global bound by itself.
