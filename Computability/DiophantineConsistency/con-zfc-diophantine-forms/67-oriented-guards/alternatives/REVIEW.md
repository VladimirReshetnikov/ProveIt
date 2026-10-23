# Independent architectures: assessment and a concrete next experiment

Status: literature/source review and mathematical architecture analysis, not a new competitive endpoint. No new polynomial is claimed in this directory.

## 1. What is already genuinely independent

Carl and Moroz, *On a Diophantine representation of the predicate of provability* (2007 preprint; Journal of Mathematical Sciences 199(1), 2014), construct an explicit Diophantine proof predicate for first-order logic with one binary relation. They specialize it to a finite Gödel–Bernays axiom package implying a contradiction. This is not a K215 computation and does not require specializing Jones's universal polynomial.

Primary preprint: https://webdoc.sub.gwdg.de/ebook/serien/e/mpi_mathematik/2007/132.pdf

In the preprint, the 15-axiom package omits Choice; Section 7 separately invokes the relative consistency of Choice to justify this omission. Thus it uses equiconsistency rather than identical theorems, exactly the flexibility allowed here. The specialization is the displayed polynomial F_P(m_0(3), x)=0, with m_0 defined by the 15 nested implication codes. This architecture is relevant but not competitive in its published form. Matthew Weidner's 2020 explicitization reports 14,558,112 integer witnesses and a specialized constant with 877,757,576 decimal digits. The primary report is pp. 88–91 of https://www.sigbovik.org/2020/proceedings.pdf. It explains axiom ordering as a way to reduce the pairing-code constant. These counts belong to that reported construction, not to a reconstructed artifact here.

The useful distinction is proof verification versus proof enumeration. A direct existential derivation certificate needs no scheduler, fair enumeration, or deterministic search interpreter. It still needs unbounded certificate checking. Simply naming that predicate does not supply a small Diophantine equation.

## 2. Best new architectural experiment: fixed-input universality

The blank-tape condition that motivates K215 is unnecessary for the Diophantine task. Fix a standard universal machine U and a finite input e describing a ZFC-refutation search. The desired reduction is

    ZFC proves: U(e) halts iff there exists a ZFC proof of contradiction.

Neary and Woods, *Four Small Universal Turing Machines*, give standard machines with state/symbol pairs (5,5), (6,4), (9,3), (15,2); the five-symbol machine uses 22 instructions. Primary source: https://doi.org/10.3233/FI-2009-0036; institutional copy landing page: https://mural.maynoothuniversity.ie/id/eprint/12416/.

The target experiment is to replace the native 943-tile transition language by a smaller fixed universal transition language while representing e as a coefficient-supported initial boundary pattern. This is a compiler change, not just replacing the machine table. The universal machine may also be supplied with a direct checker for finite refutations of an equiconsistent finite theory; it need not simulate K215.

Required interface theorem: for an explicit finite input word e, construct fixed coefficient data C(U,e) such that the native arithmetic language has a witness iff U(e) halts. Preserve the existing witness count and the arithmetic circuit where possible. Measure all coefficient payloads including e.

Three failure modes must be excluded before claiming a gain:

1. A separate tile/state for each input symbol can make the smaller transition table irrelevant.
2. Writing the input as a polynomial sum e_i q^i in a variable q can introduce degree proportional to input length. Fixed binary coefficient data are not the same as variable-base polynomial data.
3. A smaller transition table does not imply fewer polynomial variables or arithmetic operations. It may improve only coefficient height.

An actionable prototype should first implement arbitrary finite input boundaries for one existing small test machine, and prove no spurious initial configurations are admitted. Only then instantiate a published universal machine, materialize its exact input, and compare tile counts, color widths, coefficient bytes, degree, and circuit operations. This avoids spending effort on a full ZFC interpreter before determining whether the boundary compiler is economical.

Weak or semi-weak universality is not interchangeable here. Periodic infinite backgrounds require their own exact boundary theorem; the smallest advertised state count is not by itself usable evidence.

## 3. Proof-oriented fallback independent of Jones

Larchey-Wendling and Forster, *Hilbert's Tenth Problem in Coq*, LMCS 18(1), 2022, give a constructive DPRM development through Minsky machines and FRACTRAN. The paper exposes bounded-universal elimination and transitive-closure encoding as reusable components. Source: https://arxiv.org/abs/2003.04604; code release cited in the paper: https://github.com/uds-psl/coq-library-undecidability/tree/H10-LMCS-v1.1.

One can feed a certified direct refutation verifier through this route. Its advantage is proof infrastructure, not an established small witness count. Extracting and counting the resulting equations is essential; generic DPRM existence alone is not an improvement over the current frontier. A good compiler experiment flattens auxiliary checking into one local certificate/tableau relation before bounded-universal elimination, rather than independently eliminating every nested subrelation.

## 4. A precise warning about nondeterministic arithmetic simplification

Unordered FRACTRAN without zero tests has a simple valuation semantics. Let p_1,...,p_d contain every prime dividing the input and every reduced numerator and denominator. Represent an integer n by v(n)=(v_p1(n),...,v_pd(n)). Applying a reduced fraction a/b is legal exactly when

    v(n) >= v(b),

and gives v(n')=v(n)+v(a)-v(b). This is a vector-addition system. Therefore arbitrary selection of applicable fractions discards the prioritized non-applicability tests that permit usual counter-machine simulation. Ordinary vector-addition reachability is decidable; see Leroux and Schmitz, https://arxiv.org/abs/1903.08575.

This blocks a uniform universal-refutation compiler based only on such fraction rules and ordinary reachability. It does not purport to settle one particular fixed consistency instance. Any alternative compiler must retain an actual zero-test, destructive string operation, or another source of universality.

## 5. Logical hygiene

The needed theorem is an internal equivalence in ZFC between polynomial solvability and existence of a finite contradiction proof. It must not assume Con(ZFC), a standard model of ZFC, or Sigma-1 soundness of ZFC. Under the ordinary definition of Con(ZFC), its negation already means existence of a coded finite contradiction proof. Equiconsistency translations must be supplied in both directions and formalizable in ZFC.

In particular, broad prose claims that mere consistency makes all ZFC-provable existential arithmetic statements true must not be imported as a proof step. They require stronger soundness assumptions. The direct proof-predicate/refutation equivalence itself does not require this extra assumption.

## 6. Conclusion

The strongest distinct research direction is fixed-input boundary compilation, potentially reducing coefficient complexity independently of the current Pell/source optimizations. No complete smaller equation, compiler integration, universal input, or end-to-end kernel proof has been produced by this review. The current wave's validated numeric endpoints must come from the separately audited arithmetic constructions.
