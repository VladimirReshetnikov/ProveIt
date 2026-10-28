# Exact Heisenberg structure blocks a free sub-square-root entropy gain

**Status.** New elementary deductions made during source review; these are restrictions on particular proposed modifications of the alternate manuscript's operator construction. They are not lower bounds for SAT, tensor contraction in general, all crossing decompositions, or all graded algebras. No source code was executed to obtain them.

## Source and intended improvement

Source: `../sources/proveit/eth.pdf`, *A 2^{o(n)} Time Algorithm for 3-SAT*, attributed in the PDF to Claude / Anthropic, 49 pages, SHA-256 `f0af035b6c87d04d3fcf07dae040df98029f4990c6493e3e9ab64c4ac714c0eb`.

- Appendix B, p. 30: `V=Q[t_1,t_2,...]`, `deg(t_m)=m`, `dim V_E=p(E)`; `nabla_{-m} f=t_m f`, `nabla_m f=m partial f/partial t_m`.
- Appendix B, definition (47), p. 30: `a[r]` sums normally ordered mode products over tuples with `sum k_i=-r`; (O1) says it maps `V_E` to `V_{E+r}`.
- Appendix B, Lemma 9, pp. 30-31: finite-order locality makes the two operator orders give the same pieces; Lemma 10, p. 32: a complete dual family reconstructs the crossing.
- Appendix B, equation (56), p. 32: combined row/column bits `<=2 sqrt(2) lambda+O(log lambda)`.
- Appendix H, p. 48, equation (76): `[nabla_m,nabla_{-n}]=m delta_{mn} Id`; p. 49 identifies the Heisenberg Fock representation and ordinary vertex-algebra locality.
- Appendix H, p. 49, equation (77) and next paragraph: if the same construction worked with `log dim V_E ~ C E^alpha`, its concavity calculation would give `rho=2^{alpha-1}`.
- Theorem A, pp. 27-29: the final logarithmic denominator power is `log_2(1/rho)`. Thus a valid alpha<1/2 replacement would yield power `1-alpha>1/2`, subject to every effective-piece requirement of Definition 7, pp. 26-27.

The tempting shortcut is to reduce graded dimensions without changing the algebraic identities. The following lemmas show exactly why that shortcut fails.

## Lemma 1: creation monomials force partition entropy

Let F be a field of characteristic zero. Let `W=direct_sum_E W_E` be a graded F-vector space, with `0!=v in W_0`. For every integer m>0, assume operators `a_{-m}` and `a_m` such that:

1. `a_{-m} W_E subset W_{E+m}` and `a_m W_E subset W_{E-m}`;
2. `[a_{-m},a_{-n}]=0` and `[a_m,a_n]=0`;
3. `[a_m,a_{-n}]=m delta_{mn} Id`;
4. `a_m v=0`.

Then `dim_F W_E >= p(E)` for each nonnegative integer E, where p(E) is the ordinary partition number.

**Proof.** Let beta range over the finite-support nonnegative integer sequences satisfying `sum_m m beta_m=E`. Define

`v_beta=(product_m a_{-m}^{beta_m})v`.

The factors commute, and `v_beta in W_E`. Suppose `sum_beta c_beta v_beta=0`. Fix beta and apply `A_beta=product_m a_m^{beta_m}`. Commuting annihilators past creators and using the vacuum condition gives

`A_beta v_gamma = 0` if some beta_m>gamma_m,

and gives `A_beta v_beta=(product_m m^{beta_m} beta_m!)v`.

If gamma!=beta but both have weighted sum E, some beta_m>gamma_m: otherwise beta<=gamma componentwise, with at least one strict inequality, which would make the weighted sum of gamma larger. Thus applying A_beta kills every term except beta, so

`c_beta (product_m m^{beta_m} beta_m!)v=0`.

The product is nonzero in characteristic zero and v!=0; hence c_beta=0. This holds for every beta. There are p(E) such beta. QED.

**Consequence.** The Hardy-Ramanujan partition estimate implies `log dim W_E >= Omega(sqrt(E))`. A bound `log dim W_E=O(E^alpha)` for alpha<1/2 is impossible under these exact assumptions. In particular, a nonzero quotient preserving the vacuum and all Heisenberg modes/relations cannot provide the proposed entropy reduction.

**What this does not prohibit.** A genuinely different algebra, finitely many modes, positive characteristic, altered locality, an approximation with controlled exact recovery, or a new encoding could escape an assumption. Each would have to reconstruct the crossing and effective factorizations afresh; the lemma does not say such constructions cannot exist.

## Lemma 2: infinitely thinning the standard current destroys ordinary finite-order locality

Retain the exact mode commutators, and let S be a subset of positive integers. Define the formal current

`J_S(z)=sum_{m in S}(a_m z^{-m-1}+a_{-m} z^{m-1})`.

Its scalar commutator distribution is

`[J_S(z),J_S(w)]=Id * sum_{j in Z} c_j z^{-j-1}w^{j-1}`,

where `c_j=j` when `|j| in S` and `c_j=0` otherwise (including j=0).

If S and its complement among the positive integers are both infinite, no finite H makes

`(z-w)^H[J_S(z),J_S(w)]=0`.

**Proof.** Multiplication by z-w replaces the coefficient sequence c_j by the forward difference `Delta c_j=c_{j+1}-c_j`, after reindexing the monomials. H multiplications therefore force `Delta^H c_j=0` for all integers j. Over a characteristic-zero field, such a sequence is a polynomial in j of degree at most H-1 (Newton's finite-difference formula). Because the positive complement of S is infinite, that polynomial has infinitely many roots and is zero. Because S is infinite and positive, some c_j=j!=0, a contradiction. QED.

For all positive modes, c_j=j and H=2 is sufficient, recovering ordinary Heisenberg-current locality. A periodically thinned current can instead have locality at additional root-of-unity diagonals, but that is not the ordinary locality used by the printed proof, and periodic thinning does not change the partition entropy power anyway. The lemma only rules out the naive sparse current; it does not establish impossibility for all generalized locality mechanisms.

## Observation 3: nonlinear mode regrading breaks the printed homogeneous-shift identity

The original definition `a[r]` groups mode products by the linear equation `sum_i k_i=-r`, and `deg(nabla_k)=-k`. This gives (O1) term by term.

If instead `deg(t_m)=f(m)`, then `deg(nabla_m)=-f(m)` and `deg(nabla_{-m})=f(m)`. A product's degree is now `-sum_i sign(k_i) f(|k_i|)`, which is not determined by `sum_i k_i` for nonlinear f. In particular, weighting available variables by squares or higher powers to reduce partition entropy does not preserve `a[r]:V_E -> V_{E+r}` for the same operators and indexing.

Only linear changes f(m)=cm preserve the additive mode rule globally, and these merely rescale energy, leaving the sqrt(E) entropy exponent unchanged. Changing both the indexing and the generating functions might define something else, but Lemmas 9 and 10 and the factorization estimate would then need new proofs.

## Research gate

To obtain a real asymptotic improvement through this route, propose and verify a replacement satisfying **all** of the following:

1. A full exact crossing decomposition, not just a smaller Hilbert series.
2. Enough independent paired operators to name all `2^lambda` x/v values and all `2^lambda` y/u values.
3. A valid equality between the two operator orders (or an alternative supplying both integer factorizations).
4. Combined bit cost below `2 sqrt(2) lambda` by a fixed positive linear fraction, uniformly in every piece, up to O(log lambda).
5. Polynomially many pieces, polynomial coefficient bit lengths, and `2^{O(lambda)}` effective evaluation as in Definition 7.

A generic dimension guess with alpha<1/2 is not yet an algorithm, and the existing exact Heisenberg algebra cannot supply it unchanged.
