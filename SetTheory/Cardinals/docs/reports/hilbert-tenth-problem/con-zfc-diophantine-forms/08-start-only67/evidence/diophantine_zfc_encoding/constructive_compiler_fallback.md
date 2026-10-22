# A fully specified, constructive fallback (not a completed build)

## Status and what is actually new

An unspecified program index is unnecessary. A literal finite binary Turing-machine table can first be represented by a tiny finite disjunction of polynomial clauses. Larchey-Wendling and Forster's constructive DPRM implementation then supplies a syntax-producing reflexive-transitive-closure constructor. This is a precise route to a fixed finite polynomial AST, not merely the assertion that some polynomial exists. The specialization and extraction have **not** been built or checked in Rocq here, and no final polynomial or numerical variable count from it is claimed.

The candidate table used below is the independently published, exactly pinned K230 machine, not any historical local K214 artifact. Its source repository states and provides an axiom-free theorem equating blank-tape halting with a standard ZFC contradiction. That proof build has not been rerun here. The source's exact transition semantics have been read.

## Exact input

* Machine: https://github.com/elliotglazer/k230-rocq/tree/a8312f0ca703bc81baac16695a437a7d3788f690
* Table: `machine/k230.tm`, copied beside this note. SHA-256: `e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8`.
* States 0 through 229 are working states; state 230 is the only no-row state. Start state is 0; the initial bi-infinite binary tape is all zero.
* A line `q b w D q'` means: in state q reading bit b, write w, move in direction D, enter q'. There are exactly 460 rows, one for each working-state/bit pair.
* Correctness endpoint: `tm230_halts_iff_ZFC_inconsistent` in `coq/tm/Correct230.v`. Its right side is `StandardZFC ⊢TC ⊥`, not a statement of soundness or merely consistency of a weaker subsystem.

## Direct polynomial encoding of one step

All quantities are natural numbers including zero. Put

    pi(x,y) = (x+y)^2+x
    code(q,L,R) = pi(q,pi(L,R)).

Here L contains the bits strictly left of the head, nearest bit least significant. R contains the current bit followed by bits to its right, current bit least significant. Zero-extended infinite strings are identified in the expected way.

The pairing is injective. If s=x+y, then s^2 <= pi(x,y) <= s^2+s < (s+1)^2. Therefore the value determines s, then x, then y. No inverse, floor, order predicate, or square root appears in the polynomial clauses.

For each literal right-moving transition `(q,b,w,R,q')`, the clause is

    exists L,r:
      c = code(q,L,2r+b)
      c' = code(q',2L+w,r).

For each literal left-moving transition `(q,b,w,L,q')`, the clause is

    exists l,r,t:
      t*t = t
      c = code(q,2l+t,2r+b)
      c' = code(q',l,4r+2w+t).

Over natural numbers, t*t=t forces t=0 or 1. Thus each clause exactly represents the corresponding stack update, including zero tape tails. The one-step relation T(c,c') is the finite disjunction of these 460 clauses. All numbers q,b,w,q' are literal constants, so there is no program index to choose and no interpreter to specify.

The blank configuration has code 0. Let

    H := exists L,R,n: T^n(0,code(230,L,R)).

This is an intermediate specification, **not** the finished Diophantine equation: writing T^n or a bounded universal quantifier and calling it polynomial would be incorrect. The next stage actually eliminates iteration and all bounded universals using the constructive library.

## Exact constructive library and constructors

Pin https://github.com/uds-psl/coq-library-undecidability/tree/11c41e0637f0c5219ad1c4c92d11609b7e072c31 .

In `theories/H10/Dio/dio_logic.v`, `dio_rel R` is a dependent pair

    { f : dio_formula | forall nu, df_pred f nu <-> R nu }.

The informative field is an actual finite syntax tree. Its syntax contains only equalities with constants, variables, sums and products, conjunction, disjunction, and existential natural quantification. It does not contain exponentiation, bounded universal quantifiers or iteration.

1. Build `HR : dio_rel (fun nu => T (nu 1) (nu 0))` from the literal table using the elementary closure constructors. Each branch above is directly accepted by those constructors. A list recursion combines branches with `dio_rel_disj` and ends at `dio_rel_False`.
2. Apply `dio_rel_rel_iter` from `dio_rt_closure.v`. Its informative output already expands iteration through `dio_rel_is_seq`, `dio_rel_fall_lt`, digit relations, and the library's complete Diophantine exponentiation construction. These are actual Type-level constructors, not semantic existence axioms.
3. Add the three existential quantifiers and the fixed initial and final-code expressions, obtaining `HH : dio_rel (fun _ => H)`.
4. Let `f := proj1_sig HH` and `l := dio_fs f`, where `dio_fs f := proj1_sig (dio_formula_elem f)` in `dio_elem.v`. Instantiate every free parameter at zero. The resulting finite list l is already a quadratic polynomial system, with no remaining logical disjunction, exponentiation, iteration, or bounded universal quantifier.
5. Optionally use `dio_elem_equation l` in `dio_single.v`, followed by `dio_poly_eq_pos` and `dp_inst_par` with the all-zero parameter valuation. This returns a pair of ordinary finite polynomial ASTs p,q with a finite variable type `pos m`. The single equation is p=q, or p-q=0 over the integers with natural-number witnesses.

The public theorem `dio_rel_single` packages steps 4-5 partially, but direct constructors make extraction and size inspection easier. Some constructors end with `Qed`, hence are opaque to reduction in the proof assistant. Their bodies are still informative and extraction may recover data; do not claim `vm_compute` works through opaque constants without testing. Likewise, the top-level many-one undecidability theorem is a Prop-level existence claim: it is not itself a function one can blindly project into Type. The listed syntax constructors avoid that pitfall.

## Rigorous size statement available before extraction

Let s be the actual `df_size f` after step 3, an explicitly computable natural number from the fixed table and pinned constructors. The **theorem**, rather than a stale source comment, `dio_formula_elem` gives

    length l <= 1 + 7s,
    every auxiliary variable index < 8s.

Thus this construction yields at most 1+7s quadratic equations in at most 8s natural variables. The sum of the squared residuals is a single polynomial of degree at most 4. A user demanding an actual numeric count still needs the extraction/build: an unevaluated s is not a numeric size bound.

The library also gives `dio_single_size E <= 2 + 20*length l`, a syntax-node bound for its nonnegative pair p=q. Combining gives <=22+140s syntax nodes. Polynomial expansion can be much larger and is not needed to define the equation.

## Equivalence and remaining obligations

The elementary stack simulation gives H iff the literal K230 machine halts. The published formal correctness theorem gives machine halting iff ZFC has a contradiction proof. Constructive DPRM gives H iff the generated finite polynomial system has a natural solution. All finite arithmetic, finite-machine simulation, and constructive proof transformations can be interpreted in ZFC, so the chain yields the required ZFC-provable equivalence once the specialization and imported theorem bridge are checked.

The remaining engineering obligations are real: compile the specialization against the pinned library; establish the stack-semantics adapter against BusyCoq's tape semantics; extract or otherwise normalize the finite AST; serialize it; verify the final equation and count. No such completion is claimed by this note. The separate compact helical-kernel construction is more promising for the smallest human-readable answer; this fallback is valuable because it has no mysterious machine-index constant.

## Primary publication

Dominique Larchey-Wendling and Yannick Forster, *Hilbert's Tenth Problem in Coq (Extended Version)*, Logical Methods in Computer Science 18(1), article 35, 2022. https://lmcs.episciences.org/9153/pdf . DOI: 10.46298/LMCS-18(1:35)2022. This supplies the constructive elimination rather than merely a nonconstructive application of MRDP.
