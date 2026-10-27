# Established-packet audit and precision peeling

Snapshot: `VladimirReshetnikov/ProveIt@ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`.
This note covers the seven filed `Computability/SubexponentialSAT/Research`
packets and the imported contraction interface. Other agents review the seven
new incoming archives. It is a source audit, not a formal verification of the
upstream theorem or a full SAT solver benchmark.

## 1. Established baseline and what can honestly be compared

`Computability/SubexponentialSAT/README.md:9-15` explicitly states that the
filed packets have not been checked in ProveIt, that all seven depend on the
unchanged OpenAI arguments, and that none supplies an end-to-end solver or
measured speedup. The term "proved" in its tables means a natural-language
derivation in a packet, conditional on its imported results.

Write all logarithms in a fixed base. The strongest established asymptotic
profile in the seven packets is

    poly_k(n,m) 2^{ O_k( n/sqrt(log n)
                       * min(log(2+m/n), log log n) ) }.

Its constants are uniform in the density. It improves intermediate-density
inputs, such as m = Theta(n log log n), but leaves both the unrestricted
n-only order and the fixed-density order unchanged. The direct clause-network
bound can also be retained in the minimum, with the actual normalization paid.

The strongest **conditional target** is
`poly_k(n,m) 2^{O_k(n log log n/log n)}` (and `n/log n` at fixed density).
The structured-mode acceleration algorithm required for it is absent. It
cannot be silently counted as an available algorithm that a new result
dominates, nor can it be advertised as established merely because the
conditional implication is proved.

| Filed packet | What its source actually supplies | Principal source anchors |
| --- | --- | --- |
| `cauchy_mode_improvement` | Integral finite Cauchy separation, weights `1+b+2 v2(b!)`, asymptotic enumeration factor `1/sqrt(3)`; same logarithmic order. Row-dependent weight offset is already observed. | `report.tex:230-350`, especially theorem `thm:weights` and proposition `prop:recursion` |
| `eth_contraction_improvements` | Exact taper count, valid precision near `6 MD/u`, schedule coefficient `648.4410666...` versus the same sharper analysis of the source schedule `18535.7538317...`; streamed coefficient extraction. | `verification/schedule_audit.txt`; `report.tex`, source labels `eq:new-precision`, schedule analysis |
| `3sat_precision_refinement` | Exact precision `p+B_i+(q_i-1)(a+1-i)` and the full-loss minimax taper. Its optimal leading scalar loss remains `6 M/u`. | `report.tex:315-360`, `:475-560`; missing acceleration explicitly at `:738-862` |
| `sat_density_improvement` | Uniform density-aware profile above; expander/local-code/greedy checks and exact finite checks; imported spectral and contraction theorems. | `density_aware_sat_improvement.tex:101-138`, `:183-311`, `:586-635`; `PROOF_STATUS.txt` |
| `eth_density_refinement` | Overlapping density profile for polylogarithmic density; precision/schedule constants. Its factor 16 is a comparison of specified upper bounds. | `report.tex`; `README.txt`; `integration_notes.txt` |
| `3sat_refinement` | Exact scalar parity indicator and cap `k(p+a-1)`, reducing degree constants; a faster recursive factorization remains missing. | `3sat_refinement_report.tex:161-260`; `data/research_status.json` |
| `3sat_asymptotic_analysis` | Explicitly reports no stronger unconditional rate. Several useful restricted barriers and missing interfaces. | `research_decision/findings.md`; `audit/INDEPENDENT_PAPER_AUDIT.md`; `research_runtime/METHOD_BARRIERS.md` |

The precision minimax proof is particularly relevant to novelty: for
`A_i(q)=sum_{j>=1} j 2^{-j}(q_i-q_{i+j})` and
`W(q)=sum_i 2^{-i}q_i`, it already establishes

    min max_i A_i(q) = W/(u/3 + 2/9 - (2/9)4^{-u}).

For required mass `W=2M+o(M)`, this is `(6+o(1))M/u`. A simple new taper
does not remove a factor of u from the cost.

The scalar parity improvement is sound locally: expand
`E_i=(1+(-1)^c_i prod_j(1-2m_ij))/2` over the integers, then reduce. A
coefficient selecting r monomials has factor `2^{r-1}`. Its support has size
at most kr, yielding `v2(c_i,S)>=max(0,ceil(|S|/k)-1)` and the global cap.
Division by two is performed before reduction; it is not a ring inverse.

### Existing barriers that should not be rediscovered as new results

* Weighted tuples with the ordinary-degree constraint still admit an
  `exp(Omega(M/sqrt(u)))` numerical envelope. This is a barrier for that
  envelope, not a lower bound on SAT or every actual network.
* Incidence copies can carry Theta(n log log n) support entropy for legitimate
  solution-preserving parity systems. Avoiding this requires exploiting the
  identification of repeated original variables, not simply shortening an
  injective index.
* Ordinary sparsification followed by a fixed-density black box, and
  exhaustive variable restriction followed by the same black box, do not
  improve the supplied worst-case certificate.
* A one-equation extension-field norm identity does not supply a sufficiently
  cheap coefficient oracle or bounded-degree low-wire representation.
* The reviewed Lean endpoint has a loglog-squared bound. The stronger
  Appendix-D manuscript bound is the correct comparator; removing a
  loglog factor from the Lean endpoint is not a new improvement over the
  manuscript.

## 2. A new exact precision-peeling transformation

The following is independent of any asymptotic schedule improvement. Searches
through the filed and incoming `.tex`, `.md`, and `.txt` material found no
explicit implementation of residual precision `P-sum w beta`; the source
passes full working precision P to every retained mode child. This search
establishes a distinction from the reviewed packets, not global priority.

### Ring and fixed representatives

Use the source integral coefficient ring
`A=O[V]/(V^ell)`; all powers of two and residue operations are coordinatewise
in its fixed integral bases. Fix the canonical representatives of the
current call's tensor entries before constructing its deformation. Denote
the working mode precision by P.

For each mode z, let w_z be a proved nonnegative integer valuation bound.
For every row x targeted by that mode write its coefficient as

    c_xz = 2^{w_z} cbar_xz,       cbar_xz in A.

Every affine row factor has the form

    a_x + sum_z c_xz Z_z.

The signs from `l_0(t)=1-t` and `l_1(t)=t` can be included in c_xz; they do
not alter divisibility. The constant a_x includes the local interactions.

### Coefficient identity

For any multi-index beta, substituting
`Z_z -> 2^{w_z} Z_z` in the product of the normalized affine factors gives
the exact identity

    [Z^beta] prod_x(a_x + sum_z c_xz Z_z)
      = 2^{sum_z w_z beta_z}
        [Z^beta] prod_x(a_x + sum_z cbar_xz Z_z).

This uses only polynomial substitution. It is valid with cancellation,
nilpotents, negative entries, and zero factors; it does not assume that
valuation of a sum equals the minimum valuation of its summands.

In a packet/group tensor, apply the identity to its target modes and retain
the original source-moment factor `prod_z L_z(X)^{beta_z}`. Let
`v_pg(beta)` be the sum of `w_z beta_z` over modes targeted at packet p,
group g. Its packet tensor equals `2^{v_pg}` times a normalized integral
packet tensor. Summing its products over Boolean edge assignments gives

    Z_g,beta = 2^{v_g(beta)} Zbar_g,beta,
    v_g(beta) = sum_p v_pg(beta).

Each mode has exactly one target, so `sum_g v_g(beta)=V(beta)=sum_z w_z beta_z`.

### Theorem (residual precision)

For every retained tuple with `V(beta)<P`, put `Q(beta)=P-V(beta)`. Then

    F(t+alpha zeta)
      = sum_{V(beta)<P} 2^{V(beta)}
          prod_g (Zbar_g,beta mod 2^{Q(beta)})        (mod 2^P).

Consequently each normalized child may be contracted modulo `2^{Q(beta)}`,
using exactly the same graph and Boolean ports. When `V>=P`, the whole
contribution is zero and no child is needed.

Proof: substitute the exact coefficient identity into the existing
factorization. Products of integral quantities are polynomial expressions,
so computing them modulo `2^Q` introduces an error divisible by `2^Q`.
Multiplication by `2^V` makes every error divisible by `2^P`. Summing terms
does not lose precision. No cancellation assumption is needed.

### Safe division and required information

To compute `cbar_xz mod 2^Q` using modular rather than symbolic arithmetic,
first compute `c_xz mod 2^{Q+w_z}`. Its coordinate representatives are all
divisible by `2^{w_z}`; divide them as integers, obtaining the desired
residue modulo `2^Q`. Alternatively, cancel known powers of two in the exact
kernel factors and invert only units. Never divide a residue known only
modulo `2^Q` and claim Q correct quotient bits.

Modes with `beta_z=0` can be omitted from this coefficient extraction. For
every used mode, `w_z<=V(beta)`, hence `Q+w_z<=P`. Thus the original working
precision is sufficient for all needed divisions; the transformation does
not require access to any unknown higher-precision tensor entry.

### Lowered child precision and canonical lifts

The original source relies on precision increasing along a recursion path:
`quantitative-contraction.tex:57-71`. Residual precision can violate that
assumption. It must not be patched by recomputing an old tensor's defining
formula at a different precision.

Instead, make the normalized child a newly specified network over `A_Q`.
For every retained parent entry, evaluate its *already fixed canonical
representative*, reduce it modulo `2^Q`, and freeze the resulting canonical
residue as the child's entry. New normalized packet entries are similarly
created and frozen at Q. A later call may lift those Q-bit representatives,
not the earlier parent representatives or a newly recomputed formula.
Polynomiality of contraction ensures that this change preserves the
required result modulo `2^Q`.

A retained-entry descriptor can be implemented as `(original descriptor,
precision_cap)`. When an additional cap Q is imposed, replace the cap by
`min(old_cap,Q)`. Canonical coordinate reductions modulo powers of two
compose in this way. Hence no unbounded tower of entry-evaluator wrappers
is needed. The original creator evaluator can be used at its original
precision, followed by the cap; direct original evaluation at a new
precision is not assumed available.

### Scope of the complexity improvement

* Network sizes, maximum degrees, mode inventories, and structural recursion
  depth are unchanged. Space remains bounded by the existing polynomial
  envelope. All residual precisions are between 1 and P.
* The number of retained mode tuples is unchanged. Precision peeling alone
  does not prove a smaller leading mode-enumeration exponent.
* The source bounds the next interpolation precision by inherited precision
  plus a loss of order `MD/u`. Its schedules make that loss dominate the
  inherited precision. Lowering the inherited term therefore does not, by
  itself, change the currently proved leading recursive exponent.
* A retained tensor's old creator evaluator may still incur its old
  precision cost. Therefore one cannot infer that **all** costs inside a
  normalized branch scale with Q. The proven savings apply to operations
  actually moved to `A_Q`, such as subsequent coefficient arithmetic,
  products, direct contractions, and accumulators after safe normalization.
* Benchmarks of those arithmetic kernels are meaningful. They are not a
  runtime comparison of full SAT solvers. The transformation can be combined
  with any of the improved weights/packing schedules because it only uses
  their already proved coefficient divisibility.

## 3. Exact aggregate precision-work identities

Fix the available modes and any precision-independent degree/support
constraints on feasible tuples. Let

    N(t) = #{ beta feasible : V(beta)<t },       t>=1.

The total bit-precision charge for one operation per retained tuple is

    S(P) = sum_{V(beta)<P} (P-V(beta)) = sum_{t=1}^P N(t).

This follows by writing the positive integer `P-V` as a sum of that many
ones and exchanging finite sums. Uniform precision would charge `P N(P)`.
Thus `S(P)<=P N(P)`, strictly if any retained positive-weight tuple exists.
This is an exact arithmetic-work model; it is not a universal timing bound.

More generally, for any nondecreasing cost model f on nonnegative integers
with `f(0)=0`,

    sum_{V(beta)<P} f(P-V(beta))
      = sum_{q=1}^P (f(q)-f(q-1)) N(P-q+1)
      <= N(P) f(P).

This makes finite-DP comparisons reproducible without treating tuple counts
as runtimes. A full weight distribution also permits reporting the exact
median and percentile residual precisions. A heuristic saddle-point argument
suggests residual width `Theta(sqrt(P/c))` for c-colored partition models,
but no local-limit theorem is supplied here; do not present that heuristic
as an established average-case SAT guarantee.

### A rigorous aggregate tilted upper certificate (parent's observation)

Let alpha>0 and theta>0. For a finite mode inventory define

    Z(theta) = prod_z (1-exp(-theta w_z))^{-1}.

Dropping any additional tuple restrictions only increases this product
envelope. With q=P-V(beta)>0, the exact identity

    q^alpha = exp(theta P) exp(-theta V(beta))
              q^alpha exp(-theta q)

and `sup_{q>0} q^alpha exp(-theta q)=(alpha/(e theta))^alpha`
give the rigorous bound

    S_alpha(P) = sum_{V(beta)<P} (P-V(beta))^alpha
       <= (alpha/(e theta))^alpha exp(theta P) Z(theta).

The full-precision certificate obtained from the *same* generating-function
bound is `P^alpha exp(theta P) Z(theta)`. The peeled certificate is its
factor `(alpha/(e theta P))^alpha`. If theta P>=alpha, that factor is
strictly less than one. It is a comparison of these upper certificates,
not a lower bound for the full-precision implementation.

For a genuine operation model charged exactly q^alpha, the earlier exact
finite-sum identity directly compares the work totals. For generic modular
arithmetic bounded by `C q^alpha`, the tilted estimate is a valid upper
bound when C and any per-tuple operation-count factor are uniform. Costs
not moved to q-bit arithmetic must be added separately.

For c copies of asymptotically linear mode weights `w_b~gamma b`, the
existing entropy estimate is

    log Z(theta) <= (A_gamma+o(1)) c/theta,
    A_gamma=pi^2/(6 gamma).

Use the entropy saddle `theta=sqrt(A_gamma c/P)`. Then
`theta P=sqrt(A_gamma c P)`, and the peeled polynomial-prefactor
certificate is smaller by

    (alpha/(e sqrt(A_gamma c P)))^alpha.

In the contraction regime `c=Theta(M/D)` and `P=Theta(MD/u)`, this is
`O((sqrt(u)/M)^alpha)` for any fixed alpha. The exponent remains
`Theta(M/sqrt(u))`. The o(1) entropy term is the same one in the
full-precision envelope; no unproved local-limit estimate is needed for
this comparison.

One may further optimize the explicit idealized envelope
`theta P + A_gamma c/theta - alpha log theta`. Its stationary point is

    theta_alpha = (alpha + sqrt(alpha^2+4 A_gamma c P))/(2P),

the unique positive solution to `P theta^2-alpha theta-A_gamma c=0`.
This is a finite-bound improvement, not a change in the leading exponential
constant or logarithmic order. The claimed gamma entropy bound must still
be applied in its valid regime and with its actual lower-order correction.

## 4. Required tests for the prototype

1. Exhaustive affine coefficient identities with positive, negative, and zero
   coefficients; compare independent integer expansion with both full and
   peeled modular evaluation.
2. Boundary tuples `V=0`, `V=P-1`, `V=P`, and `V>P`.
3. Deliberate unsafe-division regression, e.g. `c=2^w` and `Q=1`: quotient
   from c mod2^Q is wrong when w>=Q, whereas mod2^(Q+w) is sufficient.
4. Truncated extension-ring arithmetic and cancellation, not just scalar
   nonnegative values.
5. Canonical-cap regression: an old entry 5 at precision 3, lowered to Q=2,
   must become the frozen entry 1 if later lifted to precision 4; reusing 5
   would violate the new child specification. Repeated caps must equal their
   minimum even when later call precisions increase.
6. Exact identity `S(P)=sum_{t=1}^P N(t)` from independently enumerated small
   tuple families and from a dynamic-programming weight distribution.
7. Dense integral kernel workloads should use identical entries, topology,
   modular outputs, and arithmetic algorithm in both arms; any precomputation
   excluded from timing must be identified. Interpret measured improvements
   only at the tested precision, tensor size, and workload.

## 5. Upstream integration anchors

All below are in the vendored `build/quantitative-contraction.tex`.

* Lines 46-47: divisibility and precision are coordinatewise.
* Lines 57-71: frozen creation-time representatives and monotone precision.
* Lines 449-455: coefficient valuation `sum w beta` and truncation.
* Lines 487-508: child network and packet-entry definitions.
* Lines 510-523: factorization identity to which peeling applies.
* Lines 531-550: packet-entry arithmetic and immutable descriptors.

These anchors justify a narrowly scoped patch to the current formulation,
while making the changed precision-lifting invariant explicit.
