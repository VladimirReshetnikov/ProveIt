# Finite universal histories: tag systems, Rule 110, and halting rectangles

This is an independent research note, not a replacement certificate. The published frontier remains the 90-operation system. Fixed numerals and equality tests are free; multiplication by a fixed numeral is an operation. A short program or a small universal machine is useful here only if it makes the **whole unbounded history verifier** cheaper. Compiling a smaller machine through the existing generic coefficient construction would not by itself save an operation.

The source facts below use primary publications. The arithmetic identities, proposed architecture, rankings, and obstacles are our deductions. None of the publications claims the operation counts proposed here.

## 1. Ranked directions

| Rank | Machinery | Finite acceptance semantics | Concrete arithmetic opportunity | Main unresolved cost |
|---|---|---|---|---|
| 1 | A finite Wang-tile halting rectangle | A finite valid rectangle with an initial edge and a halting corner | Linear edge matching, quadratic nonnegative energy, and implicit row geometry; potentially remove the second Pell exponent block | Tile membership, encoded input, and all boundary conditions in a uniformly short verifier |
| 2 | Rule 110 with Cook's prescribed initial configuration | A finite halting pattern appears after finitely many steps from a finitely described configuration with periodic infinite tails | Seven ordinary operations verify all local transitions simultaneously, conditional on bit planes and alignment | Bit-plane restriction, shared-tableau shifts, and a faithful finite cone instead of an unjustified finite cylinder |
| 3 | Neary's binary two-production tag system | A finite queue reaches length below its fixed deletion number | One shared nonlinear product per transition; eventual halting needs no intermediate prefix guards | Encode a common selector, its nonuniform word expansion, sampled symbols, and the ordinary input |

This order is a research judgment about the prospects for reducing the present certificate, not a comparison of computational power. Rule 110 has the most explicit small local arithmetic relation; finite rectangles currently have the cleaner finite-boundary interface.

## 2. Primary-source and semantic boundaries

**Binary tag systems.** Neary's published STACS 2015 paper proves undecidability of finite-word halting for a two-symbol tag system. The construction uses deletion number beta = 4p and rules b -> b, c -> u; the fixed word u encodes the simulated cyclic-tag program. Definition 5 defines halting as reaching a word of length below beta, and Lemma 9 supplies the halting modification. This is two productions, not deletion number two. See pp. 651-656 of [the published paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).

The binary deletion-number-two halting and reachability problems are decidable, as proved in De Mol's [2010 paper](https://www.logica.ugent.be/sites/default/files/publications/FI_Solv.pdf). Do not conflate these models. Also, Neary's [2013 arXiv version](https://arxiv.org/abs/1312.6700) has a four-pair PCP claim, while the published paper proves five pairs. This note uses the published construction and makes no simulation-speed claim.

**Rule 110.** Cook's 2009 compiler takes a Turing machine and tape to a central binary pattern with periodic left and right tails. A specified finite spatial pattern appears if and only if the simulated machine halts; this is an event in an evolving cellular automaton, not literal cessation of all cell updates. See pp. 31-32 of [A Concrete View of Rule 110 Computation](https://arxiv.org/pdf/0906.3248). The cited theorem does not replace the tails by zeros or give arbitrary finite-cylinder semantics.

**Finite halting rectangles.** Salo, Theyssier, and Torma explicitly construct Wang tiles whose finite valid rectangles, with the stated initial row, side colors, and halting corner, correspond to halting Turing computations. A surrounding frame and its validity can be specified by forbidden 2-by-2 patterns. See pp. 38-39 of [Cellular automata and bootstrap percolation](https://www.utupub.fi/bitstream/handle/10024/155519/1-s2.0-S0304397522002249-main.pdf?sequence=1). We use that finite construction, not the paper's probabilistic CA decision problem, nor unrestricted infinite-plane tileability. Its blank-input machine can have the desired program/input built into it; obtaining our existing fixed-index/query interface economically is a further encoding task.

## 3. Rule 110: a local polynomial and a seven-operation global relation

Let a,b,c be the left, center, and right bits, and y the next center bit. The rule table is exactly

    y = b + c - bc(1+a).

As a scalar relation this uses two multiplications and three additions/subtractions, once bitness is given. It must **not** be applied to ordinary packed integers by writing BC for the coordinatewise products b_i c_i. Ordinary multiplication computes a convolution.

There is, however, a linear alternative that works directly on packed integers. For each local triple introduce four bits

    d = b AND c,       x = b XOR c,
    e = a AND d,       z = a XOR d.

Then the rule is equivalent to

    b+c = x+2d,
    a+d = z+2e,
    y+e = x+d.                                            (R)

To prove the converse, the first equality between bits uniquely gives d=bc and x=b+c-2bc. The second uniquely gives e=ad and z=a+d-2ad. Substitution in the third gives y=b+c-bc-abc. Each triple a,b,c has exactly the intended output and intermediate bits.

Now take any R >= 4 and equally long bit planes

    A = sum a_i R^i, B = sum b_i R^i, C = sum c_i R^i,
    Y = sum y_i R^i, D = sum d_i R^i, X = sum x_i R^i,
    E = sum e_i R^i, Z = sum z_i R^i.

Impose the three ordinary integer equalities

    B+C = X+2D,       A+D = Z+2E,       Y+E = X+D.           (PR)

On each side, every coefficient lies between 0 and 3, strictly below R. There are no carries, so uniqueness of base-R expansion proves (R) independently at every slot. Direct evaluation takes eight operations, but the register X+D is required by the third equality and can also form X+2D. The improved exact conditional schedule is:

| Step | Register | Operation |
|---:|---|---|
| 1 | xd_sum | X + D |
| 2 | bc_sum | B + C |
| 3 | xd2 | xd_sum + D |
| 4 | e2 | 2 * E |
| 5 | ad_sum | A + D |
| 6 | ze2 | Z + e2 |
| 7 | ye_sum | Y + E |

The free tests are bc_sum=xd2, ad_sum=ze2, and ye_sum=xd_sum. Thus this entire local-transition part costs **7 = 1 multiplication + 6 additions**, independently of the number of slots. The table does not include proving bitness, choosing the planes from a single tableau, their ranges, or input/output conditions. Some valid planes can be zero, so a final system over strictly positive supplied unknowns must handle those values explicitly; no zero-coordinate convention is being assumed free.

### A single conditional bit predicate

For R a power of two, write J_N=(R^N-1)/(R-1). If 0 <= P < R^N, then

    P and (R-2)J_N have no common binary 1-bit

holds exactly when all N base-R digits of P are 0 or 1. Thus, given eight plane bounds below Q=R^N, their concatenation

    P = A + Q B + Q^2 C + Q^3 Y + Q^4 D + Q^5 X + Q^6 E + Q^7 Z

can be restricted by one no-carry predicate with mask (R-2)J_(8N). The concatenation, mask, bounds, and arithmetic realization of this predicate all remain charged work. In particular, without the individual plane bounds, overflow can reassign bits across adjacent planes. The project's previous packed-bound counterexamples make this qualification essential.

This route could remove the generic coefficient compiler's arbitrary integer coordinates, splitting, and unit normalization. It does not yet remove the Pell arithmetic that currently realizes the no-carry predicate.

### Alignment and finite-cone obligations

A,B,C,Y must be the overlapping neighborhood and successor views of one space-time array. Independent planes satisfying (PR) alone merely describe an arbitrary collection of valid local transitions. Row shifts, truncated edges, and the prescribed first row must be enforced.

A finite-time Rule 110 event depends only on a finite backward cone, by radius-one locality. Therefore a faithful finite witness exists for Cook's theorem if that cone's initial segment agrees with the prescribed central pattern and periodic tails. This is our finite-dependence deduction. Closing an arbitrary finite rectangle into a cylinder is insufficient: wrapped copies of the central pattern can interact and generate events absent from the required infinite configuration. Either the cone geometry or an equivalent boundary-isolation argument must be encoded and paid for.

## 4. Implicit rectangular geometry can avoid a variable-base exponent

Here is a separate exact arithmetic observation. Suppose q>1 is already known to be a power of two, and positive integers v,d,h satisfy

    q = v d,
    Q = q^2,       W = v^2,
    Q-1 = h(W-1).                                          (G)

Then v is a power of two, and v cannot be 1 because Q-1>0. Write q=2^N and v=2^m, with N,m positive. The elementary divisibility equivalence

    4^m-1 divides 4^N-1  iff  m divides N

shows that N=mt for a positive integer t. Consequently

    Q = W^t,
    h = 1 + W + ... + W^(t-1).

For completeness, reduce N modulo m, say N=km+r with 0<=r<m. Modulo 4^m-1, the remainder of 4^N-1 is 4^r-1, which is nonnegative and strictly smaller than the divisor. It vanishes exactly when r=0.

The base-four digit width m and number of rows t need not be supplied as numerical witnesses. W is the row-shift multiplier, Q is the total-array bound, and h is already the row-start mask. This is particularly natural for the finite halting rectangle model, whose boundaries have genuine finite semantics.

In the present system, the first exponent interface proves U=2^J with U=w n^2. The relation n=q^8 then makes q a power of two. Therefore (G) is a plausible way to use that conclusion while deleting the **second** Pell exponent/index block, rather than replacing it by another general exponent certificate. This is an architectural proposal, not yet a valid deletion from the published equations. The first exponent proof currently depends on the packing's size bounds; a new tableau construction must re-establish those bounds before invoking it. Counts for the new geometry, bit masks, boundary tests, and input interface must be compared against all removed instructions together.

The usual direct parametrization Q=R^(width*height) would hide two variable exponents. Relation (G) is useful precisely because it derives the rectangular geometry from divisibility and already certified powers of two.

## 5. Halting tiles: quadratic energy and a convolution target

Let a finite rectangle contain tiles from a fixed alphabet. If tile membership has been established, encode edge colors by distinct integers. Write E_v,W_v,N_v,S_v for the four edge labels at cell v. Then

    energy = sum_horizontal (E_v-W_(v+right))^2
           + sum_vertical   (N_v-S_(v+up))^2

is nonnegative and vanishes exactly when all internal edges match. Boundary residuals can be added as further squares. With Boolean one-hot tile selectors, the color labels are fixed linear forms, so every edge residual is linear and the energy is quadratic. This is a structural advantage over first encoding arbitrary integer multiplication gates and then testing their equations.

There is an exact global correlation identity. For any integer residuals r_0,...,r_(M-1), define

    F(z) = sum r_i z^i,
    F_rev(z) = sum r_i z^(M-1-i).

Then

    coefficient_(M-1) [F(z)F_rev(z)] = sum r_i^2.           (C)

Thus a single ordinary multiplication could test all residuals through one central coefficient, **if** reversal, the coefficient window, signed coefficient bounds, and extraction were certified cheaply. Supplying an unrelated second polynomial cannot substitute for proving reversal. At an integer radix, uncontrolled lower coefficient carries also invalidate naive coefficient extraction.

Regular-grid shifts and collision-free diagonal products pull in opposite directions. With affine exponents w_i=u+si, the unavoidable identity

    w_(i-1)+w_(i+1)=2w_i

means that the square coefficient intended for the i-th coordinate also receives cross terms. Sidon-style exponents can isolate products, but then neighboring grid positions do not differ by a uniform shift. The existing fixed support construction solves a finite collection of such collisions; here the history length is unbounded, so a new uniform mechanism is required.

The specific next experiment is a fixed tile alphabet, row-start mask h from (G), packed one-hot selectors, and a nonnegative mismatch count. A successful construction must include selector membership and boundary/input conditions; zero energy for unconstrained edge colors alone is trivial.

## 6. Binary two-production tags: one shared product, nonuniform histories

Use b=0 and c=1, and encode a finite word with its first symbol in the least significant bit. Let N be its integer value, ell its length, Z=2^ell, beta the fixed deletion number, and K=2^beta. Let s be its first bit, d its deleted beta-bit prefix, and let u have fixed length m and fixed little-endian value U_u. Assume ell>=beta, 0<=N<Z, 0<=d<K, d congruent to s modulo 2, and s in {0,1}.

The successor word value N' and length power Z' satisfy exactly

    K N' = N-d + U_u s Z,
    K Z' = 2Z + (2^m-2)s Z.                               (T)

Indeed, deleting beta bits leaves (N-d)/K, and the appendant begins at bit ell-beta. The b appendant has value zero and length one; the c appendant has value U_u and length m. Defining W=sZ shares the only product between two variable coordinates. The other coefficients are fixed, but multiplying by them is still charged arithmetic. Correct prefix and bit constraints are essential, and the initial Z must be tied to the encoded input length.

After a correct first transition, the property of being a power of two propagates through (T): Z'=2^(ell-beta+1) for s=0 and Z'=2^(ell-beta+m) for s=1. This could avoid repeated exponent tests across the history. It does not give a constant-size verifier for arbitrarily many transitions on its own.

### A finite-stream reformulation without intermediate prefix guards

For a proposed sequence of read bits s_0,...,s_(t-1), let h(0)=b and h(1)=u. The complete produced stream is

    word_initial h(s_0) h(s_1) ... h(s_(t-1)).

The j-th read bit occurs at absolute stream position beta*j. To certify exactly the proposed sequence of legal transitions, one would also impose the causal prefix inequalities

    beta*(j+1) <= ell_initial + sum_(i<j) |h(s_i)|,
    0 <= ell_initial + sum_(i<t) |h(s_i)| - beta*t < beta

for j=0,...,t-1, the second line being final halting. The formal queue length before transition j is

    ell_j = ell_initial + j*(1-beta) + (m-1)*sum_(i<j) s_i.

For the eventual-halting language, however, the intermediate inequalities are unnecessary. The sampled-symbol equations and final length window alone imply a genuine halt: take the first j with ell_j<beta. All earlier sampled symbols lie in already produced prefixes and give actual legal steps, so this j is a real halting time. Any self-supported symbols later in the proposed stream can be discarded. Conversely a genuine halting run supplies such a stream. The complete general proof and fresh regression are in `EXPLORATION_TAG_HALTING_WITHOUT_PREFIX_GUARDS.md` and its checker. This corrects the earlier claim that prefix positivity was an additional obligation for representing eventual halting.

The variable-length word substitution, sampled-symbol relation, final window and ordinary-input encoding still need a complete counted implementation. Replacing both appendants by equally long padded words is not an innocuous shortcut: if all appendants have fixed length m, the queue length evolves deterministically by ell_j=ell_initial+j*(m-beta), and length-based halting is decidable without inspecting the symbols. The unequal lengths carry necessary computational content for this halting model.

The published five-pair PCP reduction suggests a related finite-word formulation: equality of two fixed morphism images of one nonempty selector word. The selector's two variable-length expansions still have to be verified. A small number of fixed morphisms is not itself a short arithmetic certificate for their unbounded products.

There is a further exact simplification boundary: if every appendant is a power of one common word v, halting is decidable. All produced streams are prefixes of wv^infinity, so the read symbols and queue-length increments are eventually periodic. A finite prefix, one period, and its drift decide the first short queue. This includes binary systems with one empty appendant. The general proof, exact halting-time algorithm and fresh checks are in `EXPLORATION_COMMON_WORD_TAG_HALTING.md`; unequal lengths alone do not avoid this common-word restriction.

## 7. Evidence and next decision

The exact mathematical results in this note are the conditional Rule 110 identity (PR), implicit geometry lemma (G), correlation identity (C), tag transition identity (T), and the linked eventual-halting stream criterion without prefix guards. Source universality does not by itself validate their composition into a fixed-size Diophantine system. There is no new operation frontier or complete positive-witness theorem here.

The most valuable next target is a complete regular-grid verifier using already certified powers of two and the row mask h. If it proves bitness, shared-array alignment, all boundaries, and the query-input relation with fewer operations than the removed coefficient and second-exponent blocks, it would be a genuinely new architecture. Until those costs and their noncircular bounds are explicit, the 90-operation certificate remains the verified result.
