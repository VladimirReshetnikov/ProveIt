# A literal universal structural-input active-membrane frontend

Research packet, 2 October 2026. This is an explicit instantiation and proof of a fixed-rule input acceptor, not a new small universal-machine record, a claim of literature priority, a formally verified proof, or a fixed-arity Diophantine equation.

## 1. Result and exact meaning of “fixed”

The files in this packet specify, without unexpanded instruction macros:

- The independently primary-checked Neary–Woods 15-state, two-symbol TM table, with 29 defined instructions
- A deterministic 528-instruction three-register ADD/SUB program
- A deterministic **8,408-instruction two-register ADD/SUB program**
- A **34,605-rule polarizationless noncooperative active-membrane rule set**, using **19,162 object symbols and four membrane labels**

The finite rule set, alphabet, labels, and initial control object are fixed. The input is a positive integer A. Its structural loader puts A+1 empty label-1 membranes, one empty label-2 membrane, and one empty delay membrane under the skin. The total initial population is A+4 including the skin. Thus the initial membrane tree varies with input; we do not call its expanded size a fixed constant or attribute this input convention to the original generative theorem.

**Theorem.** For every positive integer A, the loaded membrane system has a globally halting maximally parallel computation if and only if the specific displayed Neary–Woods machine, started in state A with scanned symbol 0 and half tapes

    L = v_2(A),  R = v_3(A),

halts. Here v_p is the exponent of prime p in a positive integer. These valuations describe the input contract; they are not rule primitives, decoding oracles, or extra operations available to the simulator. The simulator uses only its literal ADD/SUB table, then the literal membrane rules.

Consequently this fixed-rule structural-input acceptor has a computably enumerable complete halting language. The completeness reduction uses the paper's effective finite TM encoding to obtain L,R, followed by the explicitly charged external map A=2^L 3^R. No constant-cost arithmetic implementation, fixed-arity polynomial representation of variable exponentiation, or numerical Diophantine-record improvement is claimed.

Acceptance is **existence of a globally halting run**, meaning no rule is applicable anywhere. It is not the presence of the HALT object, all-branches halting, or deterministic membrane acceptance. The counter program is deterministic, but incorrect nondeterministic membrane guesses can create a persistent trap even on accepting inputs.

## 2. Primary sources and repairs

1. T. Neary and D. Woods, *Four Small Universal Turing Machines*, Fundamenta Informaticae 91(1), 123–144 (2009), Table 16 and its bi-tag encoding: https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf . The primary paper and Table 16 were inspected during the audit; use the linked source. Third-party PDFs and images are not redistributed in this packet. The concrete serialization is https://github.com/Iijil1/MTGPrograms/blob/main/Examples/UniversalTM15x2.tm.txt . The source bytes are copied into `source/UniversalTM15x2.tm.txt` and pinned by SHA-256 in the verifier. The primary-source comparison and the exact two-half-tape input contract were previously established in the accompanying Waterfall packet's `FRONTEND-PROOF.md`; a copy of that reference proof is included in `source/` for audit continuity.
2. A. Alhazov, R. Freund, and A. Riscos-Núñez, *Membrane division, restricted membrane creation and object complexity in P systems*, International Journal of Computer Mathematics 83(7), 529–547 (2006), DOI 10.1080/00207160601065314, Theorem 4.1, PDF pp.13–15. Primary institutional PDF: https://idus.us.es/bitstreams/dcac15aa-404e-4102-88e2-08ec23b7df8a/download . The audited PDF hash and primary URL are recorded in `SOURCE_PROVENANCE.json`; the PDF is not redistributed.

The primary TM table has u15,b -> b,R,u14 and leaves u10,b undefined. With c=0,b=1 and u1=A,...,u15=O, the unique undefined instruction is J1. The conflicting later prose that says u10,c is not used. The universal initial head is on the rightmost c of the encoded G=bc and starts in u1; both half tapes are allowed to vary.

The 2006 theorem is originally a compiler for nondeterministic two-register **generation from zero registers**, with output interpreted only on halting computations. This packet does not infer an input acceptor from the theorem statement alone. Sections 5–7 below prove the arbitrary structural-input adaptation and the exact existential-halting interface.

Relevant display repairs and adaptations are explicit:

- The missing comma between [t -> epsilon]_s and [d -> #]_s separates two rules
- Counter value is number of associated empty membranes **minus one**, including the spare membrane required for future division
- Deterministic ADD sets both source continuations equal; its duplicate identical outgoing rule is stored once
- No output instruction is used. The source's extraneous unbound l-double-prime output alternative therefore plays no role, and is not silently included
- Fresh program labels, per-instruction `$1`/`$2` symbols, b1,b2,d,t,# are disjoint
- The source shares label s between skin and inner delay. We rename only the outer membrane `skin`, keep inward s-rules targeting the inner delay, and include every source s-labelled evolution/send-out rule at **both** s and skin. This conservative role split costs one extra label. It is not the source's original three-label count
- Unused source a_i output-alphabet decorations are omitted. The actual alphabet is exactly the symbols appearing in the exported rules

All of these choices are visible in `membrane_rules.jsonl`; they add no charges, cooperation, priorities, changing labels, membrane creation, or non-elementary division.

## 3. Exact source TM to three registers

### 3.1 Conventions and table

Registers L,R,T are natural numbers. ADD r q increments r then goes to q. SUB r q z decrements r and goes to q if it is positive; otherwise leaves zero unchanged and goes to z. HALT has no instruction. `virtual3.txt` and `.json` contain every instruction literally, with aliases removed.

The scanned bit is in finite control. At a TM cut, T=0, and L,R store successive symbols strictly left/right of the head, least-significant bit nearest the head. Omitted high bits are blank 0. The TM starts at control A0. A one-instruction prologue

    init_clear_T: SUB T init_clear_T tm_A0_pop0

clears arbitrary initial T before entering the simulation. This takes T+1 virtual instructions. It makes the raw positive-integer interface total on its promised domain in Section 4.

For each defined TM instruction (q,s)->(w,D,q'), let X be the half tape in movement direction D and Y the other half. All labels below are distinct for the source instruction and parity branch. The generator expands exactly this finite graph; the exported files contain no schematic rows.

### 3.2 Pop and recover quotient

At `pop0`:

    pop0: SUB X pop1 back0
    pop1: SUB X pair back1
    pair: ADD T pop0

Starting at (X_0,T)=(2Q+r,0), each full loop consumes two from X and adds one to T. After k complete loops, X=2(Q-k)+r, T=k, while the other half is unchanged. For k<Q the next two decrements are enabled; at k=Q, the final failed test selects `back0` if r=0, or one successful decrement followed by a failed test selects `back1` if r=1. The rank Q-k decreases, so the loop terminates. The exit has X=0,T=Q, with r in control.

Each parity-specific `back` loop is

    back: SUB T back_add push
    back_add: ADD X back

After j successful transfers, X=j,T=Q-j. It terminates with X=Q,T=0. There have been 3Q+(1+r)+(2Q+1)=5Q+r+2 virtual instructions in the entire pop stage.

### 3.3 Double, recover, write

For the selected parity r:

    push: SUB Y twice1 restore
    twice1: ADD T twice2
    twice2: ADD T push
    restore: SUB T restore_add write
    restore_add: ADD Y restore

If the old other half is Y_0, the first loop has Y=Y_0-k,T=2k after k iterations and rank Y_0-k. It finishes at Y=0,T=2Y_0. The second loop transfers one T to Y per iteration, preserving Y+T=2Y_0 and decreasing T. It finishes at Y=2Y_0,T=0. If w=1, `write` is one ADD Y instruction; if w=0, its edge is linked directly to the next TM cut. The next control is (q',r).

This stage takes 7Y_0+2+w instructions. Thus the complete TM macro takes exactly

    C_virtual = 5Q+r+7Y_0+w+4,

and maps the cut to X=Q,Y=2Y_0+w,T=0, scanned bit r and state q'. This is precisely the TM transition for every natural Q,Y_0 and both bits r.

All 29 cases use this graph, with the source row determining only X,Y,w,q'. The two arithmetic loops are terminating; there are no possible premature halts inside them. J1 is linked to HALT and has no simulation row. Induction gives exact simulation for every finite prefix and halting equivalence for infinite runs.

**Cut warning.** A control label alone does not identify a TM macro boundary: the pop loop revisits its first label while T>0. A TM cut requires both the listed label and T=0. The direct replay checks this condition.

## 4. Three registers to a literal two-register table

### 4.1 Representation including every raw positive input

At virtual-instruction boundaries, physical B=0 and

    A = C 2^L 3^R 5^T,  C>=1, gcd(C,30)=1.

Unique prime factorization gives this decomposition for every positive A. C remains unchanged. Virtual register primes are p_L=2,p_R=3,p_T=5. At instruction cuts A remains positive. Intermediate physical A can be zero; this is intentional.

The prologue repeatedly applies the virtual SUB T until v_5(A)=0. It terminates and leaves A=C 2^L 3^R, B=0. The TM simulation therefore starts with T=0 and exactly L=v_2(original A),R=v_3(original A), whatever its other prime factors. No external factorization is run by the loader or machine.

### 4.2 INC: multiply by a fixed prime

For a virtual ADD of register prime p, the physical table drains A one unit at a time. Each successful SUB A is followed by exactly p literal ADD B instructions, then returns to the test. After k iterations:

    A=N-k, B=pk.

The rank N-k decreases. On the first failed SUB A, A=0,B=pN. A second loop transfers B to A with one ADD A per successful SUB B. Its invariant is A+B=pN and its rank is B. On the final failed SUB B it exits to the virtual continuation at A=pN,B=0. Every operation is literally ADD/SUB.

The exact physical instruction counts are:

    ADD: 2pN
    successful SUB: (p+1)N
    failed SUB: 2
    total: (3p+1)N+2.

This multiplies the represented register by its correct prime factor, increasing its exponent by one without changing the other exponents or C.

### 4.3 SUB: divide, test remainder, restore if necessary

The physical table has p remainder-control states `rem0,...,rem(p-1)`. Each successfully decrements A and advances cyclically; crossing from p-1 back to 0 additionally performs one ADD B. At a remainder state j after k complete groups:

    A=N-pk-j, B=k, 0<=j<p.

The number of unconsumed A units decreases with every successful SUB A; the extra group ADD cannot loop by itself. Write uniquely N=pQ+r, 0<=r<p. The first failed SUB A occurs at A=0,B=Q in state r.

If r=0, the number N is divisible by p. Transfer B to A one-for-one; the invariant A+B=Q and decreasing B prove termination at A=Q,B=0. Since N>=1 and p divides N, Q>=1. Take the positive virtual SUB branch. Unique factorization says exactly that the represented exponent of p was positive and has decreased by one.

If r>0, the table enters a remainder-specific restoration loop. For each successful SUB B it executes p literal ADD A instructions. After k restoration groups, A=pk,B=Q-k. At B=0, execute exactly r further ADD A instructions and take the virtual zero branch. The result is A=pQ+r=N,B=0. Nondivisibility is equivalent to exponent zero, so the entire encoded state is restored.

There is no nondeterministic arithmetic test in this program. Remainders are bounded finite control, never an extra unbounded register. The loops terminate for every positive N, and every branch restores B=0 before continuing.

The exact counts are:

| Case | ADD | successful SUB | failed SUB | total |
|---|---:|---:|---:|---:|
| r=0 | 2Q | N+Q | 2 | N+3Q+2 |
| r>0 | N+Q | N+Q | 2 | 2N+2Q+2 |

A virtual ADD at prime p uses p+3 literal rows; a virtual SUB uses (3p^2+p+4)/2 rows, respectively 9,17,42 for p=2,3,5. The virtual table has ADD counts 74,76,145 and SUB counts 58,58,117 on L,R,T, including the scratch-clearing prologue. These counts give the exported total 8,408.

All source continuations, including HALT, occur only after the required restoration. Intermediate loops cannot halt. A physical macro boundary requires both its mapped entry label and B=0: its internal group/drain loop can revisit that label while B>0.

### 4.4 Why the verification covers unbounded input

`verify_frontend.py` reads the saved tables; it does not import the generator. For every macro it executes affine straight-line paths of the form

    input A=x+p, B=y  ->  output A=x, B=y+1

and the corresponding exits, transfer loops, and tails. The variables x,y,z are arbitrary naturals. Every tested SUB is verified either to have identically zero input, or to have nonnegative affine coefficients and constant at least 1. Thus every instruction choice on each checked path is valid for all parameter values, and every resulting affine identity is exact.

Every one of the 528 virtual and 8,408 physical instructions belongs to these checks. The invariants and decreasing ranks in Sections 3–4 compose those straight-line bodies into terminating arbitrary-length loops; this is why the proof is not finite-grid extrapolation. The checker also validates all destinations, all TM table selections, exact source bytes, and absence of aliases/unexpanded macros in the literal exports.

Additional unaccelerated interpreters test all six operation/prime shapes on 256 positive inputs each, 4,698 TM/half-tape cases through the virtual table, 261 whole TM steps through the actual physical table, and 81 arbitrary-cofactor/scratch-prologue cases. These finite tests supplement, rather than replace, the all-input proof.

## 5. Exact literal membrane translation

`membrane_rules.jsonl` is the complete finite rule table, one rule per line with fixed symbols, fixed labels and fixed outputs. `object_alphabet.txt` enumerates the complete alphabet. `frontend_metadata.json` lists exact counts. No arithmetic function is used as a membrane-rule right-hand side. There are 6,068 physical ADD and 2,340 physical SUB instructions. Hence there are 3(6,068)+7(2,340)+21=34,605 distinct rules, and 8,408+1+6,068+2(2,340)+5=19,162 symbols. The final 21 rules are shared support; the final five symbols are b1,b2,d,t,#.

Rule semantics are noncooperative object evolution, send-in, send-out, dissolution and elementary division, without polarization. Objects used by a step are those of the old configuration. A membrane has at most one structural action (send-in, send-out, divide or dissolve) in a step; evolution can coexist on other old objects. For send-in, the occupied structural slot is the receiving child boundary; using an object from its parent does not occupy the parent membrane's own boundary. Several different children may therefore receive different old skin objects in one step. Rule allocation is inclusion-maximal. The skin is never divided or dissolved. Division copies all other current contents; dissolution releases them to the parent. Every non-skin membrane here is elementary, so no non-elementary operation is needed.

Let physical register i be represented by n_i+1 elementary i-membranes. Let l be its instruction label, u=l$1,v=l$2. In the following schema q is the positive/ADD continuation and z the zero continuation. Every instance is already expanded in the JSONL file.

For ADD i q:

    l []_i -> [l]_i
    [l]_i -> [u]_i [t]_i
    [u]_i -> []_i q

For SUB i q z:

    [l -> d b_i u]_skin       and the conservative duplicate at s
    u []_i -> [u]_i
    [u]_i -> q               (dissolution)
    u []_s -> [v]_s
    [v]_s -> []_s z           and the conservative duplicate at skin

Shared rules, with i=1,2:

    [t -> epsilon]_i
    b_i []_i -> [b_i]_i
    [b_i]_i -> []_i t
    [b_i -> #]_i
    [b_i -> #]_skin           and at s
    [# -> #]_i
    d []_s -> [t]_s
    [t -> epsilon]_skin      and at s
    [d -> #]_skin             and at s
    [# -> #]_skin             and at s

There are no HALT-consuming rules. The extra role-split rules cannot act on a correctly simulated control in the wrong region. They preserve the audited source semantics on reachable configurations and keep # active in every label.

## 6. All-run membrane proof, including wrong guesses

### 6.1 Soft boundary and traps

A soft boundary for physical state (l,n_1,n_2) has:

- n_i+1 empty elementary i-membranes for i=1,2
- one empty elementary s delay membrane
- skin contents l and optionally one t

The optional t is essential: a successful SUB returns its continuation one step before a harmless skin t is erased. At the next instruction's first phase, that old t must erase by evolution and cannot compete for a structural slot. It therefore neither changes the next simulation nor accumulates. Every generated physical instruction is covered by this soft invariant.

If # ever occurs, it can never disappear globally. Its only consuming rule is #->#, present in every membrane label. Division copies it, dissolution promotes it, and no rule exports or erases it. In every later configuration at least one # evolution is applicable. Such a run cannot globally halt, even if a HALT control object also occurs.

Therefore, for soundness of halting, it suffices to classify every branch that can remain # free. The following argument uses arbitrary natural counter values, not a bounded enumeration.

### 6.2 ADD

At a boundary there is always at least one i-membrane. Maximality forces l to enter one; there is no alternative evolution for l at the skin because this l labels an ADD instruction. Optional old skin t erases. Next the chosen elementary membrane must divide, making u in one daughter and t in the other. Next u must exit as q and t must erase. All children are empty again, and exactly one extra i-membrane has been added. This takes three steps, with a clean next boundary. Choices among identical empty i-membranes only permute an indistinguishable population.

### 6.3 SUB: first two phases

First l evolves to d b_i u in skin, erasing any pre-existing t simultaneously. There are exactly three active objects.

In phase 2, every branch capable of halting must send d into the unique delay s, becoming t. Otherwise the evolution d-># is required by maximality, or is chosen. Likewise it must send b_i into one i-membrane; otherwise b_i-># occurs. These two send-ins occupy both target structural slots.

If n_i>0, there is at least one additional i-membrane. Since the delay and reserved i-membrane are busy, maximality forces u into one of the additional i-membranes. If n_i=0, no unoccupied i-membrane remains and the delay is busy, so u stays in skin. Trying to send u into the delay instead would prevent the necessary d entry and therefore forces a trap; trying to reserve the only i-membrane for u would similarly force the b_i trap. These wrong allocations are not silently ignored by the rules, but they cannot belong to a halting computation.

### 6.4 SUB: nonzero and zero completions

In phase 3, every branch capable of halting must send b_i out of its reserved membrane as t into skin; choosing its competing evolution creates #. The delay's old t erases.

If n_i>0, u is in a distinct i-membrane and must dissolve it, producing q in skin. This decreases the represented counter by one, while preserving its spare membrane. The result is the soft boundary q+t after three steps. In phase 4 t erases while q may already start its next instruction. If q is HALT, this cleanup step is necessary for actual global halting.

If n_i=0, the reserved sole i-membrane's outgoing action keeps its structural slot busy. The delay membrane is now structurally free: its t evolution does not occupy that slot. Maximality forces the still-skin u into the delay, becoming v. In phase 4 v exits as z while the skin t erases. This yields the clean zero-branch boundary after four steps, leaving the counter at zero.

Thus, modulo identical membrane choices, exactly one # free instruction outcome exists, and it is the correct deterministic counter transition. At least one such # free allocation exists in every case.

### 6.5 Halting equivalence and object bound

Iterate the preceding proof from the structural input. A globally halting run cannot contain #, and hence must follow the correct finite physical counter computation, allowing only the specified harmless pending t. There is no trap-free deadlock inside a macro. At any non-HALT boundary the next instruction has an enabled correct start; at HALT at most one cleanup of t remains. Conversely, a finite physical computation ending at HALT has a # free membrane simulation and hence a globally halting completion.

For the particular prime compiler here, every virtual-macro exit is a failed physical SUB B or the final remainder-tail ADD. Both have clean membrane exits. Thus the generated program reaches HALT with no pending t. If a whole run uses C physical instructions and Z failed physical SUBs, its correct membrane path has exactly 3C+Z steps. Each virtual instruction has exactly two failed physical SUBs, so Z=2 times the number of virtual instructions.

At every correctly simulated point there are at most three objects inside the entire system. Incorrect infinite branches have no such claimed bound. The expanded membrane population is unbounded and follows the represented physical counters.

`verify_membrane.py` independently enumerates old-object allocations, checks structural-slot disjointness and exact maximality, then performs the update. It extracts representative ADD/SUB gadgets from the actual full export and checks all maximal branches for both registers, n_1,n_2 in 0..3, with and without pending t: 128 cases. It also exhibits a wrong branch containing an inert continuation and live #, and confirms nonhalting. The general phase proof above is independent of these finite tests.

## 7. Input, universality and the Diophantine boundary

`load_input.py --A N` emits a complete sparse configuration-motif descriptor for positive N. It uses four motifs: empty label-1, empty label-2, empty delay s, and the control-bearing skin. Their supported skin-edge multiplicities are N+1,1,1. In the motif packet's positive-edge coordinates C=1+c, these are c=N,0,0. All object counts are fixed constants. This is an exact description of N+4 membranes; explicitly constructing the expanded tree costs proportional to its population. Compact description is not physical population removal.

`load_input.py --halves L R` separately computes N=2^L3^R and marks that preprocessing in its output. A simple elementary implementation uses L doublings and R triplings starting from 1; binary result length is floor(L+R log_2 3)+1. The cost is not a fixed number of bounded-degree arithmetic operations and can be exponential in the bit lengths of L,R. The supplied Python implementation may use faster exponentiation, but its work and output bit length are still explicitly external.

The source universality theorem provides an effective finite encoding of a TM program and input as the two half tapes L,R. Section 3 simulates the displayed TM exactly. Section 4 implements that simulation using the fixed literal two-counter program. Sections 5–6 implement exactly its halting behavior using the fixed membrane rules and the structural loader. This proves the theorem in Section 1. It is a transparent construction from audited data, rather than an appeal to an unaudited generic “there exists a universal two-counter program.”

Every literal membrane rule fits the separate motif-arithmetic theorem: fixed labels and symbol objects, unique skin, noncooperative evolution, communication, elementary division, and dissolution. Therefore any fixed decorated one-step schema for this frontend can use that theorem's quadratic residual construction and quartic sum of squares. A globally terminal slice must certify **no enabled rule**, including no trap loop and no pending t evolution; checking its control object alone is insufficient.

What has now been supplied is the missing literal machine/rule table and complete effective input/acceptance contract. What has not been supplied is an unbounded-time fixed-size witness decoder, a fixed-arity universal polynomial, a new witness-count bound, a 75/87-operation claim, or a generic polynomial-time overhead. The prime encoding here deliberately pays enormous time and structural-population overhead to make the frontend explicit.

## 8. Reproduction and concrete accepting example

Python 3, standard library only:

    python build_frontend.py
    python verify_frontend.py
    python verify_membrane.py
    python replay_example.py
    python load_input.py --A 64

Rebuilding deterministically emits the full literal tables. The two verification scripts read the saved tables, rather than importing the generator. Their receipts give exact coverage. No full-repository or unrelated archive is required.

For input A=64 (half tapes L=6,R=0), the TM trace reaches J1 after seven instructions. Executing the 3-counter table takes 328 virtual instructions, including the prologue. Applying the proved exact prime-macro counts gives **738,579,314,485,258,247 physical ADD/SUB instructions**, and **2,215,737,943,455,775,397 correct membrane steps**. The enormous physical/membrane microtrace is not enumerated. `replay_example.py` checks the finite virtual trace, independently follows all eight TM cuts, and reproduces these counts by the all-input formulas. This example makes the cost of the explicit prime construction unmistakable; it is not an efficiency record.

All proofs and exact-integer checks are research-level executable corroboration, not proof-assistant verification. The retained source/table boundary and the distinction between universal frontend and unbounded Diophantine arithmetization are part of the claim.

## 9. An elementary noncomputable-density corollary

Let H be the set of pairs (L,R) on which the displayed U15,2 table halts from A0, and let S be the positive raw inputs accepted by this membrane frontend. The exact all-positive-input contract gives

    S = {A>=1 : (v_2(A),v_3(A)) is in H}.

For each fixed pair, its valuation cylinder has natural density

    w_(L,R) = (1-1/2)(1-1/3)/(2^L 3^R) = 1/(3·2^L·3^R).

Indeed it consists of A=2^L3^R m with m coprime to 6. These cylinders are disjoint and their weights sum to 1. For every set of pairs, not just H, the union of its cylinders has natural density equal to the sum of its weights. To see the required passage from finite to infinite unions, truncate to 0<=L<=K and 0<=R<=J. All omitted integers are divisible by 2^(K+1) or by 3^(J+1), so their upper density is at most 2^(-K-1)+3^(-J-1). The omitted weight has the same vanishing upper bound. Each finite union has its stated density; taking arbitrarily large K,J proves existence of the full density.

In particular the membrane acceptance language has natural density

    δ = (1/3) sum_((L,R) in H) 2^(-L)3^(-R).

This real is left-computably enumerable: define the rational δ_t by summing the same weights for L,R<=t whose TM computations halt within t executed instructions. Exact finite simulation computes δ_t; the sequence is nondecreasing and tends to δ.

**δ is not computable.** Suppose a computable sequence of certified rational upper bounds u_t>=δ converges to δ. Given any pair x=(L,R), its positive rational weight w_x is known. Enumerate halting pairs and their increasing partial weight s_t (δ_t suffices). If x is enumerated, answer that it halts. Otherwise continue until u_t-s_t<w_x, which eventually occurs because both bounds converge to δ. At that point x cannot halt: its later contribution alone would force δ>=s_t+w_x>u_t. This would decide the c.e.-complete halting set H, a contradiction.

In fact δ has Turing degree **exactly 0′**. The preceding positive-weight test computes the universal halting set from arbitrarily precise oracle bounds on δ. Conversely, a halting oracle decides membership in each finite box, and the geometric tail bound computes δ to any requested precision. Consequently δ is **transcendental**: every real algebraic number is computable, by hardcoding its integer polynomial and a rational isolating interval and refining that interval. These are elementary computability consequences; no novelty claim is made.

Therefore the computable lower approximants δ_t have **no computable guaranteed convergence/error modulus**. Otherwise such a modulus would make δ computable. Finite approximants are certified lower bounds, not estimates with computable error bars. This is an elementary weighted-halting consequence of the explicit input contract; no novelty or priority claim is made.

### Explicit counting remainder, with a different computability status

Let B(N)=|S intersect {1,...,N}| be the accepted-input counting function. For q=2^L3^R, its valuation cylinder has the exact count

    floor(N/q)-floor(N/(2q))-floor(N/(3q))+floor(N/(6q),

which differs from N/(3q) by less than 4. Put K=floor(log_2 N), J=floor(log_3 N). Every pair actually occurring among 1,...,N is in the box 0<=L<=K,0<=R<=J. Summing the cylinder errors over accepted pairs in that box contributes at most 4(K+1)(J+1). The omitted density weight is less than 2/N because 2^(-K-1)<1/N and 3^(-J-1)<1/N. Consequently, for every N>=1,

    |B(N)-δN| <= 4(1+floor(log_2 N))(1+floor(log_3 N))+2.

Thus B(N)=δN+O(log^2 N), with the displayed computable uniform remainder. This does not compute δ: B itself is noncomputable, since B(N)-B(N-1) would decide membership in the universal acceptance set. It is important to distinguish this effective remainder for an uncomputable counting function from the lack of an effective error bound for the computable lower approximants δ_t.

For a fully computable counting sequence, define C(N) to count those m<=N for which the source TM on (v_2(m),v_3(m)) halts within m steps. Its membership test is a finite computation. For each fixed halting pair, all but finitely many integers in its cylinder pass that bound. Finite unions of halting cylinders therefore give liminf C(N)/N at least their total weight; taking larger finite boxes gives liminf>=δ. Since C(N)<=B(N), limsup<=δ. Hence C(N)/N tends to the same noncomputable δ. This computable rational sequence has no computable guaranteed convergence modulus, or its limit would be computable. No bounded-time membrane rule set is asserted for this auxiliary sequence.

`verify_density.py` checks finite valuation-cylinder counts and exports a few exact δ_t lower bounds. Those finite tests illustrate the corollary and are not its noncomputability proof.

### Low prefix complexity and nonrandomness

Let δ↾n denote its first n binary digits and K prefix-free Kolmogorov complexity. Then

    K(δ↾n) = O(log n).

Take the box 0<=L,R<=n+3. Its omitted mass is at most 2^(-n-4)+3^(-n-4), which is less than 2^(-n-2). Among the halting pairs in that finite box, choose one with the greatest halting time, or an empty-box sentinel if none halt. A description consists of a self-delimiting encoding of n, the chosen pair's index among (n+4)^2 possibilities plus the sentinel, and one additional bit. Its length is O(log n).

The fixed decoder runs the chosen pair to obtain its halting time, then runs every pair in the box for that long. Because the chosen pair attains the maximum, this computes the exact accepted box mass. The true δ lies between this rational mass and that mass plus the known omitted-mass bound. This interval has width less than 2^(-n), so it meets at most two length-n binary cylinders; the final bit selects the correct prefix. δ is irrational, so no dyadic-expansion ambiguity arises. The sentinel means that the exact box mass is zero.

The choice of a longest-running halting pair is **existential description data**, not a computable way to find a convergence stage. This complexity bound therefore gives no effective approximation modulus for δ.

Both liminf K(δ↾n)/n and limsup K(δ↾n)/n are zero: its constructive dimension and constructive strong dimension are both zero. It is also **not Martin-Löf random**. Directly, at length n the decoder on all indices and both final-bit choices effectively enumerates at most 2((n+4)^2+1) candidate prefixes, one of which is δ↾n. Their cylinders have total measure at most 2((n+4)^2+1)2^(-n). Choosing computably increasing n so that this is at most 2^(-k) gives a Martin-Löf test covering δ for every k. These are elementary consequences of this particular finite-box weighting, not properties asserted for arbitrary left-c.e. reals.

## 10. Explicit degree-two Diophantine outcome family

The literal frontend also gives a direct Diophantine representation of **existence of an accepting outcome at an externally fixed physical instruction count**. It does not require choosing or encoding any particular membrane birth history. This section supplies an actual quadratic polynomial family, using natural parameters for each branch's legal old/new counter values; there are no separate guard rows or positive-branch slack witnesses.

### 10.1 Fixed branches and natural coordinates

Number the 8,408 nonhalting physical controls 0,...,8407 in their exported order, with HALT=8408. The entry is 0. Expand each ADD into one semantic branch and each SUB into a positive and a zero branch. Each branch r has fixed source u_r, target v_r, an operated register, and one of the three operation types. These are literal finite integer records in `semantic_branches.json`.

There are I=6,068 ADD instructions, S=2,340 SUB instructions, and

    B = I+2S = 10,748 semantic branches.

Fix an external instruction count T>=1. At each step j introduce one natural selector e_(j,r) per branch. For each branch introduce one natural base x_(j,r,i) per counter i, **except that a zero SUB branch has no base for its tested counter**. Thus there are B selectors and 2B-S bases per step, with no global counter or control witnesses.

For every branch, define its old and new counter expressions as follows:

| Counter role | Old value | New value |
|---|---|---|
| Unaffected counter | x | x |
| ADD, operated counter | x | x+e |
| Positive SUB, tested counter | x+e | x |
| Zero SUB, tested counter | 0 | 0; no base coordinate |

These are affine expressions with nonnegative coefficients. When e=1 they parametrize exactly that branch's legal natural old/new values. When e=0 and all its retained bases are zero, both values are zero. It is essential that the ADD/positive-SUB offset is e rather than the constant 1, so inactive branches contribute nothing.

Define the following linear expressions, not additional variables:

    E_j = sum_r e_(j,r)
    U_j = sum_r u_r e_(j,r),   V_j = sum_r v_r e_(j,r)
    OLD_(j,i) = sum_r old_(j,r,i)
    NEW_(j,i) = sum_r new_(j,r,i).

### 10.2 The actual quadratic polynomial

Use these four affine rows at each time j:

    E_j-1
    U_j-(0 if j=0 else V_(j-1))
    OLD_(j,A)-(A if j=0 else NEW_(j-1,A))
    OLD_(j,B)-(0 if j=0 else NEW_(j-1,B)).

Here the un-subscripted A is the free positive raw-input parameter. To use a natural parameter that may be zero, substitute A=1+n; degree and witness count do not change. Add the final affine row V_(T-1)-8408.

For each step and branch add this quadratic product:

    (sum_(k != r) e_(j,k)) · (e_(j,r)+sum_(retained i) x_(j,r,i)).

Let P_T(A,w) be the sum of the squares of the listed affine rows, plus the sum of the listed products. This is one integer polynomial of degree at most two. Every summand is nonnegative for **every natural assignment**, before any equation is assumed. In particular the first factor is the sum of the other selectors, not the expression 1-e_(j,r), which could be negative off the one-hot equations and allow cancellation of an invalid squared residual.

`quadratic_outcome.py` emits every individual square and product for any requested fixed T. Shared intermediate forms have complete finite coefficient lists and are only linear arithmetic expressions. `quadratic_schema_T1.json` is the fully instantiated representation at T=1, with all **five affine squares** and **10,748 products** explicitly listed. No schema loop, exponentiation, execution predicate or hidden witness remains in that file. Expanding its squares/products into a dense monomial list is unnecessary and would be much larger.

### 10.3 Exact soundness, completeness and unique fibers

If P_T=0 over natural witnesses, every affine row and product is zero. E_j=1 makes exactly one selector equal to one. For an inactive branch, the sum of its other selectors is one, so its product forces the sum of all retained bases to zero. Naturalness forces every such base to zero; the omitted zero-branch tested coordinate is already the constant zero. Thus every inactive branch contributes zero to OLD and NEW.

Only the active branch remains. Its source is the required current control, and the two counter interface equations fix its old counter values. An active ADD has new=old+1 on the operated register. An active positive SUB has old=x+1>=1 and new=x=old-1. An active zero SUB has old=new=0 on its tested register. Unaffected values remain unchanged. Hence each selected branch is exactly a legal instruction of the deterministic literal program. All new counters are natural by construction, including at the final step, where no additional output-counter witnesses are necessary.

The strengthened gate also makes this proof valid over **nonnegative real witnesses**, with the same fixed natural input. If E_j=1 and two selectors were positive, the product for either would have both factors positive. Therefore the selectors are one-hot even without an integrality assumption. Inactive bases again vanish, and a natural old counter fixes the active base to that counter or that counter minus one, propagating integrality from the initial counters. Thus the nonnegative-real zero fiber is exactly the natural zero fiber. Unrestricted real witnesses, which may have negative coordinates, are not covered.

The terminal equation forces HALT after exactly T instructions. HALT has no semantic outgoing branch, so an earlier halt cannot be padded into a longer certificate. Conversely, a computation that first halts at step T supplies a zero: select its branch at each step; give each unaffected/ADD base the old counter value, each positive SUB tested base old minus one, and every inactive base zero.

For fixed A and T there is therefore **either no natural witness tuple or exactly one**. The current state and old counters determine the unique instruction and the unique applicable SUB arm. On that arm every retained base is fixed; all inactive bases are zero. Induction determines every coordinate. This is uniqueness of the counter-outcome certificate, not uniqueness of the physical choices among identical membranes.

By Sections 4–6, a zero certifies that the structural-input membrane system has some globally halting run, and every globally halting run gives the program's exact halting length and this canonical certificate. This is an **outcome-existence projection**. It does not validate an arbitrary supplied membrane trace. A trace containing # cannot be certified merely by pointing to its HALT object; the counter terminal test is justified by the separately proved existential-halting simulation.

### 10.4 Exact ledger, time units and remaining boundary

For T>=1 the preferred construction has exactly

    (3B-S)T = 29,904T natural witnesses
    4T+1 affine squares
    BT = 10,748T nonnegative quadratic products
    degree at most 2.

The input A is a free parameter, not counted among existential witnesses. Control constants are in 0..8408; all other affine coefficients are 0 or ±1 before expansion. The initial-control and both initial-counter equations are included in the four rows at time zero. At T=0 the entry is not HALT, so a nonzero constant polynomial suffices.

**T counts literal physical ADD/SUB instructions, not membrane steps.** For an accepting certificate let Z be the sum of its selectors for zero SUB arms. The correct membrane run has M=3T+Z steps, because the generated program's HALT boundary is clean. If the membrane duration M is to be prescribed as another free parameter, adding the one affine square (M-3T-Z)^2 gives that extra condition without any new witnesses or a degree increase. This optional timing row does not turn the certificate into an arbitrary-history verifier.

For comparison, the superseded separate-guard construction had 34,584T witnesses and 4,684T+1 squares, with the same product count and degree. Direct parametrization of legal branch domains removes those guard rows and extra slacks.

The generic compiler also supports any fixed register count d. With I ADDs, S SUBs and B=I+2S branches, the same proof gives

    ((d+1)B-S)T natural witnesses,
    (d+2)T+1 affine squares,
    BT nonnegative quadratic products.

This formula is a finite compiler ledger; no new generic register-machine universality theorem is invoked.

`verify_quadratic.py` independently evaluates the exported arithmetic, reconstructs every semantic branch, checks full-table prefixes and rejects their non-HALT endpoint, verifies small accepting fixtures, mutates all their coordinates, and checks off-one-hot nonnegativity. It also fully expands the small fixture polynomials and compares their integer-monomial evaluations. These tests supplement the all-input proof. The full A=64 certificate would use its enormous physical length T=738,579,314,485,258,247; it is not materialized or presented as compact.

As T varies, this is a computably generated family of different-arity polynomials. Representing unknown unbounded T in one fixed finite witness tuple remains unpaid. The result is not a fixed-arity universal equation, a singlefold MRDP representation, or a small-operation Diophantine record. It is a fully explicit degree-two bounded-time outcome certificate for the literal universal frontend.
