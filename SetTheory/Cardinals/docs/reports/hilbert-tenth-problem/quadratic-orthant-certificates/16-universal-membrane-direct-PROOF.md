# A direct three-register membrane frontend with an affine input loader

Research packet, 2 October 2026. This is an explicit instantiation from an audited universal Turing-machine table, not a small-machine record, a new generic register-machine universality theorem, or a fixed-arity universal Diophantine equation.

## 1. Result

The packet supplies one fixed literal 528-instruction three-register program and one fixed polarizationless, noncooperative active-membrane rule set. The machine accepts two natural half-tape integers L,R through an affine structural loader. Its exact static counts are:

- 295 ADD and 233 SUB instructions
- 761 semantic instruction branches
- 2,544 membrane rules, 1,296 object symbols and five membrane labels
- Initial expanded population L+R+5, including the skin

**Theorem.** For every L,R>=0, the loaded membrane system has a globally halting maximally parallel run if and only if the displayed Neary–Woods U15,2 machine halts from state A, scanned symbol 0, left half tape L and right half tape R. Thus this fixed-rule structural-input acceptor has a c.e.-complete halting relation on pairs of natural integers.

For every fixed external register-instruction horizon h, an explicit integer polynomial of degree at most two represents this outcome with exactly

    2,811h natural witness coordinates,
    5h+1 affine squares,
    761h nonnegative quadratic products.

For fixed natural input and h, the zero fiber is empty or a singleton, even if witnesses are allowed to range over the nonnegative reals. Unrestricted real witnesses, negative coordinates, and a fixed-arity unbounded-time encoding are outside the result.

The accepting example L=6,R=0 is fully executable here: seven source TM steps, 328 register instructions, 1,013 membrane steps, and at most 30 membranes and three objects on its correct run. Its complete accepting quadratic witness occupies 922,008 declared coordinate slots, of which 922 are nonzero. All 1,641 squared rows and 249,608 products are evaluated exactly to zero.

## 2. Source table, input and credit

The source is Table 16 of T. Neary and D. Woods, *Four Small Universal Turing Machines*, Fundamenta Informaticae 91(1), 123–144 (2009): https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf . The literal binary serialization is https://github.com/Iijil1/MTGPrograms/blob/main/Examples/UniversalTM15x2.tm.txt and is included as `source/UniversalTM15x2.tm.txt`, SHA-256

    ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae.

The primary table has u15,b -> b,R,u14, and its unique undefined entry is u10,b. With c=0,b=1 and u1=A,...,u15=O, this is the undefined state-symbol pair J1. The conflicting later halting prose saying u10,c is not used. The primary source and the two-half-tape input convention were independently checked in the preceding research; the reference proof is retained in `source/WATERFALL-FRONTEND-PROOF.md`. No third-party PDF or image is redistributed here.

The scanned symbol is stored in finite control. L,R are natural integers whose binary digits, nearest to the head first, are read least-significant bit first. Unrepresented high digits are blank 0. The universal initial control is A0. The paper's finite effective encoding of a source program and its input can use both half tapes; varying only one side would not establish this universality interface.

The membrane construction adapts the explicit gadgets of Alhazov, Freund and Riscos-Núñez, *Membrane division, restricted membrane creation and object complexity in P systems*, IJCM 83(7), 529–547 (2006), Theorem 4.1, DOI 10.1080/00207160601065314. Primary institutional text: https://idus.us.es/bitstreams/dcac15aa-404e-4102-88e2-08ec23b7df8a/download . That theorem states a two-register zero-input generator compiler. The arbitrary structural-input and three-register adaptations below are proved directly; they are not attributed to its statement.

## 3. Literal simulation using L,R and scratch T

`virtual3.txt` and `virtual3.json` contain every ADD/SUB instruction with all aliases resolved. ADD r q increments register r and continues at q. SUB r q z decrements and chooses q when positive; at zero it preserves zero and chooses z. HALT has no row. The scratch register is named T in these files; the external instruction horizon is denoted h in this proof.

The initial instruction clears T:

    init_clear_T: SUB T init_clear_T tm_A0_pop0.

Our loader already sets T=0, so this is one failed SUB. It is retained to use exactly the already audited 528-row program. At all subsequent TM cuts T=0.

For a defined transition (q,s)->(w,D,q'), let X be the half tape in direction D and Y the other half. Write X=2Q+r, with r in {0,1}. The following fixed graph is separately instantiated at each of the 29 source rows.

Pop pairs and remember parity:

    pop0: SUB X pop1 back0
    pop1: SUB X pair back1
    pair: ADD T pop0.

After k complete pair loops, X=2(Q-k)+r,T=k. The nonnegative rank Q-k decreases. At k=Q the first failed test chooses the parity branch, leaving X=0,T=Q. Transfer T back to X using `SUB T ...` followed by `ADD X ...`, ending at X=Q,T=0. This entire stage takes 5Q+r+2 instructions.

In the parity branch, drain Y to T, adding two to T per successful decrement of Y. After k iterations Y=Y_old-k,T=2k. The rank Y_old-k decreases; the exit is Y=0,T=2Y_old. Transfer T to Y one-for-one, preserving Y+T=2Y_old and decreasing T. Finally add one to Y if w=1. This costs 7Y_old+2+w instructions and ends at

    X=Q, Y=2Y_old+w, T=0, control=(q',r).

The complete exact instruction count for one TM step is

    5Q+r+7Y_old+w+4.

All loops terminate for every natural input. The only terminal control is J1. These identities prove exact TM simulation by induction, without an appeal to a separate universal counter-machine existence theorem.

A label alone is not a TM cut: a pop loop revisits its entry while scratch T is positive. A TM cut requires the appropriate control label **and T=0**. The checker enforces that condition.

`verify_direct.py` checks 437 affine paths on arbitrary nonnegative symbolic inputs, covering every one of the 528 literal rows. Every tested SUB on a path is either identically zero or has nonnegative affine coefficients with constant at least one. The displayed loop invariants and ranks extend those body checks to all iteration counts. Additional literal replay covers 4,698 TM macro cases. Finite tests supplement, rather than replace, the all-input proof.

## 4. Direct fixed-register membrane compiler

### 4.1 Model and structural input

The labels are skin,1,2,3,s. All non-skin membranes are elementary; skin is unique and never divided or dissolved. Rules are noncooperative object evolution, send-in, send-out, elementary division and dissolution, with no polarization, priorities, cooperative left sides, changing labels or membrane creation.

Every rule selection consumes only old objects. A membrane boundary admits at most one send-in, send-out, division or dissolution in a step. For send-in this is the receiving child's boundary, so distinct children can receive different old skin objects simultaneously. Evolution of other objects does not occupy the structural slot. Selections are inclusion-maximal, followed by the structural update.

The input loader places the fixed control object `init_clear_T` in skin, with L+1 empty label-1 membranes, R+1 empty label-2 membranes, one empty label-3 membrane and one empty s delay membrane. The represented register value is its population **minus one**. The spare membrane is indispensable for later increments by division.

`load_input.py L R` produces an exact five-motif shared-tree description. In positive-edge coordinates C=1+c its four skin-edge variables are c=L,R,0,0. Only the first two vary. The expanded tree has L+R+5 membranes, and explicitly materializing it costs proportional to that population; compact loading does not erase this physical cost. Unlike the separate prime-coded four-label variant, this direct loader does not compute variable powers.

### 4.2 Literal rule schema

For each instruction l use fresh u=l$1; for a SUB instruction also use fresh v=l$2. For ADD i q, the three rules are

    l []_i -> [l]_i
    [l]_i -> [u]_i [t]_i
    [u]_i -> []_i q.

For SUB i q z, the seven rules are

    [l -> d b_i u]_skin, [l -> d b_i u]_s
    u []_i -> [u]_i
    [u]_i -> q                   (dissolution)
    u []_s -> [v]_s
    [v]_s -> []_s z, [v]_skin -> []_skin z.

Shared support, for each i=1,2,3:

    [t -> epsilon]_i
    b_i []_i -> [b_i]_i
    [b_i]_i -> []_i t
    [b_i -> #]_i, [b_i -> #]_skin, [b_i -> #]_s
    [# -> #]_i.

Additionally:

    d []_s -> [t]_s
    [t -> epsilon]_skin, [t -> epsilon]_s
    [d -> #]_skin, [d -> #]_s
    [# -> #]_skin, [# -> #]_s.

These are seven shared rules per register and seven more, so r registers use 7r+7 support rules. At r=3 this is 28. The literal JSONL export includes every instance, with consecutive IDs and no schematic variables.

The role split conservatively duplicates the source's s-labelled evolution/send-out rules at both inner s and unique skin; inward s-rules still target the delay. This adds one label compared with reusing the same label for skin and delay. The source's missing comma between t erasure and d trapping is explicitly read as two rules. No output instruction is used, so its unbound extra output continuation is absent. Deterministic ADD uses its one continuation; identical source alternatives are deduplicated. These choices add no stronger primitive.

### 4.3 All-run correctness, for any fixed register count

A soft boundary has the current instruction object l, optionally one t in skin, one empty delay, and n_i+1 empty membranes for every counter. The optional t always erases during the next instruction's first phase and occupies no structural resource.

ADD must enter one i-membrane, divide it in the next step, then export q while the other daughter's t erases. This takes three steps, adds exactly one membrane, and returns a clean boundary.

For SUB, l first becomes d b_i u, erasing any old t simultaneously. In the next step, a branch capable of halting must send d into the delay and b_i into an i-membrane. Otherwise an enabled trap evolution of the unconsumed d or b_i makes #. These send-ins reserve both target slots. If n_i>0, at least one further i-membrane remains, and maximality forces u into one of them. At n_i=0, no such slot remains and u stays in skin.

In phase three, a potentially halting branch must export b_i as skin t, rather than choose its competing trap evolution. The delay's old t erases. If n_i>0, the distinct membrane holding u dissolves and returns q, decreasing the counter by one. The result after three steps is the soft boundary q+t. If n_i=0, the sole i-membrane remains structurally occupied by its outgoing b_i. The delay is structurally free even while t evolves, so u must enter it as v. In phase four v exits as z and skin t erases, giving the clean zero boundary.

This argument depends only on the selected register and the one delay. Every other counter population is untouched and empty. Hence it works verbatim for three or any other fixed finite number of registers. It proves this particular three-register compilation directly.

If # ever occurs it remains somewhere forever: its only consuming rule is #->#, available in every label; division copies it and dissolution promotes it. No rule erases or exports it. A trap-bearing run cannot globally halt even if a HALT object is also present.

Thus every globally halting run must follow the exact deterministic register computation, modulo choices between identical membranes, and every halting register computation has a correct trap-free membrane run. There is no trap-free deadlock inside a gadget. A pending t is the only possible extra cleanup at an instruction boundary. Correct runs contain at most three objects simultaneously.

A generic successful SUB at the very end would need one final t-erasure step. In this literal program the **only** edge to HALT is

    tm_I1_1_write: ADD R HALT.

Consequently every actual accepting boundary is clean. A run of C register instructions with Z failed SUBs takes exactly M=3C+Z membrane steps. This is a timing statement about this literal program, not a claim that C equals membrane time.

### 4.4 Exact static ledger

With I=295,S=233 and 28 shared rules:

    rules = 3I+7S+28 = 2,544.

The alphabet consists of 528 instruction symbols plus HALT, one ADD auxiliary per ADD, two SUB auxiliaries per SUB, and b1,b2,b3,d,t,#:

    symbols = 528+1+295+2(233)+6 = 1,296.

The five rule-type counts are: 487 evolution, 765 inward communication, 764 outward communication, 295 division and 233 dissolution. All five labels have a # loop. No rule consumes HALT.

## 5. Quadratic outcome certificates by branch parametrization

### 5.1 Variables and polynomial

Number nonhalting controls 0,...,527, with HALT=528 and entry=0. There are B=I+2S=761 semantic branches. At each of h externally fixed register-instruction steps, give every branch a natural selector e and a natural base for each of its three registers, except omit the tested base of a zero SUB branch.

For an unaffected register define old=new=x. For the operated register define:

- ADD: old=x, new=x+e
- Positive SUB: old=x+e, new=x
- Zero SUB: old=new=0, with no base coordinate

Let E_j be the sum of selectors, U_j and V_j the selected source and target control linear forms, and OLD_(j,i),NEW_(j,i) the sums of all branch old/new expressions for register i. These are arithmetic expressions, not witnesses.

At each step use the five affine rows E_j-1, the source-control interface U_j-(entry if j=0 else V_(j-1)), and the three counter interfaces OLD_(j,i)-(input_i if j=0 else NEW_(j-1,i)). Initial inputs are exactly L,R,0. Add one final row V_(h-1)-528. For each branch and step add the product

    (sum of OTHER selectors) · (its own selector + sum of its retained bases).

The polynomial P_h(L,R,w) is the sum of all affine-row squares and all these products. Its coefficients are integers, its degree is at most two, and every summand is nonnegative on the entire nonnegative orthant. There are no separate guard equations or slack variables.

`quadratic_schema_T1.json` literally lists all six squares and 761 products at h=1. Shared linear forms have complete coefficient lists and no added witness coordinates. `build_quadratic.py --steps h` generates the complete analogous file for any fixed h.

### 5.2 Exact zero set and uniqueness

Over natural witnesses, E_j=1 selects exactly one branch. The product for an inactive branch then forces all its nonnegative bases to zero, so it contributes nothing to any interface. The active branch's old values equal the prescribed current registers. Its affine parametrization gives precisely the ADD, positive-SUB or zero-SUB relation. The control interface links exactly consecutive instruction labels.

The strengthened gate also forces one-hot selectors over **nonnegative real** witnesses: if two selectors were positive while their sum was one, the product for either would be strictly positive. Inactive bases therefore vanish over the reals too. Starting from natural L,R,0, each active base is the old natural counter value or that value minus one. Hence all active bases are integers, by induction. The nonnegative-real zero set is exactly the natural zero set for these inputs.

The terminal row means the register program halts exactly at step h. Earlier halting cannot be padded because HALT has no outgoing branch. Conversely, a halting computation supplies selectors and bases uniquely. Thus for fixed L,R,h the zero fiber is empty or a singleton. Unrestricted real assignments may violate summand nonnegativity and are not covered.

The membrane equivalence in Section 4 turns this into an outcome-existence representation for the membrane acceptor. It does not certify an arbitrary supplied membrane history, and never treats the mere presence of HALT alongside a trap as acceptance.

### 5.3 Exact counts and time contract

There are 3B-S=2,050 retained bases and B=761 selectors per step:

    witnesses = (4B-S)h = 2,811h
    affine squares = 5h+1
    products = Bh = 761h.

The input parameters L,R are not existential witnesses. h counts three-register instructions. It is not the number of TM steps or membrane steps. If a membrane duration M is also prescribed, let Z be the linear sum of selected zero-SUB branches; add the single affine square (M-3h-Z)^2. No new witness coordinate or higher degree is needed, because this program's HALT edge is clean.

At h=0 no halt is possible from the nonhalting entry; a nonzero constant polynomial suffices. As h varies, the arity grows. No fixed-arity representation of unbounded h, singlefold MRDP result, or small-operation universal-polynomial record is claimed.

## 6. Completely replayed accepting example

For L=6,R=0, the source TM cuts are

    A0:(6,0), B0:(12,0), C0:(25,0), G1:(12,0),
    G0:(6,1), H0:(3,2), I1:(1,5), J1:(0,11).

The literal program executes 328 instructions, including its initial scratch-clear zero test. Exactly 29 SUBs take their zero arms: one in the prologue and four per TM macro. The accepting membrane run therefore takes 3(328)+29=1,013 steps. Its initial population is 11, maximum population is 30, and final counters are L=0,R=11,T=0. Its final total population is 16. At most three objects coexist on the correct path.

`accepting_counter_trace.json` records all 328 register transitions. `accepting_membrane_trace.json` records every membrane configuration, using exact counts of identical elementary leaves rather than names for individual membranes. `verify_membrane.py` checks old-object resource use and inclusion maximality by enumerating all possible rule allocations at each microstep, confirms the unique trap-free successor, and checks actual final quiescence. The same verifier tests 324 small all-branch gadgets and the HALT-plus-live-trap obstruction.

The exact full-horizon quadratic ledger is

    922,008 natural coordinate slots,
    1,641 affine squares,
    249,608 quadratic products.

`accepting_quadratic_witness.json` stores its 922 nonzero coordinates; every omitted coordinate among the declared 922,008 is explicitly zero. This sparse serialization does **not** reduce the witness arity. `verify_accepting_quadratic.py` reads that saved witness and evaluates every square and product exactly to zero, using a streaming expansion of the fixed forms. It additionally constructs and evaluates all 328 complete one-step arithmetic chunks. The large full unrolled JSON can be regenerated with `build_quadratic.py --steps 328`; it need not be stored to check the supplied witness.

## 7. Reproduction and limits

Python 3 standard library, from this directory:

    python build_direct.py
    python verify_direct.py
    python build_quadratic.py --steps 1
    python make_accepting_witness.py
    python verify_accepting_quadratic.py
    python verify_membrane.py
    python load_input.py 6 0

The all-input proofs use exact loop invariants, finite source data, maximality and nonnegative arithmetic. The finite replays are executable corroboration, not proof-assistant verification or a substitute for universality of the cited TM table.

This five-label, two-parameter affine-input variant is distinct from the four-label prime-coded one-parameter variant. It avoids variable exponentiation and is much smaller and faster on the displayed example, while using one more label and a different input interface. The prime variant's noncomputable natural-density results concern its valuation-based set of positive integers; they are not asserted for an unweighted two-dimensional counting of the present halting relation.

The local rules also fit the separate decorated-motif polynomial theorem: unique skin, fixed labels, symbol objects, elementary division and dissolution. The direct outcome polynomial above uses the register projection and should not be confused with that theorem's certificate for an arbitrary specified membrane step or trace. Unknown unbounded time remains an explicit open interface in both approaches.
