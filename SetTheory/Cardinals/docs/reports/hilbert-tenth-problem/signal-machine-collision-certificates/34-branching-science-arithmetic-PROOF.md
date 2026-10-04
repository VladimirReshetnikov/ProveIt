# Unique positive-integer bounded-horizon certificates for the five-signal counter compiler

4 October 2026. This separate packet leaves the frozen physical Report 64 unchanged. Its arithmetic theorem is independent of the physical implementation. The final transport corollary uses Report 64's fixed ordered-section compiler, whose independent physical audit was pending when this packet was prepared.

## 1. The exact claim and its limit

Fix a finite deterministic two-counter program M with one designated halt state H and fixed initial control state q_0. Its nonhalting instructions are increments with specified next states, or zero-test/positive-decrement instructions with specified zero and positive next states. For a horizon T>=1, the construction below produces an explicit integer polynomial

    P_(M,T)(A,B; W),

where A,B are positive integer inputs encoding the native initial counters a=A-1, b=B-1. The witness tuple W consists only of positive integers. Let E be the number of transition edges after splitting each conditional into its zero and positive edges and adding one absorbing halt edge. Let Z be the number of zero-test edges.

**Theorem.** The program reaches H in at most T transitions from (q_0,A-1,B-1) if and only if P_(M,T)(A,B;W)=0 has a positive-integer witness. If a witness exists, it is unique. The exact ledger is

    positive witness variables: T(E+2),
    native positive input variables: 2,
    residual equations before bundling: T(E+Z+4)+1,
    final equations: 1,
    total degree of the final polynomial: exactly 4.

A first-halt-exactly-T variant has the same witnesses and degree and one additional residual equation. The T=0 case is stated separately in §7.

**The horizon indexes a polynomial family.** T is not a free variable in a single fixed-arity polynomial. As T changes, the number of witnesses and equations changes. Taking the union over all T gives the usual unbounded halting relation at the level of this family, but this packet does not turn that union into one fixed polynomial representation. No packing, Pell, exponentiation, MRDP, or fixed-arity unbounded-halting module is supplied or silently assumed.

The positive inputs are native counter values shifted by one. They are not arbitrary physical coordinates; the exponential geometric encoding is used separately in §8. This is a transparent finite-trace certificate and resource ledger, with no novelty or optimized-variable-count claim.

## 2. Fixed transition data

Give every control state a distinct integer code. State codes are fixed polynomial coefficients, not witnesses. Let the edge set be e=1,...,E. Each edge has fixed data

    u_e = source state code,
    v_e = target state code,
    d_e in {-1,0,1} = change to counter A,
    f_e in {-1,0,1} = change to counter B.

Use exactly one edge for each increment instruction. For each conditional instruction use exactly two edges:

- its zero edge has both counter changes zero and a designated zero test on the tested counter
- its positive edge subtracts one from the tested counter and changes the other counter by zero

The zero and positive targets may coincide; the guard conditions still distinguish the edges. Do not add duplicate copies of an edge: witnesses name individual edges, so gratuitous duplicate enabled edges would destroy witness uniqueness.

Add exactly one absorbing halt edge h with u_h=v_h=H and d_h=f_h=0. This is only virtual padding of a terminated native computation. It does not purport to be the post-halt physical dynamics of the escape-to-right convention in Report 64.

Let E_A0 and E_B0 be the sets of A-zero and B-zero edges, with disjoint union E_0 and |E_0|=Z. Every control state has precisely the outgoing edge structure described above. Thus a native configuration has one enabled edge: an increment, the uniquely correct branch of its conditional, or the halt loop.

If the program has I increment states and C conditional states, besides its one halt state, then

    E=I+2C+1,   Z=C.                           (1)

No simulation run is needed to extract this finite instruction data.

## 3. Positive witnesses and equations

For t=0,...,T-1 and e=1,...,E introduce a positive integer w_(t,e) and abbreviate

    s_(t,e)=w_(t,e)-1.

For each t=1,...,T introduce positive integer counters A_t,B_t. These are the only other witnesses. Set

    A_0=A, B_0=B

as input-variable abbreviations, not extra witnesses. There are TE+2T=T(E+2) positive witnesses.

### 3.1 Binary selectors and one edge per step

For every t,e include

    S_(t,e)=(w_(t,e)-1)(w_(t,e)-2)=0.         (2)

Since w is an integer, it is 1 or 2, hence s is 0 or 1. For every t include

    O_t=sum_e s_(t,e)-1=0.                    (3)

Exactly one edge is selected at each step. Inactive edges have w=1, so they contribute no free or nonunique padding witnesses.

### 3.2 Exact counter updates

For each t=0,...,T-1 include

    U_t=A_(t+1)-A_t-sum_e d_e s_(t,e)=0,
    V_t=B_(t+1)-B_t-sum_e f_e s_(t,e)=0.      (4)

These are affine equations. In particular, when the selected edge decrements A, it forces A_(t+1)=A_t-1. Because A_(t+1) must be positive, A_t>=2, meaning the unshifted native counter is positive. Thus a positive-decrement guard requires no extra witness or residual. The identical observation applies to B.

This argument uses one-hot selection essentially. A sum of several edge displacements could conceal an inadmissible decrement, but (2)–(3) preclude that situation.

### 3.3 Zero guards

For each t and e in E_A0 include

    Z_(t,e)=s_(t,e)(A_t-1)=0.                 (5A)

For e in E_B0 use

    Z_(t,e)=s_(t,e)(B_t-1)=0.                 (5B)

Only a selected zero edge constrains the relevant counter; it forces the native counter to be zero. The residual is quadratic, and it uses no new variable.

### 3.4 Control consistency and final halt

Include the initial-source equation

    C_initial=sum_e u_e s_(0,e)-q_0=0.       (6)

For t=0,...,T-2 include

    C_t=sum_e v_e s_(t,e)-sum_e u_e s_(t+1,e)=0.       (7)

Finally include

    C_final=sum_e v_e s_(T-1,e)-H=0.          (8)

Distinct state codes and one-hot selection mean these equations compare actual state codes, not averages of codes. Equation (7) sets the next selected source equal to the previous selected target. There are 1+(T-1)+1=T+1 control equations, including when T=1.

## 4. Correctness and unique witnesses

### 4.1 From a halted computation to witnesses

Suppose the program first reaches H after k<=T transitions. Follow its unique deterministic edge sequence for k steps and then use the unique absorbing edge h for the remaining T-k steps. If k=0, every selected edge is h.

Set w_(t,e)=2 on the selected edge and 1 on every other edge. Set A_t and B_t to the two native counter values after t padded steps, plus one. They are positive. Equations (2)–(3) hold by construction, (4) is exactly the native counter update, (5) holds on zero edges, and (6)–(8) express the actual padded control sequence. Thus all residuals vanish.

### 4.2 From witnesses to a genuine halted computation

Equations (2)–(3) select a unique edge e_t at each t. Equation (6) gives its first source q_0; the linking equations give a control-consistent path. Equation (4) performs the exact counter changes.

If e_t is a zero edge, (5) forces the tested native counter to be zero. If it is a decrement edge, positivity of the next shifted counter forces its entering native counter to be positive. Increment and halt edges are unconditionally valid. Therefore every selected edge is an enabled transition of the padded native program. The selected path starts at the required configuration and ends at H by (8). Removing its virtual halt-loop suffix shows the original program reaches H within T transitions.

### 4.3 Uniqueness

At an increment state there is one edge. At a conditional state, shifted tested counter 1 permits its zero edge and makes a decrement violate next-counter positivity; shifted counter >=2 rules out the zero edge and permits exactly its decrement edge. At H there is one padding edge. Starting from the fixed inputs, induction therefore fixes every selected edge and every next pair of counters uniquely. Each selector is then uniquely w=2 or w=1. Hence the full positive-integer witness tuple, including all inactive selectors, is unique.

This is uniqueness of the native trace certificate for fixed M,T,A,B. It is not a finite-fold or single-fold claim for an unbounded-horizon fixed-arity Diophantine representation, since no such representation has been constructed here.

## 5. One quartic equation and the exact ledger

Let R be the list of residual polynomials (2)–(8), and define explicitly

    P_(M,T)=sum_(r in R) r^2.                 (9)

All coefficients are integers. Over integer witnesses a sum of squares vanishes if and only if every residual vanishes. Thus §4 proves the theorem for the single polynomial equation P_(M,T)=0.

The ledger is

| Residual group | Count | Degree before squaring |
|---|---:|---:|
| Selector equations (2) | TE | 2 |
| One-hot equations (3) | T | 1 |
| Two counter updates (4) | 2T | 1 |
| Zero guards (5) | TZ | 2 |
| Initial, linking, final control (6)–(8) | T+1 | 1 |
| Total | T(E+Z+4)+1 | at most 2 |

There are TE selector witnesses and 2T counter witnesses, no state witnesses, no sign witnesses, no unused padding variables, and no hidden existential bounds. The domain restriction is simply that A,B and all witness variables are positive integers.

Squaring makes the total degree at most 4, including A,B as variables. It is exactly 4 for T>=1: E>=1 because of h, and each squared selector residual contributes the pure fourth power w_(t,e)^4 with coefficient 1. No other residual contributes a negative pure fourth-degree coefficient that could cancel it. In fact the other residuals are at most linear in any one selector, so their squares contain no fourth power of that selector.

Using (1), the alternative ledger is

    witnesses = T(I+2C+3),
    residuals = T(I+3C+5)+1,
    total variables including native inputs = 2+T(I+2C+3).         (10)

These counts describe the displayed construction and are not claimed to be minimal. A sum-of-squares presentation itself specifies an integer polynomial completely; expanding its monomials is unnecessary for the theorem.

## 6. First halt exactly at horizon T

For T>=1, add the single linear residual

    H_early=sum_(t=0)^(T-1) s_(t,h)=0.        (11)

Every selector is nonnegative, so this says that no padded halt edge is selected before the final arrival. With the final-control equation unchanged, the selected path must arrive at H for the first time exactly at transition T. Conversely, any first-halt-at-T trace has no selected halt edge and satisfies (11).

Define

    P_exact_(M,T)=P_(M,T)+H_early^2.          (12)

The same unique witness property holds. The witness count and degree remain T(E+2) and 4; the residual count becomes T(E+Z+4)+2. This does not require T separate early-halt equations. The nonnegativity already established by (2) is why their sum suffices.

If q_0=H and T>=1, the by-horizon version has its unique all-halt-loop witness, while the first-halt-at-T version has none, as required.

## 7. Horizon zero and dependence on parameters

For T=0 there are no transition selectors or next counters. Use

    P_(M,0)=(q_0-H)^2.

There are zero witnesses, and its empty tuple is a solution exactly when the initial control state is already H. This is also the first-halt-at-zero convention. The polynomial is constant, so the quartic and positive-T residual ledgers are explicitly not applied to this case.

For fixed M, the construction is an effective sequence of finite integer polynomials indexed by T. Its coefficients use only the fixed transition data and integer arithmetic. The speed/rule table of the physical compiler in Report 64 remains the same for all these horizons; changing T changes only the certificate's size.

The statement

    the program halts iff some member of this family has a witness

is true by finite-time halting. It is not a single fixed-arity polynomial formula with T supplied as one more input. An unbounded packing construction would have to encode the entire variable-length trace into finitely many integers, verify all its entries and transitions, and pay for those arithmetic modules. None of those costs is included in (10), and none is claimed solved.

## 8. Exact transport to the frozen physical compiler

Report 64 constructs, for this same fixed program M, one finite rational-speed number-preserving signal machine with exactly five live signals and instruction sections

    L=0, X=x, Y=y, R=D,

plus a speed +1 instruction messenger at L. For positive input A,B choose native counter values a=A-1,b=B-1 and initialize

    x=D(1/20+(1/10)2^(-(A-1))),
    y=D(19/20-(1/10)2^(-(B-1))).             (13)

A positive rational D yields rational initial coordinates. The powers in (13) are a separately specified geometric initialization, not polynomial terms hidden in P_(M,T).

Under Report 64's physical theorem, P_(M,T)=0 has its unique positive witness if and only if this encoded physical run reaches its designated halt section within T simulated native instructions. The first-halt variant characterizes first arrival at its T-th instruction section. The virtual padding h after a halt is arithmetic bookkeeping only: with the escape convention, the physical messenger has left the instruction loop. The corollary requires only the physical prefix ending at the first halt and makes no assertion that the padding is physically executed.

For a first halt at k>0, the physical elapsed time is strictly between kD and 10kD, and there have been at most 32k binary collisions. If k=0 it is already at the halt section. For an infinite native run, Report 64 gives infinitely many instruction sections with times at least nD, so no finite-time accumulation is used to interpret these certificates.

This transports a bounded native reachability certificate through a proved physical simulation interface. It does not provide a polynomial predicate on arbitrary real or rational physical coordinates, and it does not equate a fixed collision count with an instruction horizon: different branches have different collision counts.

## 9. Static evidence and primary-source scope

The fresh `static_algebra.py` expands the specified residuals for a small declared instruction graph and several fixed horizons using integer monomial dictionaries. It checks the exact variable/equation/degree ledger, the fourth-power coefficients, and manually supplied positive trace fixtures. It does not simulate a signal machine, predict collisions, run an author program, or execute a native counter-machine interpreter. The construction and uniqueness proof are §§2–6, independent of these finite algebraic checks.

The retained physical proof is pinned by SHA-256 in this packet's manifest. Its scientific claims remain subject to that packet's independent audit; the arithmetic theorem and its exact ledger stand without that dependency.

The instruction semantics have a standard primary-source reference: Andrej Dudenhefner, *Certified Decision Procedures for Two-Counter Machines*, FSCD 2022, §2, Definition 2 and Theorem 6. That paper uses increments and zero/positive-decrement control and emphasizes that universality depends on the exact instruction set. Our compiler allows specified targets for both branches and increments, so it includes that instruction model. The present finite-trace sum-of-squares encoding is elementary; no novelty or universal-polynomial claim is made.

https://doi.org/10.4230/LIPIcs.FSCD.2022.16
