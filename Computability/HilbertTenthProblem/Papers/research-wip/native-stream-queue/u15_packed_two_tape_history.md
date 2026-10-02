# A complete packed two-tape U15 halting polynomial

The direct binary-tape route gives a complete **653=255M+398A-operation
polynomial** with ordinary positive integer input, **105 positive witnesses**,
and four fixed positive program numerals. Its certificate has49 comparisons
and costs507=206M+301A. The emitted polynomial's formal degree is at most1936;
this is an upper bound from the actual arithmetic source, not an exact-degree
claim.

The raw half-tape interface costs **410=147M+263A**, with54 positive witnesses
and14 comparisons. Both are fixed-arity polynomials for an **unbounded**
computation. The history duration is recovered from paid power and repunit
relations, not fixed externally. The complete source contains only binary
addition, subtraction and multiplication.

This gives a direct binary-tape alternative to the744-operation GPCP history
compiler. Other reviewed universal constructions are cheaper, and the
established universal polynomial bound remains87. The
four-numeral program convention is proved below; arbitrary positive numeral
quadruples are not claimed to describe valid programs.

The [compiler](u15_packed_two_tape_history.py) and
[receipt](u15_packed_two_tape_history.json) emit every source gate, comparison,
positive coordinate, fixed table and complete finalizer for both interfaces.
The [raw input loader](u15_raw_half_tape_loader.md) supplies the ordinary
input conversion. The [native computed-field theorem](native_binary_computed_fields.md)
supplies the complete scalar AND relation, including its positive Pell
extension. No variable power, bitwise operation, table-lookup oracle,
controller, or tape-range predicate remains unpaid.

The transition table is the same29-rule U15 table authenticated in the
[Waterfall review](waterfall_report_review_24a743255.md). That review resolves
its primary-paper transcription and halting convention. This construction
encodes source-machine halting; it does not include the extra Waterfall
firing count C and timestamp tau as supplied relation arguments.

## 1. Coordinates and computed geometry

Use positive supplied edge hats Ehat_i for the 29 actual defined instructions, with no halt self-loop or fictitious idle. Mathematically E_i=Ehat_i−1>=0; compute

```
J = sum_i Ehat_i − 29 = sum_i E_i,
D = L0+R0+rho,                 rho>0,
B = 64D,
P = (B−1)J+1.
```

J is computed and may be zero away from solutions. D>=1, B>=64, P>=1 hold before any equations. Choose positive supplied H,G,U,ZL,ZR,ZU,beta and a positive left endpoint hat Lfhat and positive right endpoint Rf; compute Lf=Lfhat−1. A genuine halt has Rf>=1 because its final instruction I1 writes1 moving left. Retain one scalar bound

```
H+G+ZL+ZR+ZU+beta=P.                              (1)
```

Therefore at a zero all five bounded fields are below P and J cannot be zero: P=1 would contradict the sum of six positive terms. Thus J>=1, P>=B and E_i<=J<P hold before power or digit typing.

For instruction i write its fixed source state/read bit, target state, left-direction bit and written bit as (q_i,s_i,n_i,d_i,w_i). Compute ordinary linear projections

```
Q=sum q_i E_i; Nstate=sum n_i E_i; S=sum s_i E_i;
W=sum w_i E_i; Dw=sum d_i E_i; WD=sum d_i*w_i E_i.
```

All are computed by arithmetic on the edge hats with the corresponding fixed hat-offset constant subtracted. In particular S,Dw,WD<=J on every supplied tuple, independently of Boolean typing. **WD is not an extra digitwise AND**: d_i*w_i is fixed compiler data. Keep the head comparison

```
B U = S+P.                                         (2)
```

Before any digit typing, its integer equation gives BU<=BJ+1, hence U<=J<P. Its positive input domain already guarantees U>=1. Thus all three source chunks H,G,U and all three selected outputs fit below P before extracting AND chunks.

## 2. One joined AND pays for all missing digit predicates

Set K29=sum_(i=0)^28 P^i, and form the edge word Hc=sum_i E_i P^i. These are computed finite polynomials, with a paid addition chain for K29. Let Rmask=(D−1)J. Use the 34-lane joins

```
A = H+P G+P²U + P³H+P⁴G + P⁵Hc,
M = (B−1)Dw + P(B−1)Dw + P²Dw
    + (P³+P⁴)Rmask + P⁵J K29,
Z = ZL+P ZR+P²ZU + P³H+P⁴G + P⁵Hc,
Ncap = B P³⁴.                                      (3)
```

The low three lanes select two arbitrary tape digits and one popped bit. The next two lanes test ranges by copying their source into the AND output. The remaining 29 lanes test that each edge word is a subset of the cell-origin repunit.

Apply the **complete prescribed-scale scalar AND certificate** at scale Ncap, with mathematical ports A+1,M+1,Z+1. The actual existing padded registers can be specialized directly to 16A+12,16M+10,16Z+8; no extra three port-shift gates need be emitted. The kernel scale is q=16Ncap. The reviewed six-computed-field, positive-scale version has 64 certificate gates, 9 comparisons and 15 private strictly positive witnesses.

This import is within its full positive graph contract on every positive supplied tuple: q>=16, every contribution to A,M,Z is nonnegative, and F3=16Z+8>=8. Hc=the packed hats minus K29 is nonnegative identically since each hat>=1. Rmask is nonnegative since D>=1. No typing or AND conclusion was used to establish this domain. The three truth fields F0,F1,F2 stay positive supplied coordinates; there is no unsupported subtraction-based elimination of them.

At a complete zero, the scalar AND theorem proves precisely

```
Ncap is dyadic, 0<=A,M<Ncap, Z=A AND M.              (4)
```

The pretyping bounds are stronger: each displayed base-P lane is below P. For the direction masks, (B−1)Dw<=P−1; Rmask<P; Hc<P^29 and J K29<P^29. Equation (1) bounds H,G,ZL,ZR,ZU, and (2) bounds U. Thus A,M,Z<P^34<Ncap before dyadic typing. This excludes cross-lane carries/borrows in the output as well as the inputs.

Since Ncap=B P^34 is a power of two and B,P are positive integers, both B and P are powers of two. Together with P=(B−1)J+1 and J>=1 this gives

```
P=B^t, J=1+B+...+B^(t−1), t>=1.                    (5)
```

Proof: writing B=2^b and P=2^ell, reduce ell modulo b in B−1 | P−1. The smaller number 2^r−1 cannot be a nonzero multiple of 2^b−1. Thus b divides ell. This pays the common duration without a second geometry kernel or a supplied exponent. Also D=B/64 is dyadic.

## 3. Controller, ranges and selected fields

Split (4) at the now justified base-P binary boundaries. The last 29 lanes give Hc AND (J K29)=Hc. Each E_i<P therefore has Boolean base-B digits e_i(j), supported at exactly the possible cell-origin bits. The identity sum E_i=J holds because J was computed from the hats. At each cell the sum of the 29 Boolean digits is at most29<B, so there is no carry: exactly one actual instruction is selected at each position.

The next two lanes give H AND Rmask=H and G AND Rmask=G. Since D is dyadic, Rmask has exactly the low log2(D) bits set in every cell. Consequently the canonical tape digits obey

```
0<=L_j,R_j<D.                                      (6)
```

This explicit range test is essential. The matrix canonical-history proof cannot simply be reused with coefficient two on the next tape digit: for B divisible by4, H=B/2,r=1,L0=0,Lf=B/4−1 satisfies 2(H+B Lf)=B(H−r), although it asserts an invalid left pop. The paid range mask rejects that alias.

After instruction typing, S has bits s_j. Equation (2), with U<P, implies the initial symbol is zero and

```
U=sum_(j<t) r_j B^j,
r_j=s_(j+1) for j<t−1, r_(t−1)=1.                 (7)
```

This is ordinary exact base-B shifting; U's bit typing is recovered from S and the terminal bit. Thus no fourth Boolean-selector kernel is needed.

The first two AND lanes now give ZL=sum d_j L_j B^j and ZR=sum d_j R_j B^j, since (B−1)Dw is the whole-cell direction mask. The third gives ZU=sum d_j r_j B^j; using Dw itself as mask is correct because both U and Dw now have only cell-origin bits. All selected products and all source bit/direction/write/state labels are therefore certified.

## 4. Chronology, tape transport and first halt

Retain the two tape comparisons and one state comparison

```
T=2WD+ZU,
2(H−L0+P Lf)=B(4H−3ZL+2W−T),
2(G−R0+P Rf)=B(G+3ZR+T−U),
B Nstate=Q+9P.                                    (8)
```

Together with (2) this is the same 27=14M+13A comparison interface previously audited, except WD is explicitly a paid table projection and ZU is supplied through (3).

The state comparison's coefficients are the initial state, successive source/target mismatches, and the terminal state minus9. All have magnitude at most14<B, so coefficient induction gives state0 initially, adjacent state agreement, and state9 finally. Equation (7) gives initial head0 and final head1. No selected rule is undefined, so no earlier (J,1) can be crossed.

For tapes, D>L0,R0 by its computed definition. Thus the constant coefficients 2(L_lane0−L0) and 2(R_lane0−R0) have magnitude below2D<B. Each interior recurrence coefficient, using (6) and the certified bits/selections, has magnitude below4D<B. Modulo-B induction sets all these coefficients to zero. The remaining top coefficient forces the terminal equality exactly; it needs no prior upper bound on Lf,Rf. Lf is natural by its hat and Rf is supplied positive. The latter restriction is complete because the final I1 instruction writes1 moving left.

For d=1 the recovered local equations are L_j=2L_(j+1)+r_j and R_(j+1)=2R_j+w_j; for d=0 they are R_j=2R_(j+1)+r_j and L_(j+1)=2L_j+w_j. Binary remainders and natural next tapes make these precisely the deterministic two-stack step, including legal pops. The selected finite history is therefore the machine's actual first halt. Soundness has no remaining external controller, no-carry, power, ordering or horizon hypothesis.

## 5. Why the direct positive history fields are complete

Every genuine halt ends in H0 followed by I1 (indeed the full forced suffix is G0,H0,I1). The last instruction is left and its popped bit is1. Hence its incoming left tape is 2Lf+1>=1. H0 writes1 moving left, so the right tape entering I1 is 2R_previous+1>=1. Therefore H,G,ZL,ZR and ZU all have positive last-cell contributions; U also has its final bit1. They can all be supplied strictly positive without hats. This saves five decode subtractions and the offset gate on the aggregate bound, six additions in total. This argument is specific to the actual U15 first-halt relation, not an arbitrary two-stack controller.

Conversely, take any actual first-halting run. Choose a power of two D larger than L0+R0 and every source and terminal tape value. Put rho=D−L0−R0>0; choose its actual edge hats, histories, selected fields and endpoints. All listed supplied coordinates are positive. In each cell,

```
L_j+R_j+d_j L_j+d_j R_j+d_j r_j
 <=4(D−1)+1 < B=64D.
```

Therefore beta=P−H−G−ZL−ZR−ZU is strictly positive. All five outer comparisons hold by telescoping/actual chronology. Every joined AND lane is true and fits its region; Ncap is dyadic. The full uniform positive converse of the prescribed AND theorem supplies all 15 native witnesses at this exact scale. These are genuine full Diophantine extensions by theorem, not assertions based on finite placeholder tests.

## 6. Complete ordinary-input composition

The [paid loader](u15_raw_half_tape_loader.md) starts from the ordinary
integer x>0. Its existing width32 recoder has a full positive Diophantine
converse and proves, for some n>=2, q=2^n,0<x<q,Q=q^32 and
z=sum bit_j(x)*2^(32j). This input-padding length n is distinct from the
computation duration t recovered in (5). No equation identifies them.

For every c.e. set of positive integers, use the effective source-machine
construction on a recognizer that reads little-endian input pairs, ignores
trailing zero padding and simulates a recognizer of that set. The literal
program recipe produces four fixed positive numerals L_S,A_S,B_S,D_S.
The initial half tapes are constrained by

```
L0=L_S,
16711935*R0+D_S=A_S*Q+B_S*z.
```

These expressions account for the complete fixed bi-tag program, initial
head and marker words, bit blocks, padding and final marker frame. The
loader's proof gives both orientations of the bit convention and positive
coefficients explicitly. It replaces no ordinary input by an unpaid word.

The compiler aliases L0 directly to program_L, so no extra L0 witness or
comparison is retained. R0 becomes one positive shared witness input_R0.
The complete loader prefix costs138=73M+65A and contributes35 comparisons
and50 other positive witnesses. Its actual gates and recoder comparisons
are renamed literally, with disjoint native coordinates. The raw history
source then starts from those very same half tapes.

On a full zero, first apply the paid recoder and frame theorem. This identifies
a permitted padding of x on a valid fixed program slice. The raw history
theorem proves that exact input first-halts. Every permitted padding has the
same recognized membership by construction of the represented recognizer.
Conversely, if x belongs to the represented set, choose a permitted padding;
the recoder supplies its complete positive witnesses, the corresponding
universal run halts, and Section5 supplies the complete positive history and
its native witnesses. The two private witness families are disjoint.

Thus, for each c.e. set S of positive integers, its effective fixed program
quadruple gives

```
x in S  iff  there exist105 strictly positive integers v
             with F(x,program_L,program_A,program_B,program_D,v)=0.
```

F is the single fixed polynomial emitted by ordinary mode. This is a
valid-program-slice universality statement, not an assertion about arbitrary
supplied positive program parameters. Standard zero-input conventions can
be shifted externally; the declared relation argument here is x>0.

## 7. Literal complete ledgers and formal degree bound

Every emitted binary +,−,* costs one, including products with a fixed program
numeral or integer coefficient. Constants and copies are free. The compiler
folds constants and shares exact repeated arithmetic subexpressions. Its
finite compiler-time grouping of fixed rule coefficients introduces no
runtime operation. All emitted gates reach the final polynomial output.

| Interface | Certificate M+A | Comparisons | Positive witnesses | Polynomial M+A |
|---|---:|---:|---:|---:|
| Supplied natural L0,R0 |133+236=369|14|54|147+263=410|
| Ordinary positive x, fixed program numerals |206+301=507|49|105|255+398=653|

The raw witness count is29 edge hats, height, six positive fields
H,G,U,ZL,ZR,ZU, Lfhat,Rf, the aggregate bound slack, and15 private native
coordinates. J,D,B,P and all six rule-label projections are computed. The
ordinary mode adds the shared initial R0 and50 recoder witnesses.

The finalizer emits every comparison difference, its square, and a sum of
all squares. It costs3e−1 operations for e comparisons:14M+27A in raw mode
and49M+97A in ordinary mode. The all-real sum-of-squares property makes its
zero set exactly the simultaneous comparison zero set; the prescribed
natural/positive domain is then used in the semantic proof.

Formal degree is propagated through the literal emitted arithmetic DAG:
a product adds degrees; a sum or difference takes their maximum. Fixed
program numerals have degree zero. This gives at most1936 in both modes.
No equality valid only at solutions, such as P=B^t, is used for that degree
calculation. Cancellation may lower it, so exact degree is not asserted.

The imported64-operation native descriptor, including parameters, private
coordinates, source and comparisons, is pinned by SHA-256
`d8bc3b92ac1a6715f9afc6df8957b9ef69bcfc2025848be824bae3724c637f49`.
The three virtual hat shifts change only their private padded input gates;
the compiler checks those sole-consumer conditions before substitution.
The loader authenticates its twenty retained repository dependencies.

## 8. Replays, public interfaces and evidence limits

Run the script without arguments to compare a fresh receipt; use --write
to regenerate it. Public build(ordinary=False) returns a defensive copy.
checked requires a complete type-sensitive canonical packet. evaluate
requires precisely the declared coordinates and their exact integer domains;
formal signed evaluation must be explicitly requested with signed=True.
Low-level DAG arithmetic and trace/fixture construction are research helpers,
not a separate hostile-input polynomial service.

The saved replay exercises both complete emitted polynomials on72 supplied
assignments, including36 signed ones, verifies16 genuine first-halting outer
histories, rejects128 changed outer coordinates, and checks498 malformed
coordinate assignments and two altered metadata packets. It also retains
the coefficient-two omitted-range alias as a regression. Literal source
liveness, positive coordinate counts, operation histograms, dependency order
and degree propagation are checked when each packet is built.

The genuine-history fixtures satisfy every outer comparison and the exact
joined AND predicate. Their remaining native Pell coordinates are positive
placeholders, so these fixtures are explicitly **not full polynomial zeros**.
The existence of complete positive extensions is the uniform inherited AND
and recoder theorem. The finite fixtures supplement the all-value proof
above; they do not search the unbounded witness set or establish an arithmetic
minimum.

Independent reviews: [full source and residual audit](review_u15_packed_history.md)
([helper](review_u15_packed_history.py), [receipt](review_u15_packed_history.json))
and [mathematical composition review](review_u15_packed_two_tape_history_math.md).
Their scope distinguishes the emitted polynomial proof from finite fixtures.
