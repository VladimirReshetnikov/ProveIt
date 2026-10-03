# Complete fixed Grill program with paid ordinary input

## The emitted claim

The files `grill_program.u32`, `universal.dag`, and `universal.json` specify one finite numerical Grill program and one fixed integer polynomial F represented by a complete binary +,-,* DAG. The program has397,488 run phases. The polynomial has six external positive integer coordinates

    x, a_e, p_e, s_e, C_e, L_e

and797,135 positive existential coordinates. Only x varies as the ordinary argument of a selected represented language. The five program coordinates remain fixed for that language; they are never included among the existential witnesses.

Conditional on the precisely pinned native/U15 theorems and the separately reviewed source simulation, the claim is:

    For every c.e. S contained in the positive integers,
    there is a positive tuple theta_S=(a_e,p_e,s_e,C_e,L_e) such that
    for every x>0,

    x is in S  iff  there exist y_1,...,y_797135>0
                         with F(x,theta_S,y_1,...,y_797135)=0.

There is no assertion that an arbitrary positive program tuple is a valid U15 initialization. Those tuples still define an ordinary polynomial, but only the explicit valid slices below have the stated machine interpretation. There is no claim here about x=0 or negative inputs, a real-domain zero set, a minimal gate/witness count, or a proof-assistant formalization.

The actual complete source ledger is3,600,546=803,517M+2,797,029A. All supplied coordinates and emitted arithmetic gates reach the output. The literal formal degree propagation gives an upper bound71,731,007; it is not presently claimed exact. These costs belong to this new source, not the historical205 example or the16,291/16,289 reject-all illustration.

## 1. Fixed sources and imported premises

All repository premises are pinned at commit `2d887f0fa768fd67f3e545d83f8998b5780e530d` in `VladimirReshetnikov/ProveIt`, under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.

1. `neary_woods_explicit_universal_tm.md` supplies the finite U15 table and per-language finite-frame initialization. The original Table16 is visually checked in the frozen primary PDF. Its unique missing instruction is (u10,b), regardless of the contradictory sentence naming c in the primary prose
2. `grill_tag_halt_bridge.md` and its independent review supply the corrected E/L/R compiler, persistent phase alignment, unique-H cleanup and exact first-empty-time proof
3. `grill_tag_native_word_closure.md`, `grill_tag_native_weak_cone.md`, `grill_tag_native_phase_sharing.md`, `grill_tag_native_phase_residual206.md`, `grill_tag_native_composed205.md`, and `pcp_uniform_affine_pair_units.md` supply the complete fixed-arity native history theorem, native positive extensions/restoration, and exact polynomial rewrites
4. `native_binary_input_dilation130.md` and the inherited complete recoder theorem supply the full unrestricted binary dilation relation at fixed width k>=4. The generic-width substitution is the two-private-power-gate replacement recorded in `gpcp_fixed_program_input_bridge.py` and used by the reviewed exact-width loader. The exact-duration extraction argument is separated from the additional dyadic predicate in `native_binary_dyadic_duration_recoder.md`

The exact recoder source is frozen as JSON data with SHA-256 `175c498990a8e63de7a91d1e3d321ef90a19f129f305074f0c6de10967d0a182`. The fixed native67-row unit kernel is frozen with SHA-256 `2d88343037c08fe8b073f67dca531ee73309c0735c1d98a23c20b9ddb1eb08ae`. Source/provenance files give the upstream blob and source pins. No upstream Python was executed.

The semantic packet `../grill-universal-input-research-20261003/SEMANTIC_CONTRACT.md`, its literal numerical table, independent literal review and separate root input audit establish the intervening corrected tag and Genera simulation. This packet does not substitute an informal substrate-universality slogan for that input-language theorem.

## 2. Exact fixed source machine

U15 uses c=0 and b=1, blank0 outside a finite tape. Refined state i=2(u-1)+r remembers the symbol r just read. For a U15 instruction (u,r)->(v,t,D), the refined state writes t, moves D, and branches to2(v-1)+r' on the next read. The start is0=(u1,0); the accepting state is19=(u10,1). There are29 nonhalt instructions,15 left and14 right.

The corrected tag compiler uses canonical words

    A_i xi_i (a_i xi_i)^M B_i xi_i (b_i xi_i)^N,

where M and N are the left/right binary tape integers with nearest square as the low bit. The complete right/left production tables, including the explicit left prime rotation, are in the literal packet. The even finish rule includes the final filler missing from one printed Cocke–Minsky production. That is an explicitly proved correction in this construction, not an asserted published erratum.

The macro proof gives the actual write/move/read update at every canonical boundary. All valid rejecting and accepting runs have at least three tag symbols before acceptance. The first active A_19 occurs exactly at a canonical accepting boundary, with no previous macro's head lineage still pending. It emits one fresh H; all remaining accepting-state data have inert rules and cannot emit another H. Mere occurrence of a symbol in the second deleted position is never interpreted as acceptance.

Normalize every original phase-0 tag production and empty phase-1 production by padding to four with width-zero dummy d, then producing two width-zero pair symbols. A pair expands to its two original/dummy symbols in either phase. Original symbols retain width one; d produces dd. Two normalized generations reproduce one original generation after erasing d, including the persistent phase. First H appears only in a pair-expansion layer. Its preceding prefix consists only of originals/dummies, whose next normalized outputs have no H. Thus both the unique-H and hypothetical-prefix requirements hold.

The literal normalized source has1,013 symbols:569 nonhalt originals,442 pairs, one dummy and one halt. There are2,024 nonhalt phase rows, each with exactly two outputs. The ignored halt row is total too. Its SHA-256 is `3c8924dbb1b5d6e6b8897e59550b0e38a703654b87442c73487f411e94ae355b`.

With N_G=1013, set a=28(N_G+1)=28392, b=7a=198744. The corrected compiler gives m=14a=397488 runs. `grill_program.u32` is the full little-endian uint32 array, hash `fa658fcdfe1dae2be3a8e2bf97bd613db59558949ea23ca03f549b77201dad01`. Independent formula reconstruction agrees at every entry and byte. The program has24,300 positive runs,373,188 zero runs and2,030 distinct exponents including zero. The largest exponent is275,944.

These are run/macro phases: exponent n denotes n commands11 followed by command10. No bit-complexity or equality between macro time and individual-command time is claimed.

## 3. The valid five-parameter slices

Fix a c.e. set S of positive integers. Choose a one-tape semidecider that reads the canonical LSB-first spelling of u=x+1, decodes u, subtracts one, and recognizes S. Its input symbols use the same pair convention as the pinned U15 initialization. This fixed input convention belongs to the selected semidecider, not to an external computation performed on each x.

The pinned effective machine-to-bi-tag-to-U15 initialization gives a finite program word, a finite data-alphabet size q_B>=2, and fixed right/left boundary-symbol indices. The U15 head is on the final c of the start marker bc. The word immediately left of the head is the finite program followed by b. Define M_e as its reversed LSB value. Everything farther left is blank0.

Define physical binary words

    A_i=(01)^(8i-5)11,
    B_0=A_2 A_1, B_1=A_1 A_2,
    P_e=(01)^(8q_B), S_e=A_right A_left.

Both B_i have length32. The right word is

    P_e B_w0 ... B_w(n-1) S_e,

where w_i=bit_i(x+1), n=bit_length(x+1). Its LSB value is N_e(x). The omitted scanned square is0 and is remembered by refined start state0. Everything after this finite right word is blank0. Since S_e ends in11, N_e(x)>0.

The first three program parameters are

    a_e=val_LSB(P_e)=2(4^(8q_B)-1)/3,
    p_e=2^|P_e|=2^(16q_B),
    s_e=val_LSB(S_e).

All are positive. No runtime computation of q_B or the program word is needed; these are fixed after selecting S.

For each original Genera symbol y, its corrected E word has width b and value E_y=A*2^(14y), where the fixed A is specified in Section5. The literal start IDs are A:00=0, a:00=270, B:00=30, b:00=300, xi:00=539. Set K=2^(2b), and write W_y=E_y+2^b E_539 for a symbol/filler pair. Define

    C_e=W_0 + K W_270 (K^M_e-1)/(K-1) + K^(M_e+1) W_30,
    L_e=K^(M_e+2).

The quotient here is a definition of one fixed program integer: it is the finite sum of M_e powers of K, and is0 if M_e=0. It is not a division gate or existential condition in the polynomial. These two parameters are precisely the value and width of

    E(A_0 xi_0 (a_0 xi_0)^M_e B_0 xi_0).

They are positive and fixed for S. Thus the valid tuple is exactly(a_e,p_e,s_e,C_e,L_e) from one finite selected program. This provides explicit finite recipes for every program parameter and separates their permitted program dependence from the varying ordinary input.

## 4. The two complete paid recoders

### 4.1 Canonical ordinary input

The first disjoint namespace is `canonical_input_bits`. Compute u=x+1 in one addition. The full width32 recoder, retaining all34 comparisons and49 positive auxiliaries, supplies

    q0=2^n, n>=2, 0<u<q0,
    Q0=q0^32=2^(32n),
    R=sum_(i<n) bit_i(u) 2^(32i).

It retains its positive slack s=q0-u. Introduce positive beta and compare s+beta=u+1. Hence u<q0<=2u, forcing n=bit_length(u), including power-of-two inputs. Conversely beta=2u+1-q0>0. Since x>0, u>=2 and the excluded one-bit case never occurs. No input padding is existentially selected.

Let m0=2^32-1. The fixed LSB values of B_0,B_1 are c0=3941247658 and c1=3937053418, so c1-c0=-4194240. Introduce positive N and retain the denominator-cleared comparison

    m0 N = m0 a_e + p_e c0(Q0-1)
                   + p_e m0(c1-c0)R + p_e m0 s_e Q0.

At the recoder zeros this is exactly the finite concatenation value N=N_e(x). Every product with a program coordinate or fixed scalar is emitted and charged. The negative fixed coefficient is not suppressed. N is a supplied positive witness; no arbitrary signed computed expression is used as a native positive input.

### 4.2 Unrestricted tape exponent

The second namespace is `unrestricted_tape_exponent`. It is the full generic recoder with fixed width k=2b=397488, specialized to positive input1 and positive spread output1. It has all34 comparisons and49 fresh positive auxiliaries. It has neither the canonical-length guard nor a dyadic-duration test.

Its complete theorem gives some h>=2 and

    q1=2^h, Q1=q1^k, B=2^(k-1)Q1,
    P=B^h, J=sum_(j<h)B^j.

Introduce positive ell,v,g and retain

    (B-1)v+ell=J, ell+g=B-1, ell=N+1.

The bound is part of the proof, not a promise: B=2^(kh+k-1)>=2^(4h+3)>h+1. Thus2<=h<=B-2. Positivity gives1<=ell<=B-2. Since J is congruent to h modulo B-1, the first equation identifies their unique representatives and forces ell=h=N+1.

Conversely, N=N_e(x)>0 gives h=N+1>=2. The unrestricted recoder has a full positive extension at that h. Set

    v=sum_(j=1)^(h-1) sum_(i=0)^(j-1) B^i>0,
    g=B-1-h>0.

All additional coordinates are positive. The cases h=0,1 are not needed and are not silently admitted. Input bit length n, exponent h=N+1 and native history duration are three different quantities. None is identified with another or bounded externally.

## 5. Exact fixed numeral recipes and unary E boundary

The constant pool contains only these exact finite integer constructors:

- `int(decimal_string)`
- `pow2(t)=2^t` for a fixed nonnegative integer t stored in the source
- `geom4(t)=(4^t-1)/3=sum_(j<t)4^j` for a fixed nonnegative t
- addition, subtraction or multiplication of previously specified constants

Every recipe operand is a constant handle, never an input or a runtime gate. The constructors determine ordinary literal integer coefficients; there is no witness-dependent exponentiation or unchecked division. These coefficient recipes are reproducible descriptions of finite integers, not a claim about small coefficient bit lengths. Every runtime use of a nontrivial coefficient is paid by a multiplication gate unless it is exactly0 or1.

Put gval(t)=2 geom4(t). The fixed corrected E base is

    A=2^7 [gval(a-3)+2^(2a-5)gval(7)+2^(2a+10)gval(a-4)].

The second long grill uses a-4, not the erroneous a-2 prose. The repeated pair has value

    V=A*2^(14*300)+A*2^(b+14*539),

and width k=2b. This value has319,867 bits and matches an independently built literal397,488-bit E pair.

Introduce positive T and retain K*T=Q1. Since Q1=K^(N+1), this forces T=K^N. Introduce positive X and retain

    (K-1)X=(K-1)C_e+L_e V(T-1).

Thus X is exactly the value of

    E(A_0 xi_0 (a_0 xi_0)^M_e B_0 xi_0 (b_0 xi_0)^N).

Its exact width is L_e*T. The native history retains its positive Z0 and computes P0=X+Z0. The additional comparison is P0=L_e*T. This binds every terminal zero bit; a different padded width is not an available interpretation of the same numeral.

Every original E block is nonzero and ends with at least two zeros. With common base2^b, its value is less than2^b/4; summing the finite geometric bound gives0<3X<P0 for this literal word. Therefore the strong native converse applies at the same P0 with positive slack P0-3X. The established strong-to-weak map gives Z0=P0-X>0 and preserves the word, width and history. No positivity is asserted for a computed arbitrary off-zero difference.

## 6. Complete native history and safe finalization

`native_history_proof.md` proves the scalable emitter identical, over all integer tuples, to the pinned complete weak native history polynomial for the same fixed program. The proof covers grouped affine transport, exact selector chronology, phase prefix sums, fixed-exponent powers/repunits, the complete67-row native kernel and its four-factor unit U. Equal appendants retain distinct phase/head selectors.

For the emitted program s=2m=794976 selectors and g=2030 slope classes give797029 native positive coordinates: s selector hats, g selected-history hats, seven outer coordinates and16 native-kernel coordinates. All ten nonunit native comparison pairs are retained.

The complete residual list consists of:

-10 native-history nonunit residuals
-34 first recoder residuals
-1 canonical-length residual
-1 right-tape-value residual
-34 second recoder residuals
-3 exact-exponent extraction/binding residuals
-1 unary scale residual
-1 unary queue-value residual
-1 exact native-width residual

There are86 nonunit residuals, plus the unit condition U=1. The emitted output is exactly

    F=U*(1+sum_(j=0)^85 R_j^2)-1.

If F=0 on integer coordinates, the positive integer1+sum R_j^2 divides1. It is therefore1, every R_j=0, and U=1. This holds even though U or the historical native polynomial may be negative away from the zeros. Conversely those conditions give F=0. No loader SOS is added outside the unit product.

All inputs to the native/restored kernels have the required positivity: ordinary u=x+1 is positive, second seed/output1 are positive, supplied N/X and slacks are positive, selector/group unhat sums are nonnegative on positive hats, P0=X+Z0>=2, and the wrapper's height/radix construction gives positive native scales. The namespace maps share only explicitly supplied ports. Positive extensions from separate recoders and the native history can therefore coexist.

## 7. Soundness and complete positive converse

Fix one valid tuple theta_S from Section3.

If the complete polynomial has a positive zero at x>0, Section6 restores every comparison. The first recoder and canonical guard identify exactly the LSB spelling of x+1 and its finite tape integer N. The second recoder/extraction identifies exactly K^N. The unary-value and width equations then identify the exact E word and its exact dyadic width. Native soundness gives actual finite Grill emptying from that word. The corrected source bridge gives a valid unique-H Genera event. Normalization and the accepting-head macro invariant give U15 acceptance at refined state19. The selected finite program recognizes S on the decoded argument x. Hence x is in S.

Conversely, let x be in S. The chosen U15 finite computation accepts. The corrected tag macro run has no premature short queue and reaches its one accepting head; normalized Genera produces one H in a valid expansion layer. The corrected Grill bridge gives a finite first empty time from its exact E word. Choose the complete first recoder extension at canonical n=bit_length(x+1), set its beta, and use its genuine finite tape value N>0. Choose the second complete recoder extension at h=N+1 and the positive ell/v/g above. Choose T=K^N and the literal positive X. The E-word margin gives a positive strong native extension at the same width; transfer it to the retained weak width slack. All witness sets are disjoint except the now fixed intended ports. Every residual vanishes and U=1, so the full polynomial vanishes.

The native closure witness can encode a selected word with a post-halt suffix; native soundness guarantees actual halting at or before that closure length. This proof does not assert legal physical execution after the first empty queue. The source bridge independently establishes the first-empty cleanup boundary and phase alignment. There is no fixed external computation-time cutoff.

## 8. Complete cost attribution and measured resources

The frozen binary stream contains these paid stages:

- Two complete recoders and input loader:310=173M+137A
- Complete native history source:3,599,976=803,257M+2,796,719A
- One finalizer for all86 nonunit residuals:260=87M+173A
- Total:3,600,546=803,517M+2,797,029A

The finalizer count includes86 differences,86 squares,85 sum additions, addition of1, multiplication by U and subtraction of1. Every constant multiplication, every fixed-exponent runtime product and every source input/width binding is charged. Constant-only recipes describe polynomial coefficients, as in the inherited literal-numeral arithmetic model; this is not bit complexity.

The two recoders contribute98 native positive auxiliaries. Their extra spread, beta, N, ell,v,g,T,X contribute eight, totaling106 new positives. Adding797029 native-history positives gives797135. The six external positive coordinates are not included in that count. The degree calculation treats all six external coordinates and all witnesses as degree one, so it does not incorrectly freeze program parameters while counting the universal polynomial's degree.

The full source SHA-256 is `a07c1ba41e3a18fafd05c19b8ac39211b0475e30ed8a08ddf43c45a9f5f440f2`; it occupies61,209,290 bytes, including the8-byte header. The manifest contains8,160 interned exact numeral recipes. Emission plus backwards liveness/ledger checking took5.47 seconds with107,515,904-byte peak RSS in this run. Explicit limits were6,000,000 gates,200,000 constants,600 seconds and1,800 MiB RSS. No limit was reached. These are measured execution facts, not a performance guarantee.

Prototypes at1,000/10,000/100,000 phases passed the same complete liveness/port checks in0.015/0.133/1.389 seconds. They are truncated-program resource fixtures and are not described as universal. The full797135 witnesses are retained; no unproved phase-selector elimination is used. Constant interning saves storage and does not remove arithmetic uses or quantified coordinates.

Independent whole-source reviews are recorded separately. Bounded simulation, signed/modular arithmetic tests and structural audits are evidence for the implementation. The parametric identities and imported full positive-converse theorems supply the unbounded mathematical equivalence; no enormous full accepting Pell tuple has been materialized.
