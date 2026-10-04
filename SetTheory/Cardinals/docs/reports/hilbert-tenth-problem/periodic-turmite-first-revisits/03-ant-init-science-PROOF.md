# A paid periodic-rectangle and fixed-length raw-input bridge

## Status

This closes the periodic rectangle, phase, finite anchor, translated initial head, and **each fixed pair of raw word lengths** as an explicit arithmetic DAG. It is a circuit family indexed by two lengths, not one fixed all-length Diophantine formula. The remaining uniform raw-input dilation obligation is stated precisely below. No improved universal arithmetic count is claimed.

All claims about the ant background, input patch, and infinite trajectory are conditional on the separately frozen literal interface theorem. All claims about the 174-operation history are conditional on its pinned theorem. We read those sources; we execute neither their programs nor saved schedules. This packet's code is new arithmetic/checking code, not a re-execution of the ant controller.

Set

    u = 481238074400, v = 576000.

Physical coordinates (a,b) increase east/south. The frozen ant begins at (288650,75,E). Its normalized coordinates and then its board coordinates will be

    X = b-75, Y = 288650-a,
    x = X+u, y = Y+h/2.

The rotation is orientation preserving; the head begins north. The literal accepting event retained by the frozen theorem becomes residues (481225262775,29948,E) modulo (u,v), and both translations above preserve these residues when h/2 is a multiple of v.

## 1. Exact input and inherited ports

Fix two nonnegative meta-integers L,R; write n=L+R and m=n+1. They determine the finite source, rather than being uncharged arithmetic inputs to it. RawLeft and RawRight are arbitrary positive integer parameters. The intended interpretation is

    RawLeft  = 2^L + sum_(j=0)^(L-1) ell_j 2^(L-1-j),
    RawRight = 2^R + sum_(j=0)^(R-1) r_j   2^(R-1-j).

Here ell_0 and r_0 are nearest the simulated head. Empty words have code 1; length-L all-zero words have code 2^L. The code preserves zero padding and is ordinary binary with an initial sentinel 1. For the fixed-length circuit, integers of another bit length are rejected.

The already validated parent history supplies W=3^w, Wp=W/3=3^(w-1), Q=W^h, with w>=3 odd and h>=2 even; it also supplies InitialHead and InitialMemoryPlus. The parent already computes Wp; using it is a wire alias, not an uncharged division. A version exposing only W can instead substitute the equality 3*Wp=W with one additional multiplication and one new positive witness; that variant is not included in the displayed ledger. We reuse the parent's precise initial Boolean-board and north-facing even-index contracts. The five named inherited values are ports, not new witnesses in this component.

For each raw bit supply a positive BitPlus, compute b=BitPlus-1 and bminus=b-1, and impose b*bminus=0. This forces b in {0,1}. Reconstruct each raw parameter by Horner evaluation starting at 1 and using base 2, in nearest-first order. No digit extraction, floor, division or exponentiation instruction is silently supplied. There are n new positive bit witnesses and n+2 equations here.

## 2. A paid, arbitrarily large board and exact placement

The following four new witnesses are positive:

    Xextra, H, K, P.

Prescribed fixed numerals are Cu=3^u and Cx=Cu-1. Construct G=W^v by the binary addition chain, and impose

    Wp-1 = Cx*(Xextra+1),
    H-1 = (G-1)*K,
    Q = H*H,
    H = P*G^m,
    InitialHead = Cu*H.                              (1)

All powers of variable W or G are charged below.

### Geometry theorem

Under the parent's geometry, (1) is equivalent to

    w = 1+a*u with a>=2,
    h = 2*k*v with k>=m,
    H = W^(k*v), P = G^(k-m),
    InitialHead = 3^u W^(k*v),                       (2)

with the uniquely determined positive Xextra and K.

Proof. For integers A>=2 and d,e>=1, A^d-1 divides A^e-1 exactly when d divides e: reduce e modulo d and note that the positive residual A^r-1 is smaller than A^d-1. The first equation therefore gives u | (w-1). The quotient for a=1 is 1, but Xextra+1>=2, so a>=2. Conversely its quotient is at least 1+3^u>1 for a>=2.

The positive square root of Q=W^h is H=W^(h/2), since h is even. The next divisibility gives v | h/2, hence h=2kv with k>=1 and K=(G^k-1)/(G-1)>0. The equation H=P G^m forces k>=m because P is a positive integer; it then uniquely gives P=G^(k-m). The initial head is the monomial for (x,y)=(u,kv). Since u,v are even, its flattened exponent u+wkv is even, matching the parent's north-facing initial parity. Every reverse implication follows by substitution. No integer factorization is an arithmetic gate in this argument.

The zero quotient k-m=0 is allowed: it gives P=1, not a forbidden zero witness. The other geometric quotients are genuinely positive.

### Initial support bounds

The fixed anchor occupies physical a in [288617,289200], b in [-144,76], hence board x in [u-219,u+1] and y in [kv-550,kv+33]. All variable tape and marker changes have x=u-21. Their least board y is kv-vm+23945>=23945; their greatest y is below kv+33. Thus all initial changes and the initial head lie strictly inside or on valid cells of every board (2). Since a>=2, w>=2u+1>u+1. Since k>=m>=1, 0<=kv-550 and kv+33<2kv=h.

The frozen global proof bounds every prefix below in physical b by -144. Consequently its normalized X is at least -219, and the fixed horizontal translation by u works for **every** prefix. For any given finite prefix the upper X and the two extremes of Y are finite. Choose a large enough a>=2 and k>=m so that it lies inside width 1+au, height 2kv after this translation. Such boards are arbitrarily large. Conversely any bounded history begun on the constructed board agrees step for step with the infinite literal board until its endpoint, because it never leaves the rectangle. Padding is therefore enough and does not change acceptance.

## 3. Exact fixed periodic rectangle

Let c(a,b) be the binary color of the frozen literal periodic generator, before all input changes. Define its normalized fixed background

    B(i,j) = c(288650-j, i+75).

It has periods (u,v). For 0<=j<v put

    alpha_j = sum_(i=0)^(u-1) B(i,j)*3^i,
    beta_j = B(0,j),
    A(W) = sum_(j=0)^(v-1) alpha_j W^j,
    B0(W) = sum_(j=0)^(v-1) beta_j W^j.

These are prescribed constants, not existential colors or arbitrary coefficient ports. Their exact recipe is the frozen, pinned total color function. It is not necessary to expand an alpha_j's roughly 10^11 decimal digits to specify that coefficient. The free-fixed-numeral convention and the enormous literal construction convention are separated in section 6.

Put Hx=Xextra+1 and Hy=K*(H+1). Then

    Background = Hy*(Hx*A(W) + Wp*B0(W)).            (3)

Proof. Hx=(3^(au)-1)/(3^u-1)=sum_(s<a)3^(su) repeats a complete u-column row tile. Wp=3^(au) contributes the first tile column once more, supplying width w=au+1. These supports are disjoint, so no ternary carry is possible. Hy=(Q-1)/(G-1)=sum_(t<2k)G^t repeats the v rows exactly 2k times. Since W=3^w, row supports are disjoint as well. Thus (3) is exactly the row-major ternary Boolean encoding of the fixed background on the chosen rectangle. No period is incorrectly required to divide the odd width.

## 4. Compressed anchor and literal input correction

For each frozen anchor row (a,b,old,new), put delta=new-old, which is +1 or -1. Define the fixed degree-at-most-583 polynomial

    J(W) = sum_anchor delta * 3^(b+144) * W^(289200-a). (4)

All exponents are nonnegative: 0<=b+144<=220 and 0<=289200-a<=583. Its 584 coefficients are again prescribed signed numerals. The anchor is used exactly once; it already includes the left marker. It has 2806 distinct cells.

Let the m entries t_i be reversed(ell), followed by a zero head placeholder, followed by r, and form

    T(G) = sum_(i=0)^(m-1) t_i G^(m-1-i).

Equivalently T=G^(R+1) sum ell_j G^j + sum r_j G^(R-1-j). The first form is evaluated by one length-m Horner chain, costing exactly 2n operations even when some arguments are zero. Set

    Cbase=3^(u-219), C198=3^198,
    E = W^24000*T(G) + G^R,
    Z = W^23945 + W^263945*(W^264000+1)*E,
    D = W^(v-550)*G^n*J(W) - C198*(W+1)*Z,
    InitialMemoryPlus = Background + Cbase*P*D + 1.  (5)

Every multiplication, addition, subtraction, and fixed power in (5) is in the source DAG.

### Initialization theorem

For the fixed L,R raw inputs accepted by section 1 and the geometric constraints (1), the integer on the right of (5), minus one, is exactly the initialized frozen literal ant board after translation (x,y)=(b-75+u,288650-a+kv).

Proof for the anchor. A changed physical cell (a,b) contributes

    delta * 3^(u+b-75) W^(kv+288650-a)
    = Cbase*P * delta*3^(b+144) W^(vm+288650-a).

Since vm+288650-a=(v-550)+vn+(289200-a), the sum is precisely the first term of Cbase*P*D.

Proof for the input. Slot q in module i changes exactly (a,b)=(vi+704+24000q,54) and (vi+705+24000q,54), both from 1 to 0. Their negative contribution after division by Cbase*P is

    -C198*(W+1)*W^(vm+287945-vi-24000q).            (6)

For the right marker i=m,q=11 this exponent is 23945, giving the first term of Z. The left marker is not added: its two cells are already in the anchor.

A tape bit 1 at primary index i has two source fields: (module i,slot 13) and (module i+1,slot 0). Their exponents in (6) are v(m-1-i)+551945 and v(m-1-i)+287945. These are the terms

    G^(m-1-i)*W^24000*W^263945*(W^264000+1).

The A0 primary head is value 2 at i=L, hence bit index 1 instead of 0. Its two fields are (i,slot 14) and (i+1,slot 1), lowering both exponents by 24000; their shared exponent in G is m-1-L=R. This gives the G^R summand of E. Summing tape bits, the head, and the endpoint marker yields the second term of D exactly.

The frozen theorem proves that all variable source fields have old color 1 and the two left-marker overlaps agree with the anchor. Every other field is disjoint. We omit that overlapping left marker, so the signed difference has no double-counted cells. After adding it to Background all ternary digits remain 0 or 1. Cardinality of the changed support is 2806+4(popcount ell+popcount r+1)+2=2812+4(popcount ell+popcount r). Leading zero bits still affect m, the right marker, and the geometry through G^m; they are not erased.

## 5. What has and has not been composed

The new equations determine a correct board and a correctly positioned north-facing initial head for every raw word pair of the fixed lengths. The inherited history can now be attached by literal wire identifications. Its endpoint selector from the separately frozen endpoint packet still applies, because both translations are multiples of the normalized periods.

This does not by itself assert a new all-length universal arithmetic relation. There is one source for each (L,R); its bit witnesses, equation count, and operation count grow with L+R. Neither the number of raw integers nor an unspecified compiler erases that dependence. The underlying U15 arbitrary-program compiler remains the separate dependency identified by the frozen interface.

There are n+4 new positive witnesses and n+8 equations in this component, in addition to the named inherited ports and two raw parameters. Gate names are expressions, not extra unknowns. Internalizing the original history's five parameter ports, selecting its final head/sign, and combining all equations into one polynomial would require a new global ledger. We do not silently include or omit those operations and variables by printing 174 plus the present number.

## 6. Exact operation ledgers

Let lambda(e)=0 for e=0 or 1, and lambda(e)=floor(log2(e))+popcount(e)-1 for e>=2. This is the length of the literal left-to-right binary multiplication chain used in the source. Powers with exponent 0 are the constant 1; exponent 1 is a wire alias. Put

    Cpow = lambda(v)+lambda(n)+lambda(n+1)+lambda(R)
         +lambda(575450)+lambda(23945)+lambda(263945)
         +lambda(264000)+lambda(24000).

For the unoptimized literal free-fixed-numeral DAG the exact counts are

    M = 2(v-1)+583+3n+Cpow+18,
    A = 2(v-1)+583+4n+13,
    operations = M+A,
    equations = n+8,
    new positive witnesses = n+4.                  (7)

The 2(v-1) contributions in each class evaluate A(W),B0(W). The 583 contributions evaluate J(W). The raw bit typing costs nM+2nA; raw sentinel reconstruction costs nM+nA; T(G) costs nM+nA. The rest is the displayed powers and 18M+13A of geometry, background, patch assembly, and final positive adapter. Assertions of equality of constructed expressions cost no arithmetic operation. Multiplication by a fixed numeral is counted. We do not suppress leading-zero or zero-coefficient Horner gates.

For empty words n=R=0, the measured source has 1,152,737M+1,152,594A = **2,305,331 operations**, eight equations and four new positive witnesses. It is an unoptimized initialization example, not a universal record.

### Literal constants from 1 and 3 only

Here is a fully paid, exact alternative prefix. Build 0=1-1, -1=0-1 and 2=1+1. Build Cu=3^u, Cbase=3^(u-219), C198=3^198 by independent binary chains and Cx=Cu-1. For each of the v coefficients alpha_j, evaluate its prescribed u-bit ternary Horner string, starting at its first fixed 0/1 bit: this costs u-1 M and u-1 A even when some bits are zero. Each beta_j is an alias of 0 or 1. For each of the 584 coefficients of J, evaluate a prescribed 221-symbol signed ternary Horner string with symbols in {-1,0,1}, for exactly 220 M and 220 A. Each sign is fixed by the 2806-row anchor map, not an unknown.

The strict prefix therefore has

    Mconst = v(u-1)+584*220+lambda(u)+lambda(u-219)+lambda(198),
    Aconst = v(u-1)+584*220+4.

Numerically this is 277,193,130,853,952,587M + 277,193,130,853,952,484A = **554,386,261,707,905,071** extra operations. This is a precisely specified finite straight-line program, not a claim that its expansion was materialized or run. Its astronomical size is part of the result. The coefficient-recipe generator has no input-dependent data and yields a well-defined literal sequence of 0/1/-1 constants. Computing which fixed bit goes into the source is compile-time source generation, not a run-time variable-color query.

Adding this prefix to (7) is the strict literal ledger for this bridge only. The parent history has its own fixed numeral convention; the strict bridge ledger does not upgrade the parent's numeral ledger for free.

## 7. Exact remaining all-length obligation and an obstruction

One useful way to close the uniform problem would be a single finite positive Diophantine DAG with ordinary raw binary sentinel ports x_left,x_right and variable radix G, whose unique outputs are

    A = G^(L+R), B = G^R,
    T = G^(R+1) sum ell_j G^j + sum r_j G^(R-1-j),

with L and R exactly the sentinel lengths of the two inputs. Its other output G^(L+R+1) can be computed as A*G in one multiplication. It must include all digit typing, word lengths, left-word reversal, exponent synchronization, positive adapters, bounds, and converse witnesses. Replacing our length-indexed bit/Horner module by such a paid fixed relation would leave the entire periodic/anchor/placement construction fixed. The own-code function `build_uniform_wrapper` explicitly supplies that fixed outer source: it consumes already-certified expression ports A,B,T, constructs G=W^v and G^(L+R+1) as A*G, and otherwise implements (1),(3),(5) unchanged. Its independently streamed ledger is 1,152,738M+1,152,594A = **2,305,332 operations**, six equations and four additional positive witnesses. T may be zero and is an expression port; if instead one supplies a positive Tplus and subtracts one inside this wrapper, add one subtraction and charge that supplied coordinate at the composition boundary. The three dilation outputs are not made free raw parameters in any claimed theorem. The receipt has a separate SHA256 from the fixed-length family. Its off-solution residuals were compared against the family after exact substitutions for A,B,T. Uniform raw dilation cannot be treated as a coefficient recipe because its values depend on the two raw inputs.

There is a sharp elementary obstruction only to **witness-free polynomial** dilation, not to Diophantine definability. Fix any valid board radix G=3^(wv)>1. Suppose a finite circuit using only +,-,* computed the sentinel-preserving dilation f(x)=G^L+sum b_j G^j on every positive binary sentinel input. On the all-zero length-L words x=2^L this would give f(2^L)=G^L. A polynomial of degree d has asymptotic ratio f(2^(L+1))/f(2^L) tending to 2^d (a nonzero constant polynomial gives 1). The demanded ratio is G, an odd power of 3 greater than 1. This is impossible. Free enormous fixed coefficients do not change the argument. Existential witnesses may overcome this obstruction; their missing construction and cost are exactly what we do not claim.

## 8. Verification and provenance

`bridge_dag.py` is the complete own-code fixed-length arithmetic DAG generator. Its default closed ledger does not emit millions of lines. `--full-stream` actually constructs and validates every gate of the free-fixed-numeral circuit, hashes all gates and equality assertions in source order, and compares counts with (7). `--emit` writes the same literal DAG as JSON lines. It never expands a fixed giant coefficient. The optional small `period_y` parameter in the Python function is a structural-test tool only; it is not a different literal ant construction.

Both executable scripts explicitly reject optimized Python before scientific checks. The DAG generator checks opcodes, earlier-wire references and equality endpoints. It is an own fixed-source generator, not an untrusted-source parser.

`check_bridge.py` independently checks geometric repetition against dense small periodic boards, exact patch-polynomial identities against independently assembled frozen coordinates, raw sentinel recovery, finite source ledgers, and both full 2.3-million-gate literal streams (fixed-length empty case and conditional uniform wrapper). It tests rejection-oriented boundaries and old/new anchor changes. These checks supplement the proof; they do not construct a dense literal board, instantiate the parent's enormous history/Pell witnesses, simulate the giant ant program, or prove the all-length missing module.

Read-only source pins:

- Parent note: SHA256 9c26b118aa28f8454204be6fb6f751beeae713a752d18b75943e9862e7de1656; official source https://github.com/VladimirReshetnikov/ProveIt/blob/5883b08b7af362077f13bb4afa97a23a90ae4cf8/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md
- Frozen interface proof: SHA256 a8b4a65ad97a06f3c854a9d133e67dca240d6212749f42ed6c4a92b30318483b
- Frozen anchor JSON: SHA256 cc67f7c924bcb27ca1c4a48c8d3a630d837b639fbff3032d04515ec1d534ed68
- Frozen interface root: sibling `literal-turmite-interface-release-20261003-v2`
- Frozen endpoint root: sibling `literal-turmite-endpoint-release-20261003`

All frozen files are preserved. No upload, publication, public-repository write, third-party contact, upstream program execution, or saved-schedule execution is part of this work.
