# Grouping the positive7 right pack and sharing its tail power with the native scale

A paid local schedule saves at least 2r+5 multiplications, with no change in additions, against the current common-center compiler for every fixed r>=1. It preserves the right packed polynomial and native scale on every integer tuple. The intended universal regime r>=151 is included. This is a local proof and grammar ledger, not an emitted complete successor or a numerical universal alphabet.

Root requested a further paid saving, emphasizing the collected common-center branch. Riemann derived the grouping and joint power schedule below. The common-center source is frozen at commit d2b9e11c06ea6f4bb914dfb9875939fab07bf6ed; immutable inspection uses HEAD 5be712ff13514ddf8abb671adf23cefd3b830412. No frozen or supplied code was run/imported and no stored arithmetic array was evaluated.

## 1. Exact paid interface

Let m=8+2r, P be lane_scale, Pn=P^n, and Rn=1+P+...+P^(n-1). The current source already pays for P2,P6,P7,P12,P28,Pm and R2,R6,R7,Rm. P12 is obtained through the existing left_support_P12 port, including its possible geometric alias. The retained tail is

    tail=(D-1)*(J+P).

The unchanged source pays one addition and one multiplication for this tail. The old right pack descends through m labelled selectors S_i. Its widths are 6 at i=0,...,3, 7 at i=4,...,7, and 2 at i=8,...,m-1. Each old block computes

    acc <- P_width*acc + C_width*S_i,
    C_width=(B-1)*R_width.

The three C_width producers cost 3M. They have no arithmetic consumers outside these old block lower products. The block loop costs 2mM+mA. The resulting high word then enters

    packed_right=Pm*high+J*Rm.

Both outer products and the final addition are retained. So are the two other native packs, every witness, fixed recipe, comparison and finalizer.

The old native scale is T=P^(3m+38). It currently uses 4-C products, where C=1 if binary m begins 10011, otherwise C=0. This is the existing P19 alias flag. Its private chain starts at P19=P12*P7 when C=0, then multiplies by Pm, squares, and multiplies by Pm again. Its only external arithmetic consumer is pell_q; any updated T port must name the new exit.

## 2. Three selector polynomials and an exact identity

Build by ordinary descending Horner recurrences

    Q6 = S_0 + P6*S_1 + P12*S_2 + P18*S_3,
    Q7 = S_4 + P7*S_5 + P14*S_6 + P21*S_7,
    Q2 = sum_{i=0}^{2r-1} S_(8+i)*P^(2i).

The displays specify values, not free power ports: Q6 uses only Horner multiplication by the already paid P6; Q7 uses P7; Q2 uses P2. Their total cost is (2r+5)M+(2r+5)A: 3+3+(2r-1) Horner steps. In particular Q2 is nonempty because r>=1.

The following identity is obtained by grouping the old descending block recurrence according to its three consecutive equal-width runs:

    high=(B-1)*[R6*Q6+P24*(R7*Q7+P28*R2*Q2)]
         +P^(52+4r)*tail.                                      (1)

The first four widths sum to 24, the next four to 28, and the last 2r widths sum to 4r. Thus the last exponent is 52+4r=2m+36. This is a polynomial identity; no one-hot selector condition or native-zero assumption is used.

## 3. Fully paid replacement

Define D18=1 precisely if binary m has at least five bits and begins 1001, and E24=1 precisely if it has at least five bits and begins 1100. The base schedule uses these products when the corresponding power is not already available:

    P24 = P12*P12;                   # omit if E24=1
    P18 = P12*P6;                    # omit if D18=1
    Y = Pm*P18;
    H = Y*Y;
    native_factor = Pm*P2;
    T = H*native_factor.                                      (2)

Here H=P^(2m+36), and T=P^(3m+38) is exactly the old native scale. The two optional powers precede all consumers; H serves both the right tail and the native scale. The total support/joint-native cost in (2) is (6-D18-E24)M.

Use the following seven products and three additions for the right high word:

    q2 = R2*Q2;
    q7 = R7*Q7;
    q6 = R6*Q6;
    shifted2 = P28*q2;
    middle = shifted2+q7;
    shifted7 = P24*middle;
    lower = shifted7+q6;
    selected = (B-1)*lower;
    upper = H*tail;
    high = selected+upper.                                    (3)

Every displayed product is charged, including the product by B-1. Delete all three old C_width producers; R2,R6,R7 remain paid and used. Equations (1)–(3) prove the exact two-exit replacement (high,T).

The old cut has (3+2m+4-C)M+mA=(23+4r-C)M+(8+2r)A. The new cut has

    (2r+5)M+(2r+5)A   selector Horner polynomials,
    (6-D18-E24)M      support and shared native scale,
    7M+3A            right high word,

or (18+2r-D18-E24)M+(8+2r)A. Hence the exact saving is

    deltaM=2r+5-C+D18+E24,       deltaA=0.                     (4)

C implies D18. Thus deltaM>=2r+5, with one further saving for prefix 10010 or prefix 1100 when the stated length condition holds. These two extra cases are disjoint. In the requested r>=151 regime the length condition is automatic, but it is retained for smaller r.

## 4. Alias, topology and whole-output obligations

The current geometric grammar starts from 6 for prefix 110, from 7 for 111, otherwise from 2 for 10. Every subsequent bit first doubles its current exponent; a 1 bit then appends the odd exponent. P18 is available exactly by doubling the visited prefix 9, which occurs exactly for prefix 1001 followed by at least one bit. P24 is available exactly by doubling prefix 12, which occurs exactly for prefix 1100 followed by at least one bit. For example, m=18 has binary 10010: the prefix 9 occurs before the final 0, which doubles it to the available P18. No other seed branch reaches these exponents. The sources preserve earlier power rows, so both aliases remain available. When C=1, the old geometric P19 remains part of that unchanged extension; only its three native descendants are deleted.

The generic grammar and the three saved r=1,2,4 records show that C2/C6/C7 only feed the matching old right_block_lower rows. The old right tail feeds the first block, every nonfinal block join feeds the next shift, and right_block_join_0 has sole external arithmetic consumer right_selector_shift. The private native chain ends only at pell_q. Rebind those two consumers and the T metadata port. Retain the right tail producer and all existing P/R support producers. If a future source gives deleted internal names additional active metadata uses, rebind those explicitly; historical splice receipts are not executable ports.

The replacement can be emitted after the existing left-pack support and before the right selector join. Thus the existing P12 port, P28 and all geometric powers precede their new consumers. T may be produced there or after the right join. No new witness, fixed literal role, domain restriction or division is introduced. All selectors may be arbitrary integers in the identity; guarded semantic positivity remains exactly the parent's statement.

Since the other packed inputs and all residual machinery are unchanged, an exact full composition would preserve the complete final polynomial on the same integer tuple, and hence every positive zero and ordinary-input projection. This inference requires the future source actually to close all stated consumers. No complete successor arrays have been emitted in this packet.

For the collected r>=8 branch, subtracting (4) from the frozen parent's proven general ledger predicts

    (222+28r+gM-A-B-D18-E24-eta)M
      +(512+39r+gA-B-eta)A,                                 (5)

with the existing flags A=prefix101, B=prefix1110 of sufficient length, eta=prefix100, and the unchanged geometric costs gM,gA. Formula (5) is a conditional composition ledger, not a revised count assigned to the frozen source. In particular it applies to the retained unpruned recipe's r>=151 regime without supplying a numerical universal r.

## 5. Retained boundaries and evidence

**Remark 1 (the uncharged tail-power shortcut is false as a paid claim).** Grouping the selector coefficients alone does not leave P^(4r) as a free port. Replacing each run by a single shift while omitting its power cost is unsupported. Equations (2) and (3) pay a shifted tail power that also serves T, avoiding division. There is no polynomial quotient shortcut at P=0.

**Remark 2 (retained weaker valid draft).** The preliminary schedule kept C2,C6,C7 and used them in (3), omitting the outer B-1 product. It saved (2r+3-C+D18+E24)M and no additions. The final schedule removes those three private coefficient products and adds one outer product, saving another 2M. The preliminary identity and ledger were valid, but weaker.

**Remark 3 (short-prefix alias boundary).** Binary m=12 is 1100, but its geometric chain stops at P12 and does not supply P24. The length condition in E24 is essential. This is a literal power-availability boundary, not a statement about evaluating a compiler assignment.

**Open question 1, credited to root.** Emit and independently audit a complete successor with the two-exit replacement, deleted C_width/native cones, optional aliases, metadata bindings, row counts and liveness. This packet provides no universal numerical matrices, degree bound, optimality proof or full successor count certification.

All identities and ledgers were derived by hand. Existing Python sources were read only as text; saved JSON rows were inspected solely for literal names, operands and consumers. No source arithmetic, coefficient specialization, degree propagation, scientific sampling or frozen/helper replay occurred. The companion receipt binds exact read spans and immutable source bytes. Pascal independently read the full 110-line draft and passed the identities, ledger, prefix conditions and conditional collected ledger; his scope excludes source-array auditing. Root also read all 110 lines and passed the same mathematics, while distinguishing the separately documented inert consumer scan from his own hand-review scope. The final added m=18 example only spells out the already proved alias boundary. This note and its receipt are frozen; the complete-splice question remains open.
