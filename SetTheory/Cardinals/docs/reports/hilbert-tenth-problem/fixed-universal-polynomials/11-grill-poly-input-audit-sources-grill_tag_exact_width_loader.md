# Paid exact-width loading for corrected Grill E blocks

The exact-width gap has a complete arithmetic solution using the existing fixed-width binary recoder. The construction retains the native positive width slack and equates the already computed width to the recoder's certified power. It does not substitute a potentially negative computed slack before applying the native theorem. A canonical input-length guard costs two additions; a denominator-cleared encoding equation costs three multiplications and two additions and needs no new repunit witness.

The [emitter](grill_tag_exact_width_loader.py) and [receipt](grill_tag_exact_width_loader.json) contain all recoder gates, all loader constraints, one actual corrected-program native history, and a safe integer-unit finalizer. That measured example has1,568 Grill phases and costs **16,291=4,996M+11,295A**, with3,217 positive witnesses and48 comparisons before finalization. It is a deliberately nonuniversal three-symbol source table, not the205-operation program011. No numerical universal Genera program or ordinary-input universal bound is supplied.

## 1. Exact input contract

Use the corrected compiler and halt protocol of [grill_tag_halt_bridge.md](grill_tag_halt_bridge.md). Fix an alphabet of size N>=3 whose two nonhalt input symbols0 and1 both have width one, and whose halt symbol is different. Other nonhalt symbols may have either source width. Write

~~~
a=28(N+1), b=7a, K=2^b, D=2^14,
A=val(E_0), M=K-1, C=A*(K-1)*(D-1).
~~~

Here val reads queue bits least-significant-first. The corrected blocks have values A and A*D and common length b.

The ordinary external parameter is x>0. This version explicitly pays u=x+1 and encodes the canonical least-significant-first binary word of u. Its source input convention is **binary(x+1)**, not binary(x). This avoids the existing recoder's excluded one-bit duration without hiding a disjunction or a special treatment of x=1. A source recognizer for an intended ordinary-input language must use this explicit convention; substrate universality alone does not furnish that recognizer.

For n=bit_length(u), the required ports are

~~~
q=2^n, Q=q^b=K^n,
R=sum_(i<n) bit_i(u)*K^i,
J_K=(Q-1)/(K-1),
X=A*(J_K+(D-1)*R), P0=Q.
~~~

The source uses the complete [generic-width recoder](gpcp_fixed_program_input_bridge.py): replace only the two private q^4 gates in the authenticated [inline130 source](native_binary_input_dilation130.py) with the literal binary multiplication chain for q^b. This costs mu(b)=floor(log2(b))+popcount(b)-1 multiplications. The recoder certificate costs128+mu(b), with34 comparisons and49 positive auxiliaries when u and R are supplied parameters.

Its theorem gives some n>=2 with0<u<q=2^n, Q=K^n and the unique spread value R, and supplies full positive native extensions for every such n. Since b>=4, its required scale inequality B=2^(b-1)q^b>=8q^2 is retained. The dyadic-duration variant is not used: a canonical bit length need not itself be a power of two.

## 2. Canonical length and E value

Retain the recoder's positive input slack s, with its existing row u+s=q. Supply one additional positive beta and append

~~~
s+beta=u+1.                                    (1)
~~~

Both sides cost one addition. Together the rows give q+beta=2u+1, hence u<q<=2u. Since q is dyadic, this is exactly q=2^bit_length(u). Conversely the canonical q gives positive s=q-u and beta=2u+1-q. The inclusive upper endpoint matters: when u is a power of two, beta=1. Since u=x+1>=2, the native recoder's n>=2 requirement holds. Without the input shift, u=1 would remain excluded; the checker explicitly records this boundary.

Append

~~~
M*X = A*Q + C*R - A.                           (2)
~~~

This costs three products and two additions/subtractions. Every multiplication by a large fixed coefficient is charged. Their binary description sizes remain program-dependent; the arithmetic model is not a bit-complexity bound.

At recoder zeros, M=K-1>0 and Q=K^n, so (2) forces exactly X=A*((Q-1)/(K-1)+(D-1)*R). The quotient is a mathematical repunit, not a division gate or supplied witness. Conversely that integer X satisfies (2). The exact formal identity is

~~~
M*X-A*Q-C*R+A = A*(M*J_K-Q+1)
~~~

after substituting X=A*(J_K+(D-1)*R). The emitted source neither supplies nor computes J_K. The different repunit inside the recoder geometry remains fully paid.

Each E_0/E_1 block is nonzero and has at least two trailing zero bits: the final zero run has length3a-14y-10 for y=0,1. Hence its value is less than K/4, and concatenation gives

~~~
0<X<(K/4)*(Q-1)/(K-1)<Q/3,
~~~

where the last inequality uses K>4. Thus every loaded word satisfies the original strong cone3X<Q, as well as X<Q.

## 3. Exact native width and positive converse

Build the complete weak native history for the actual corrected Grill run table, rename its input parameter to X, and retain its positive witness Z0. The existing computed initial width is P0=X+Z0. Append

~~~
P0=Q.                                          (3)
~~~

Both operands already exist, so no new certificate arithmetic is needed for (3); its residual and square are paid by the finalizer. All old history coordinates, gates, native factors, selectors and phase conditions remain.

On a complete zero, the recoder and (2) first determine X and Q. Equation (3) fixes the input queue to exactly bn bits and Z0=Q-X>0. The native soundness theorem therefore identifies halting of this exact queue. It is not permitted to select a different width for the same integer.

Conversely, if that exact E word halts, choose the recoder's positive extension at canonical n. The strong margin3X<Q gives positive strong slack Q-3X, so the strong native converse applies at the same width Q. Its inherited strong-to-weak coordinate map adds2X to that slack, giving Z0=Q-X without changing the word, width or other coordinates. The phase rewrites preserve the full polynomial. This constructs every positive witness. Neither period padding nor an assumed positivity of an arbitrary off-zero subtraction is used. The finite checks do not materialize full Pell witnesses; their existence is supplied by this parametric converse.

A six-zero extension is now rejected directly: replacing P0 by64Q with X and the loaded ports fixed changes (3)'s residual to63Q. Canonical source-bit length and exact queue-bit width are distinct obligations, both enforced here.

Together with the corrected halt bridge, acceptance is equivalent to Genera halting on binary(x+1) for inputs on which that source execution obeys its published halt convention. No claim is made about undefined multiple-halt source executions. A numerical universal table and a well-defined input protocol recognizing the intended ordinary-input language remain separate obligations.

## 4. Safe full finalization

Let U be the native integer-unit product and S_H the sum of squares of its ten other residuals. Its existing polynomial is F_H=U*(1+S_H)-1. Let S_L sum the34 recoder squares and the three new comparison squares. Emit

~~~
F=U*(1+S_H+S_L)-1
 =F_H+U*S_L.                                   (4)
~~~

The second line is an all-value polynomial identity. Over integer tuples, F=0 implies that the positive integer1+S_H+S_L divides1. Thus U=1 and S_H=S_L=0. Conversely the complete native and loader comparisons imply F=0. This retains every condition. Simply adding S_L to F_H would not have that argument: F_H can be negative away from its zeros.

Every new residual costs a subtraction, square and accumulation addition into the existing nonempty sum. The old addition of1, multiplication by U and final subtraction remain literal. No loader zero test or finalizer is free.

| Added component | M | A | Total |
|---|---:|---:|---:|
| Fixed-width recoder |65+mu(b)|63|128+mu(b)|
| Explicit input shift and two canonical sides |0|3|3|
| Cleared E-value equation |3|2|5|
| Complete added prefix |68+mu(b)|68|136+mu(b)|
|37 residuals, squares and accumulation additions |37|74|111|
| Increase over native polynomial |105+mu(b)|142|247+mu(b)|

The49 recoder auxiliaries, now existential R, and beta contribute51 new positive witnesses. Native input X becomes one more witness: W native witnesses become W+52. The native11 comparisons become48. The recoder input duration n is independent of the arbitrary existential history duration; there is no external computation-time horizon.

## 5. Literal fixed source and scope

The measured source fixes N=3, widths(1,1,1), halt symbol2, and all four nonhalt phase productions to00. It has1,568 Grill phases and60 positive run exponents. Every nonempty binary source word doubles forever without H; this is explicitly a reject-all example, not a universal instance.

Here b=784 and mu(b)=11. The actual native polynomial is16,033=4,880M+11,153A on3,165 positive witnesses. The emitted composition is16,291=4,996M+11,295A on3,217 positive witnesses, with48 comparisons. Complete literal degree propagation gives the conservative upper bound283247. This is not an exact-degree or optimality claim. The205-operation count belongs only to the separate three-phase program011.

The generic loader proof applies to any fixed corrected table meeting the stated input-alphabet convention, but a different table requires its own actual native emission and ledger. The interface does not establish that the present input convention fits a numerical universal Genera table. It also does not claim that a bounded simulation prefix is a complete computation certificate.

## 6. Reproducible evidence

The emitter authenticates the inline recoder source/receipt, generic-width source recipe, corrected block compiler and native compiler. The native builder retains its transitive source guards and imports from authenticated bytes. The large table exceeds Python's default recursion limit in an inherited graph traversal, so the driver temporarily raises that process limit during its construction and restores the previous setting. No compiler source changes.

The supported prototype interface is its standalone CLI. The internal composition routine assumes the authenticated packet returned by the driver; it is not an arbitrary hostile-packet validator. Its receipt includes the entire comparison source and entire finalized source, all coordinates, the actual fixed program, literal ledgers and degree bound.

Checks pass for:

- 93 genuine E-word/recoder outer interfaces over N=3,4,7, and93 rejected six-zero width extensions;
- 128 canonical-length census inputs, including u=1 and power-of-two boundaries;
- 24 complete polynomial corrections (4), including12 signed cases;
- 96 signed block-value identities and preservation of every literal history gate and original comparison;
- Full source closure, current coordinate usage, final-output liveness and actual gate counts.

For the long-table off-zero evaluations, all selector hats equal1 so that J=0 and arithmetic remains bounded. These are explicitly not accepting histories. Genuine recoder outer/AND fixtures retain placeholder Pell coordinates; full positive native extensions follow from the theorem, not these finite examples.

The research environment supplies SymPy required by historical dependencies:

~~~sh
python3 grill_tag_exact_width_loader.py \
  --root /path/to/native-stream-queue \
  --expect grill_tag_exact_width_loader.json
~~~

Use --output PATH to write the deterministic receipt. The long native source is built once per standalone run; no original author suite is rerun. This packet gives a complete exact-width interface and one fully paid fixed source composition. It leaves numerical universal recognizer selection and its ordinary-input theorem open.

