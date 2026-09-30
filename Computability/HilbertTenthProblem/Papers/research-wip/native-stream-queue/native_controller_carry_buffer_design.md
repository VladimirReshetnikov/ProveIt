# A concrete carry-buffer and NAND-feedback design audit

This note tests two small proposed ingredients for a deliberate-carry
one-field compiler. It gives an exact constructive buffer-extension lemma,
the additional condition needed to insulate tested bands, and a local
counterexample to a simple NAND feedback encoding. It is not a general
obstruction to carry-based computation and supplies no complete universal
certificate below76.

## 1. A modular buffer really does have a periodic extension

Let Q>=2 be a fixed buffer capacity. For a periodic integer forcing word
g0,...,g_(T-1), let S=sum g_j. A buffer digit b in{0,...,Q-1} updates by

    b_(j+1)=b_j+g_j-Q*k_j, 0<=b_(j+1)<Q.              (1)

For each starting b0 this update is unique and total. After one forcing
period its residue is b0+S modulo Q. Therefore after

    m=Q/gcd(Q,S)

repetitions it returns to b0. This proves an exact periodic extension of
length mT, with explicit integer carry values k_j. It does not prove that
those carries can be discarded. Indeed

    sum_(j=0)^(mT-1) k_j=mS/Q.                        (2)

A k-digit stack in radix R is exactly the same construction with Q=R^k;
the k_j in(1) are its final spill values.

## 2. Exact insulation criterion and positive construction

Suppose the next band is a fixed zero guard, has no other local term
that can cancel the incoming spill, and every residual there is small
enough to preclude a further carry. Then the guard requires each
spill k_j to be zero. Under this insulation requirement, a periodic buffer
exists exactly when

    S=0 and max_j s_j-min_j s_j<=Q-1,                 (3)
    s_0=0, s_j=g0+...+g_(j-1), 0<=j<=T.

Necessity follows by summing b_(j+1)-b_j=g_j and by observing that all
b_j=b0+s_j lie in an interval of length Q-1. Conversely choose any integer

    -min s_j <= b0 <= Q-1-max s_j.

Then all b_j are valid digits, b_T=b0, and every spill is zero. This is
the full constructive map. If a separate positive coordinate is needed,
one may mathematically represent b_j by b_j+1, but any arithmetic that
implements this offset in a certificate still has to be paid.

Two concrete failures distinguish totality from insulation:

- Q=4, forcing(1,1,1,1): every modular buffer returns after one period,
  but its total spill is1. A following zero guard is impossible.
- Q=4, forcing(1,1,1,1,-1,-1,-1,-1): the forcing has zero mean and every
  modular buffer returns, but its prefix range is4. No starting value
  keeps a no-spill buffer in{0,1,2,3}.

Repeating either forcing period does not repair insulation. A nonzero
sum remains nonzero under repetition, and a zero-sum period retains its
original prefix excursion. Thus the assertion that a finite buffer map
has a cycle is insufficient for the proposed reset design. A construction
must supply an actual harmless spill sink or prove condition(3) for every
genuine computation it claims to encode.

## 3. A genuine local NAND carry gadget

Let R=2^b, b>=1. For Boolean inputs a,b0, the equation

    a+b0+v=R+1                                           (4)

forces v to be one of the three positive code values

    v=R+1 for inputs00,
    v=R   for mixed inputs,
    v=R-1 for inputs11.

The bit of v at weight R is exactly NAND(a,b0). Its lower b bits are
respectively1,0,R-1. For b=1 the low bit is XNOR(a,b0). This is an
actual carry-based Boolean gate; its lower part is correlated garbage,
not an independently free field.

For streams whose cells have radix B>=4R, typed input digits0/1 and
typed output digits in[0,2R-1], the packed equality

    A+Binput+V=(R+1)J_B

is coefficientwise exact. The sum on its left has every cell coefficient
at most2R+1<B; consequently there are no carries between cells. If J_B
and all three typed words are already supplied by a proved interface,
two additions and one product by the fixed numeral R+1 implement this
equality. This conditional three-operation ledger does not provide their
typing, input projections, or a one-field placement.

## 4. The simplest feedback placement loses information

A natural next step is to shift two upstream codewords down by b bits
and read their high bits as the two Boolean inputs. Multiplication shifts
the whole codewords, including their lower remainders. Those remainders
can produce a carry into the intended input-count band.

The two perfectly valid codeword pairs

    (R-1,R+1) and (R,R)

have the identical total2R. Their high-bit pairs are respectively(0,1)
and(1,1), which require NAND outputs1 and0. Thus no gate that sees only
their full-codeword sum, with the same incoming carry/reset state, can
implement NAND on both. This is an exact information collision, not an
estimate on rare carry behavior.

In the first pair the lower remainders sum R, creating an extra unit
carry. The false projected input count is floor(2R/R)=2 although the
actual high bits sum1. Applying (4) to that false count produces R-1,
whose high bit0 is wrong. A guard that instead forbids the extra carry
rejects this locally valid pair. The second pair also has full sum2R,
but its high bits really do sum2 and need the low output.

This refutes the specific strategy of applying the equal-weight input
projection to the whole three-valued output codes and treating their
lower bits as disposable. It does not cover different codewords,
asymmetric projections, an additional state that distinguishes the two
inputs, or a proved spill-sink construction. The actual scalar compiler
still needs to address every convolution band; no unused position is
declared free here.

## 5. Evidence and scope

The [checker](native_controller_carry_buffer_design.py) exhausts small
periodic forcing words, constructs the modular extensions and their spill
totals, compares(3) with every possible initial buffer digit, and checks
both concrete failures. It also audits the NAND truth table and the two
indistinguishable input pairs over several powers of two.

The [receipt](native_controller_carry_buffer_design.json) is compared by
default. Independent full proof, source, and default-replay review passed.
These are exact conditional
components and a falsified small feedback design; generic scalar
compilation with deliberate carries remains open.
