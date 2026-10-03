# Independent review of the paid exact-width Grill loader

**PASS.** The frozen [emitter](grill_tag_exact_width_loader.py),
[receipt](grill_tag_exact_width_loader.json) and
[proof](grill_tag_exact_width_loader.md) correctly compose the literal
fixed-width recoder, canonical-length and E-value constraints, exact
native input width, and integer-unit finalizer. No source or proof
correction was requested.

This review covers the complete measured **1,568-phase reject-all table**,
not the unrelated three-phase program011. The actual composed source
costs **16,291=4,996M+11,295A**, has3,217 strictly positive witnesses and
48 comparison conditions, and has the stated conservative degree upper
bound283247. Neither an exact-degree claim nor an ordinary-input universal
recognizer is inferred.

## 1. Input and positivity proof

Write u=x+1 for the explicitly paid positive ordinary-input shift.
For x>=1, u>=2. The inherited complete recoder supplies n>=2,
q=2^n, Q=q^b, the unique b-spaced value R of u, and positive
s=q−u. The new positive beta condition s+beta=u+1 is equivalent to
q+beta=2u+1. Thus u<q<=2u, which fixes q=2^bit_length(u) for every
integer u>=2. Powers of two are included with beta=1. The excluded
one-bit u=1 case is not silently admitted: it cannot occur under x>0.

The independent checker reads the corrected E blocks literally, rather
than reusing the author's closed-form constants. For width-one source
symbols0 and1, both blocks have b bits and values A and2^14 A. Literal
least-significant-first concatenation therefore gives

    X=A*((Q−1)/(2^b−1)+(2^14−1)R).

The paid denominator-cleared equation is equivalent because 2^b−1>0.
Its repunit quotient is integral at recoder zeros and is not a hidden
runtime division or extra witness. Both corrected blocks have at least
two terminal zero bits. Their geometric-series bound implies3X<Q,
with X>0, for every nonempty loaded word.

The native width witness Z0 is retained positive. The new comparison
P0=Q, with P0=X+Z0 in the weak native source, fixes precisely the loaded
word width, including all its terminal zero bits. It does not permit a
second existential choice of padding for the same numeral.

The converse is specifically **at the same width Q**. If the exact loaded
E word halts, its strict3X<Q margin gives a positive strong slack
Zstrong=Q−3X. The strong native converse supplies a witness at that width.
The previously proved strong-to-weak map sets
Zweak=Zstrong+2X=Q−X while preserving the word, width, history and native
coordinates. The phase rewrites preserve the entire polynomial. This
argument uses no theorem that halting survives extra padding and makes
no premature positivity assumption about an arbitrary computed Q−X.
Soundness proceeds directly from the complete weak native zero and
its paid P0=Q binding.

## 2. Every condition and every gate is paid

The authenticated native product has one integer-unit factor U and ten
other comparison residuals. The added loader has34 complete recoder
comparisons plus canonical length, encoded value and width binding:
37 new residuals. The composed source is exactly

    U*(1+sum of all47 nonunit residual squares)−1.

Every integer zero forces U=1 and every square to vanish, since the
positive integer1+S must divide1. This remains valid when computed
intermediate values have either sign. It is not a real-domain argument.
The independent checker derives the full finalizer polynomial from the
literal47 residual-square rows, treating U and those squares as formal
independent atoms. It also verifies the all-value correction
Fnew=Fnative+U*Sloader against the actual native source. Merely adding
Sloader outside the product would not have this integer-unit proof.

The exact fixed source has b=784 and an11-multiplication binary power
chain. The independent replay reconstructs all147 loader prefix gates,
all16,001 inherited history certificate gates, and the complete finalizer.
The native polynomial is16,033=4,880M+11,153A on3,165 witnesses. The
increase is258=116M+142A, including111 operations for the37 newly
finalized residuals. The51 new recoder/R/beta witnesses and newly
existential native input X give52 additional witnesses. Every supplied
coordinate and every counted gate reaches the final output. Direct
literal degree propagation reproduces the upper bound283247.

## 3. Scope and independent evidence

The reviewer independently reconstructed the corrected run table from
its defining positions and the four source productions00. It matches
the saved1,568-phase program exactly, including60 positive run exponents.
This source cannot produce the halt symbol from a nonempty binary word:
each source generation doubles its length with zeros. It is a valid
fully paid illustration of the interface, explicitly not a universal
instance.

For other fixed tables the parametric loader proof remains conditioned
on width-one symbols0 and1, a distinct halt symbol, and the corrected
compiler's well-defined halt protocol. In that domain the inherited
bridge gives halting equivalence on **binary(x+1)**. Undefined multiple-
halt source executions are not certified. A numerical universal source
recognizer with this input convention remains an additional obligation.
The native history duration is existentially packed with fixed arity;
there is no external computation-time horizon. Input bit length and
history duration are different quantified quantities.

The [independent checker](review_grill_tag_exact_width_loader.py) and
[receipt](review_grill_tag_exact_width_loader.json) contain:

- Complete literal comparison, witness, source, finalizer and ledger reconstruction;
- 1,024 canonical-input census cases and21 larger boundary cases through127-bit inputs;
- 96 genuine recoder outer/E-word interfaces for three alphabet sizes, with192 rejected added-width assignments;
- 72 signed denominator-clearing identities and16 complete native/output corrections, including8 signed cases;
- One full symbolic finalizer identity and all47 literal residual-square checks.

The code reuses the authenticated native205 builder, including its
transitive source guards and previously reviewed native theorem. It
reuses no author loader, composition or test function. Corrected E words,
program positions, power chain, renamed recoder rows, complete finalizer,
ledger and canonical-length checks are independently reconstructed.
Full positive Pell extensions are supplied by the parent theorem;
outer fixtures with placeholder Pell coordinates are not asserted to
be complete accepting witnesses. The author's supported interface is
its standalone driver, not arbitrary hostile packets passed to its
internal composition function; this review does not enlarge that API.

The review pins the author Python, JSON and Markdown respectively at
685a5744c180439ca67cdfcb6eace118379365e3575c302cb19ce404aa29d2f4,
48f409c2eb7965ae26a4bef8b58a36ae366dfae3df4b3ca077d463581969fb75,
and9076fcfd9d78c144ccb757dddb34bc5300f0d443336532e45dda621c73187da6.
The source authenticates its complete direct dependency inventory before
execution; the long native build temporarily raises and restores the
interpreter recursion limit. SymPy is required by historical native
compiler dependencies. A portable replay is

```sh
/tmp/diophantine-research-venv/bin/python review_grill_tag_exact_width_loader.py \
  --root /path/to/native-stream-queue \
  --author /path/to/grill_tag_exact_width_loader.py \
  --expect review_grill_tag_exact_width_loader.json
```

Adjust the interpreter path to an equivalent environment with SymPy.
No archive, repository source, author receipt or original theorem was
modified by this review.
