# Review of the concrete machine, windows, and fixed coefficient recipe

Reviewed against ProveIt snapshot
`cdd582bec13f908df3711fa9e05d1ddac368a5db`, 22 October 2026.
This review covers the finite coefficient recipe and its normalization input.
It does not constitute a new Lean/Rocq build or an independent verification of
every theorem in the inherited Pell and helical-tableau dependency chain.

## Findings

No discrepancy was found between the standalone `fixed_compiler.py` finite
layout and the two inspected upstream compiler functions. The normalized
K215 machine/window specification was authored separately and inspected here.
Its exact allowed-window count and the simplified layout powers are correct
under the supplied local predicate. All coefficients are uniquely specified
by finite algorithms. Their full enormous numeral expansions have not been
computed.

### A. Concrete normalization and local predicate

The physical cell at -j stores original virtual cells j and -j-1. The selected
track and the original control state are held in `6+2q+side`; the origin flag
is carried by the tape symbol. The four movement cases, including a stationary
track switch at virtual 0/-1, agree with the stated tape invariant. Input
erasure produces an all-blank simulated tape with its origin marked. The
initial stationary write matches the two retained distinguished windows.
HALT is absorbing and every missing initialization case enters SINK.

The radius-one local predicate retains the source's boundary conventions:
V propagates vertically, H propagates horizontally only across non-V
neighbors, initial phases implement the fixed L/I/Q/R grammar, head escape
is forbidden, and a final interior row permits only an accepting head. The
payload update rejects two or more incoming heads. Finite initial-row
propagation, followed by induction on successive rows, is the mechanism
that rules out extra heads in a marked valid computation.

The corner coordinates are ignored by the center predicate, but their actual
values remain in the 3-by-3 windows and are tested by the two overlap relations.
They must not be removed from the window list merely because the predicate
ignores them. The supplied list preserves them. It puts Start first, End
second, and otherwise uses lexicographic order; that makes the compiler
selector numbering and every `c_i` unambiguous.

### B. Window count

I independently inspected the count formula against `local_valid` and
`next_payload`, and reran the actual 3488-transition count. There are 1722
left-moving, 904 stationary, and 862 right-moving rows. No transition targets
the initialization control state. Thus a headed successor payload has one
tile representation; headless symbols 0 and 1 have three and two respectively,
and other headless symbols have one.

Let a=3502, N=a-1=3501, ell=862 and r=1722. The non-arrival counts are
L=N-ell=2639 and R=N-r=1779. A headed center moving left/right respectively
removes the possible left/right V neighbor from its non-arrival count. A
stationary headed center already supplies the one permitted arrival. For
other centers, the valid cases are no arriving head, one from the left, or
one from the right. This directly gives the formula in `normalization.md`.

The four parts of the cross count recompute to:

| Case | Exact count |
|---|---:|
| Center V | 42936278004 |
| Center H | 85848028000 |
| Upper H, interior center | 686784301040 |
| Interior successor | 135633605274191 |
| Total | 136449173881235 |

The terminal contribution includes 16 no-phase choices for the center
(8 headless, 8 HALT), with a left neighbor, N right neighbors and N choices
of a non-H predecessor. The phase contributions L/I/R add `6a-4`.
For an interior successor, the four initial phases contribute
`2(3L+ell)`, `2(2(L-1)+ell)`, `L-1`, and `2(3(L-1)+ell)`, totaling
`17L+6ell-11`. These details check the two least immediate terms in the
formula independently of its implementation.

Multiplication by the four-corner factor gives exactly

```
k = 20522746353535702537070419760.
```

The separately authored count validation also brute-forces every cross on
two 18-tile fixture machines, checking 3,779,136 cross candidates. I inspected
that test's structure and its recorded receipt; this review does not claim
to have rerun the full brute fixture enumeration a second time.

### C. Exact finite coefficient compiler

The standalone port was checked against extracted ASTs of the inspected
upstream `compile_windows` functions; neither historical module nor its
other imports or test suites was executed. Five concrete finite fixtures
give equality of every field exported by the reference layout, including
both branches of the high-monomial correction, zero-clause padding, all
native positions, both sparse coefficient maps, the enlarged radix bound,
and the modified dummy choice.

On the smallest fixture the full integer constants were materialized.
The native mask ranges, residues and binary populations passed; six exact
modular evaluations agreed with the full values. In particular, the exported
polynomial coefficient is `MF_native+B-1`, not `MF_native`, and its range is
not confused with the native-mask range. `Kconstant=DC+B*DR` and
`W0=2^(b+2d)` were checked explicitly. These checks are recorded in
`fixed_compiler_checks.json`.

The two local reference-copy SHA-256 values are listed below. Each compiler copy has one extra terminal LF; exact upstream hashes are in `PROVENANCE.json`.

```
explore_fixed_raw_universal_76.py
809688579104b43d07d76cb44dc9d5a998fbf981b8a1a2a8506cfca6416079f2

complete75_half_binomial_compiler.py
787a7a35e49651df0be4475d988cb1cbe47ccb894aab99ee5e060a04804a6984
```

The code was fetched from the pinned raw GitHub URLs, and the test receipt
records the hashes of those exact local reference bytes.

### D. Simplified actual layout

At the actual k and a, the least selector radix is A=2^95. The number of
zero-expression padding clauses is `(k-73736)/2`; there is exactly one dummy.
The formulas for M,H,T1,T2 and g then reduce to those in `constants.md`.
The exact integer inequalities checked here are

```
5^43 < 213M+4a+5 <= 5^44,
5^42 < 95J_mu+2 <= 5^43.
```

The padded mu term dominates the alternative coefficient-mass bound:
the actual positive coefficient sum is bounded by `2A^31523`, while
`mu >= A^(31522+p)` and p is greater than 3. This justifies using the
second inequality for the actual compiler, rather than treating it as
an arbitrary admissible choice. It yields `L=5^44`, `b=5^43`, `d=5^87`.

### E. Deliberate evidence boundaries

The complete K215 window alphabet was not enumerated. In particular, the
actual finite sum defining DC and its optional high-correction bit were not
numerically evaluated. That bit is nevertheless exactly determined by the
fixed bounded divisibility test in the recipe; it is not an unknown witness.
The full coefficient expansions would be enormous: B alone has `5^87+1`
bits. They are specified, not materialized.

The new proposed polynomial's arithmetic identities, degree, witness count
and fixed-input elimination are separate from this coefficient review.
The inherited complete75 proof and modified compiler proof were read, and
the interfaces used here match them. Their full chain of Pell/kernel/
helical mathematical proofs has not been re-formalized or newly audited
by a proof assistant in this work.

## Existing nine-variable theorem

The repository's current `Diophantine/Paper1982/NineMain.lean` already
contains the theorem

```lean
theorem Jones1982.nine_unknowns {S : Set ℕ} (hS : REPred S) :
    ∃ M : MvPolynomial (Fin 10) ℤ, ∀ x : ℕ, 0 < x →
      (x ∈ S ↔ ∃ a : Fin 9 → ℕ,
        MvPolynomial.eval
          (fun k => ((Fin.cons x a : Fin 10 → ℕ) k : ℤ)) M = 0)
```

The source forwards through `nine_unknowns_dioph` and the MRDP bridge.
This is a nine-witness existence result; it does not by itself supply the
concrete K215 polynomial's coefficients or a numerical degree bound. It
prevents calling a 16-variable construction the smallest known by variable
count. Circuit cost, degree, explicit coefficient definition and proof
transparency are the intended comparison criteria here.

Pinned source URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean
