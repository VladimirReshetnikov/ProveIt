# STRIVE-iPRA theorem ledger

Status vocabulary:

- **inherited checked**: present in the pinned ProveIt Lean libraries;
- **source candidate**: complete Lean source supplied but not elaborated here;
- **human proved / executable tested**: full paper proof plus reference tests;
- **Lean blueprint**: exact target and dependency path, with visible `sorry`;
- **conditional**: theorem schema requires an explicit producer/residual;
- **open**: no generic producer is claimed.

| ID | Statement | Status | Main dependencies |
|---|---|---|---|
| K1 | Substitution, weakening, simultaneous cut, existential sealing | inherited checked; wrapped by source candidate | `ConciseIPRA.Deduction` |
| K2 | Open-sequent transport between ordinary and Foundation iPRA | inherited checked | `IPRABridge` |
| M1 | Mixed-radix pack/unpack is inverse for bounded digits | human proved / executable tested; Lean blueprint | Division, Powers, MultiSums |
| M2 | Packed bounded table code is below the product of radices | human proved / executable tested; Lean blueprint | Order, Semiring, Powers |
| M3 | Heterogeneous digit access and extensionality | human proved / executable tested; Lean blueprint | `div_mod_unique`, prefix products |
| G1 | Every fixed bounded formula has a Boolean value PR program | human proved / executable tested; Lean blueprint | structural specialization, folds |
| G2 | Positive checker soundness: accepted code implies formula | human proved / executable tested; Lean blueprint | M1-M3, Search, qf induction |
| G3 | Negative checker soundness: accepted code implies negation | human proved / executable tested; Lean blueprint | M1-M3, Search, qf induction |
| G4 | Canonical signed strategy code is accepted for computed value | human proved / executable tested; Lean blueprint | least search, prefix sums/products |
| G5 | Empty existential/universal conventions are handled exactly | human proved / executable tested; Lean blueprint | empty sum/product equations |
| C1 | Local certificate is erased by existential elimination | inherited checked; source candidate wrapper | `Prf.exE` |
| C2 | Observed certificate can be erased under pairwise invariance | human proved; Lean blueprint | C1, equality/equivalence transport |
| C3 | Named certificate obtained by bounded least search | conditional on bounded existence; Lean blueprint | `Core.Search` |
| D1 | Finite monotone demand iteration reaches least prefixed point | inherited human result; executable tested specialization | finite-chain rank |
| D2 | Stabilized demands compile to a finite clocked schedule | conditional; human proof | D1, trace reflection obligations |
| O1 | Exact stable observer makes selection independent of certificate | human proved; Lean blueprint | equality transport |
| O2 | Quotient observer needs only a reflected equivalence, not a quotient type | human proved; Lean blueprint | congruence contract |
| O3 | Metric observer yields explicit diameter error | conditional on distance/diameter producer | rational arithmetic |
| A1 | Finite-net optimization schema | conditional on coverage and evaluation modulus | G1-G4, O3 |
| A2 | Approximate inversion schema | conditional on a positive lower bound | division and error arithmetic |
| A3 | Bounded Diophantine enumeration | conditional on an explicit height bound | G1-G4 |
| X1 | Generic height bound from finiteness alone | open / not claimed | genuine theorem-specific input |
| X2 | Generic modulus or branch separation from bare existence | open / not claimed | genuine theorem-specific input |
