/-!
# Object-theory endpoint blueprint (not compiled in this archive)

The final files live inside the ProveIt checkout and import:

```
import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation
```

The exact endpoint is never merely a native theorem.  It is a value of one of
these forms (notation shown in ASCII here):

```
Prf PRAAx [] powerCoverFormula
Prf PRAAx [] localizationTransFormula
Prf PRAAx [] principalCoverGlueFormula
Prf PRAAx [] p1LaurentSplitFormula
Prf PRAAx [] projectiveCechHomotopyFormula
```

The final transport is the existing repository theorem:

```
theorem pra_iff_native {Gamma : List (Fm PTm n)} {phi : Fm PTm n} :
  (Gamma |- [PRAAx] phi) <->
    NPrf (Gamma.map NFm.ofPRA) (NFm.ofPRA phi)
```

Planned object functions (each one a fixed `PR` code):

* finite-list length/get/update/fold and bounded max;
* integer, tuple, polynomial, Laurent-polynomial and exponent-vector codecs;
* polynomial substitution and coefficient comparison;
* ideal-certificate checker;
* localization witness constructors for refl/symm/trans/add/mul;
* weak-composition enumeration, multinomial coefficient, and term assignment;
* power-cover coefficient producer;
* denominator homogenization and principal-cover gluing producer;
* subset enumeration, Cech differential, insertion homotopy, and matrix check;
* P^1 Laurent high/low/middle split.

For every loop, introduce a quantifier-free formula describing the entire
finite state.  Global hypotheses such as validity of the ring presentation are
parameters and are only instantiated at finitely many indices.  The induction
constructor is `PRA.qfInd`; no induction on quotient equality, sheafhood, or a
Cauchy predicate is used.
-/
