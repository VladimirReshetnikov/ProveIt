import BusyBeaver.ZFC.TarskiComplete

/-!
Finite implicational certificates and the unconditional Tarski logic bridge.

The 107 `cd_` certificates below port the published condensed-detachment
DAG in Jeff's `ZF/m254/coq/logic/CD254.v`, at busy-beaver commit
`297ab8df7e5de329605c3875b4934643b371a5e3` (Mira-Cult's machine; Jeff's
verification). They retain the source numbering. The original generator
is `ZF/m254/tools/logic/cdgen.py`; its uninstantiated proof-only variables
use numerical formula `0`. Here each such filler is the arbitrary local
formula `v0`; no conclusion contains that filler. No upstream Coq build,
proof search, implication injectivity, or assumption about falsity is used.
This is an attributed port of those proof certificates, not a relicensing
of the upstream snapshot, which declares no repository-wide license.

K, S, and Peirce need only modus ponens and rho8. Ex falso additionally
uses the original rho6, whose existential is defined relative to `NF.bot`.
Thus `Tarski.classical` supplies both explicit hypotheses of the previously
conditional `Tarski.completeness`, for any theory predicate `Ax`.

This concerns the named syntax with primitive falsity. It does not identify
that syntax with numerical machine codes, justify the runtime falsity
alias, verify a theory bundle, or prove a binary machine consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.Lukasiewicz

universe u
variable {α : Type u}

/-- Only the actual implicational row and its inference rule. -/
structure Implicational (imp : α → α → α) (T : α → Prop) : Prop where
  mp : ∀ {a b}, T (imp a b) → T a → T b
  rho8 : ∀ c u a b, T (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))

variable {imp : α → α → α} {T : α → Prop}

/-- Source certificates list the minor premise before the major premise. -/
private theorem detach (h : Implicational imp T) {a b : α}
    (ha : T a) (hab : T (imp a b)) : T b := h.mp hab ha

private theorem cd_0 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) v2) (imp (imp v2 v0) (imp v3 v0))) :=
  h.rho8 v0 v1 v2 v3

private theorem cd_1 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp (imp v0 v1) (imp v2 v1)) (imp v1 v3)) (imp v4 (imp v1 v3))) :=
  (detach h (cd_0 h v1 v3 v0 v2) (cd_0 h (imp v1 v3) v0 (imp (imp v0 v1) (imp v2 v1)) v4))

private theorem cd_2 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp (imp v1 v2) (imp v2 (imp v1 v2)))) :=
  (detach h (cd_1 h v0 v2 v1 (imp v1 v2) (imp v1 v2)) (cd_1 h (imp v0 v2) (imp v1 v2) v2 (imp v2 (imp v1 v2)) v0))

private theorem cd_3 (h : Implicational imp T) (v0 v1 : α) :
    T (imp (imp v0 v1) (imp v1 (imp v0 v1))) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_2 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1))

private theorem cd_4 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 (imp v1 v0)) v1) (imp v2 v1)) :=
  (detach h (cd_3 h v1 v0) (cd_0 h v1 v0 (imp v0 (imp v1 v0)) v2))

private theorem cd_5 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) (imp v2 (imp v1 v2))) (imp v3 (imp v2 (imp v1 v2)))) :=
  (detach h (cd_4 h v2 v1 v0) (cd_0 h (imp v2 (imp v1 v2)) v1 (imp v0 v1) v3))

private theorem cd_6 (h : Implicational imp T) (v0 v1 : α) :
    T (imp v0 (imp v1 (imp v1 v1))) :=
  (detach h (cd_3 h v1 v1) (cd_5 h v1 v1 v1 v0))

private theorem cd_7 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 (imp v0 v0)) v1) (imp v2 v1)) :=
  (detach h (cd_6 h (imp v1 v0) v0) (cd_0 h v1 v0 (imp v0 (imp v0 v0)) v2))

private theorem cd_8 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp (imp v1 v1) (imp v2 (imp v1 v1)))) :=
  (detach h (cd_7 h v1 (imp v2 (imp v1 v1)) (imp v1 v1)) (cd_1 h v1 (imp v1 v1) v2 (imp v2 (imp v1 v1)) v0))

private theorem cd_9 (h : Implicational imp T) (v0 v1 : α) :
    T (imp (imp v0 v0) (imp v1 (imp v0 v0))) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_8 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1))

private theorem cd_10 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 (imp v1 v1)) v1) (imp v2 v1)) :=
  (detach h (cd_9 h v1 v0) (cd_0 h v1 v1 (imp v0 (imp v1 v1)) v2))

private theorem cd_11 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) (imp v2 (imp v1 v1))) (imp v3 (imp v2 (imp v1 v1)))) :=
  (detach h (cd_10 h v2 v1 v0) (cd_0 h (imp v2 (imp v1 v1)) v1 (imp v0 v1) v3))

private theorem cd_12 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp v1 (imp v2 v2))) :=
  (detach h (cd_9 h v2 v1) (cd_11 h v2 v2 v1 v0))

private theorem cd_13 (h : Implicational imp T) (v0 v1 : α) :
    T (imp v0 (imp v1 v1)) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_12 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1))

private theorem cd_14 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 v0) v1) (imp v2 v1)) :=
  (detach h (cd_13 h (imp v1 v0) v0) (cd_0 h v1 v0 (imp v0 v0) v2))

private theorem cd_15 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp v1 (imp v2 v1))) :=
  (detach h (cd_14 h v1 (imp v2 v1) v1) (cd_1 h v1 v1 v2 (imp v2 v1) v0))

private theorem cd_16 (h : Implicational imp T) (v0 v1 : α) :
    T (imp v0 (imp v1 v0)) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_15 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1))

private theorem cd_17 (h : Implicational imp T) (v0 : α) :
    T (imp v0 v0) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_13 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0))

private theorem cd_18 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 v1) v0) (imp v2 v0)) :=
  (detach h (cd_17 h (imp v0 v1)) (cd_0 h v0 v1 (imp v0 v1) v2))

private theorem cd_19 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) (imp v1 v2)) (imp v3 (imp v1 v2))) :=
  (detach h (cd_18 h v1 v2 v0) (cd_0 h (imp v1 v2) v1 (imp v0 v1) v3))

private theorem cd_20 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp v0 (imp v1 v2)) (imp v3 v1)) (imp v4 (imp v3 v1))) :=
  (detach h (cd_19 h v3 v1 v2 v0) (cd_0 h (imp v3 v1) (imp v1 v2) (imp v0 (imp v1 v2)) v4))

private theorem cd_21 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp (imp (imp v1 v2) v3) v2) (imp v1 v2))) :=
  (detach h (cd_0 h v2 v0 (imp (imp v1 v2) v3) v1) (cd_20 h (imp v2 v0) (imp v1 v2) v3 (imp (imp (imp v1 v2) v3) v2) v0))

private theorem cd_22 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp (imp v0 v1) v2) v1) (imp v0 v1)) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_21 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2))

private theorem cd_23 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) (imp (imp v0 v1) v2)) (imp v3 (imp (imp v0 v1) v2))) :=
  (detach h (cd_22 h v0 v1 v2) (cd_0 h (imp (imp v0 v1) v2) v1 (imp v0 v1) v3))

private theorem cd_24 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp (imp (imp v1 v2) v1) v1)) :=
  (detach h (cd_18 h v1 v2 (imp (imp v1 v2) v1)) (cd_23 h (imp v1 v2) v1 v1 v0))

private theorem cd_25 (h : Implicational imp T) (v0 v1 : α) :
    T (imp (imp (imp v0 v1) v0) v0) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_24 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1))

private theorem cd_26 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 (imp v0 v1)) (imp v2 (imp v0 v1))) :=
  (detach h (cd_25 h v0 v1) (cd_0 h (imp v0 v1) v0 v0 v2))

private theorem cd_27 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp (imp v1 (imp v1 v2)) (imp v1 v2))) :=
  (detach h (cd_26 h v1 v2 (imp v1 (imp v1 v2))) (cd_23 h v1 (imp v1 v2) (imp v1 v2) v0))

private theorem cd_28 (h : Implicational imp T) (v0 v1 : α) :
    T (imp (imp v0 (imp v0 v1)) (imp v0 v1)) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_27 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1))

private theorem cd_29 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 v1) (imp v1 v2)) (imp v1 v2)) :=
  (detach h (cd_19 h v0 v1 v2 (imp (imp v0 v1) (imp v1 v2))) (cd_28 h (imp (imp v0 v1) (imp v1 v2)) (imp v1 v2)))

private theorem cd_30 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) (imp v2 v0)) (imp v3 (imp v2 v0))) :=
  (detach h (cd_29 h v2 v0 v1) (cd_0 h (imp v2 v0) (imp v0 v1) (imp v0 v1) v3))

private theorem cd_31 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp v1 (imp v2 v0))) :=
  (detach h (cd_30 h v0 (imp v1 (imp v2 v0)) v2 v1) (cd_22 h v0 (imp v1 (imp v2 v0)) (imp v2 v0)))

private theorem cd_32 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp v0 (imp v1 (imp v2 v3))) v2) (imp v4 v2)) :=
  (detach h (cd_31 h (imp v2 v3) v0 v1) (cd_0 h v2 v3 (imp v0 (imp v1 (imp v2 v3))) v4))

private theorem cd_33 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 (imp v1 (imp v2 v3))) v2) v2) :=
  (detach h (cd_32 h v0 v1 v2 v3 (imp (imp v0 (imp v1 (imp v2 v3))) v2)) (cd_28 h (imp (imp v0 (imp v1 (imp v2 v3))) v2) v2))

private theorem cd_34 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp v0 (imp v1 (imp v2 (imp v0 v3)))) (imp v4 (imp v1 (imp v2 (imp v0 v3))))) :=
  (detach h (cd_33 h v1 v2 v0 v3) (cd_0 h (imp v1 (imp v2 (imp v0 v3))) v0 v0 v4))

private theorem cd_35 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp v0 (imp v1 (imp v2 (imp v0 v3)))) (imp v1 (imp v2 (imp v0 v3)))) :=
  (detach h (cd_34 h v0 v1 v2 v3 (imp v0 (imp v1 (imp v2 (imp v0 v3))))) (cd_28 h (imp v0 (imp v1 (imp v2 (imp v0 v3)))) (imp v1 (imp v2 (imp v0 v3)))))

private theorem cd_36 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp v0 v1) (imp v1 (imp v0 v1))) v2) (imp v3 v2)) :=
  (detach h (cd_2 h (imp v2 v0) v0 v1) (cd_0 h v2 v0 (imp (imp v0 v1) (imp v1 (imp v0 v1))) v3))

private theorem cd_37 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp (imp v1 (imp v2 v1)) v2) (imp v3 v2))) :=
  (detach h (cd_0 h v2 v1 (imp v1 (imp v2 v1)) v3) (cd_36 h v2 v1 (imp (imp (imp v1 (imp v2 v1)) v2) (imp v3 v2)) v0))

private theorem cd_38 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp (imp (imp v0 (imp v1 v0)) v1) (imp v2 v1)) v3) (imp v4 v3)) :=
  (detach h (cd_37 h (imp v3 v0) v0 v1 v2) (cd_0 h v3 v0 (imp (imp (imp v0 (imp v1 v0)) v1) (imp v2 v1)) v4))

private theorem cd_39 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp v1 v2) (imp v3 (imp v1 v2)))) :=
  (detach h (cd_38 h v0 v2 v1 (imp v3 (imp v1 v2)) (imp v1 v2)) (cd_1 h (imp (imp v0 (imp v2 v0)) v2) (imp v1 v2) v3 (imp v3 (imp v1 v2)) v0))

private theorem cd_40 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 v1) (imp v2 (imp v0 v1))) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_39 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2))

private theorem cd_41 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 (imp v1 v2)) v1) (imp v3 v1)) :=
  (detach h (cd_40 h v1 v2 v0) (cd_0 h v1 v2 (imp v0 (imp v1 v2)) v3))

private theorem cd_42 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp (imp v1 (imp v2 v3)) v2) v2)) :=
  (detach h (cd_41 h v1 v2 v3 (imp (imp v1 (imp v2 v3)) v2)) (cd_23 h (imp v1 (imp v2 v3)) v2 v2 v0))

private theorem cd_43 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 (imp v1 v2)) v1) v1) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_42 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2))

private theorem cd_44 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp v0 (imp v1 (imp v0 v2))) (imp v3 (imp v1 (imp v0 v2)))) :=
  (detach h (cd_43 h v1 v0 v2) (cd_0 h (imp v1 (imp v0 v2)) v0 v0 v3))

private theorem cd_45 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 (imp v1 (imp v0 v2))) (imp v1 (imp v0 v2))) :=
  (detach h (cd_44 h v0 v1 v2 (imp v0 (imp v1 (imp v0 v2)))) (cd_28 h (imp v0 (imp v1 (imp v0 v2))) (imp v1 (imp v0 v2))))

private theorem cd_46 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp v1 v2) (imp (imp (imp v2 v3) v1) v2))) :=
  (detach h (cd_0 h v2 v3 v1 (imp (imp v2 v3) v1)) (cd_44 h (imp (imp v2 v3) v1) (imp v1 v2) v2 v0))

private theorem cd_47 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 v1) (imp (imp (imp v1 v2) v0) v1)) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_46 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2))

private theorem cd_48 (h : Implicational imp T) (v0 v1 v2 v3 v4 v5 : α) :
    T (imp (imp (imp v0 (imp v1 v2)) (imp v3 (imp v2 v4))) (imp v5 (imp v3 (imp v2 v4)))) :=
  (detach h (cd_20 h v3 v2 v4 v1 v0) (cd_0 h (imp v3 (imp v2 v4)) (imp v1 v2) (imp v0 (imp v1 v2)) v5))

private theorem cd_49 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp (imp v1 v2) v3) (imp v2 v3))) :=
  (detach h (cd_0 h v3 v0 (imp v1 v2) v2) (cd_48 h (imp v3 v0) v1 v2 (imp (imp v1 v2) v3) v3 v0))

private theorem cd_50 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 v1) v2) (imp v1 v2)) :=
  (detach h (cd_0 h v0 v0 v0 v0) (cd_49 h (imp (imp (imp v0 v0) v0) (imp (imp v0 v0) (imp v0 v0))) v0 v1 v2))

private theorem cd_51 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp (imp v0 v1) (imp v2 v1))) :=
  (detach h (cd_0 h v1 v0 v0 v2) (cd_50 h (imp v1 v0) v0 (imp (imp v0 v1) (imp v2 v1))))

private theorem cd_52 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) v0) (imp (imp v0 v1) (imp v2 v1))) :=
  (detach h (cd_51 h v0 v1 v2) (cd_47 h v0 (imp (imp v0 v1) (imp v2 v1)) v3))

private theorem cd_53 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp v0 v1) v2) (imp (imp v1 v3) v1)) (imp v0 v1)) :=
  (detach h (cd_18 h v1 v3 v0) (cd_47 h (imp (imp v1 v3) v1) (imp v0 v1) v2))

private theorem cd_54 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp (imp v0 v1) v2) (imp (imp v3 (imp v1 v4)) v1)) (imp v0 v1)) :=
  (detach h (cd_41 h v3 v1 v4 v0) (cd_47 h (imp (imp v3 (imp v1 v4)) v1) (imp v0 v1) v2))

private theorem cd_55 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) (imp v4 v0)) :=
  (detach h (cd_51 h (imp v0 v1) v2 v3) (cd_0 h v0 v1 (imp (imp (imp v0 v1) v2) (imp v3 v2)) v4))

private theorem cd_56 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) v0) :=
  (detach h (cd_55 h v0 v1 v2 v3 (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0)) (cd_28 h (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) v0))

private theorem cd_57 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v4) v2) (imp v1 v2)) :=
  (detach h (cd_56 h (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v4 v2 v1) (cd_54 h (imp (imp (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v4) v2) (imp v1 v2) (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v0 v3))

private theorem cd_58 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 (imp (imp (imp v1 v2) v1) v3)) (imp (imp v1 v2) v1)) v1) :=
  (detach h (cd_57 h v0 (imp v1 v2) v1 v3 v1) (cd_53 h (imp (imp v0 (imp (imp (imp v1 v2) v1) v3)) (imp (imp v1 v2) v1)) v1 v1 v2))

private theorem cd_59 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 v1) (imp (imp (imp v0 v2) v0) v1)) :=
  (detach h (cd_58 h (imp v0 v1) v0 v2 v1) (cd_52 h v0 v1 (imp (imp v0 v2) v0) (imp (imp v0 v2) v0)))

private theorem cd_60 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp v0 (imp v1 v2)) v3) (imp v1 (imp v1 v2))) (imp v0 (imp v1 v2))) :=
  (detach h (cd_26 h v1 v2 v0) (cd_47 h (imp v1 (imp v1 v2)) (imp v0 (imp v1 v2)) v3))

private theorem cd_61 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) v0) (imp (imp v0 v2) (imp v3 v2))) :=
  (detach h (cd_51 h v0 v2 v3) (cd_59 h v0 (imp (imp v0 v2) (imp v3 v2)) v1))

private theorem cd_62 (h : Implicational imp T) (v0 v1 : α) :
    T (imp v0 (imp (imp v0 v1) v1)) :=
  (detach h (cd_61 h v0 (imp (imp v0 v1) v1) v1 (imp v0 v1)) (cd_60 h v0 (imp v0 v1) v1 v0))

private theorem cd_63 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 v1) v0) (imp (imp v0 v2) v2)) :=
  (detach h (cd_62 h v0 v2) (cd_59 h v0 (imp (imp v0 v2) v2) v1))

private theorem cd_64 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp v0 v1) v1) (imp v0 v2)) (imp v3 (imp v0 v2))) :=
  (detach h (cd_63 h v0 v2 v1) (cd_0 h (imp v0 v2) v0 (imp (imp v0 v1) v1) v3))

private theorem cd_65 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp (imp v0 v1) v1) (imp v0 v2)) (imp v0 v2)) :=
  (detach h (cd_64 h v0 v1 v2 (imp (imp (imp v0 v1) v1) (imp v0 v2))) (cd_28 h (imp (imp (imp v0 v1) v1) (imp v0 v2)) (imp v0 v2)))

private theorem cd_66 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp v0 (imp v1 v2)) v3) v2) (imp v0 (imp v1 v2))) :=
  (detach h (cd_31 h v2 v0 v1) (cd_47 h v2 (imp v0 (imp v1 v2)) v3))

private theorem cd_67 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp v1 (imp (imp v0 v2) (imp v3 v2)))) :=
  (detach h (cd_61 h v0 (imp v1 (imp (imp v0 v2) (imp v3 v2))) v2 v3) (cd_66 h v0 v1 (imp (imp v0 v2) (imp v3 v2)) v0))

private theorem cd_68 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp (imp (imp v0 v1) v1) v2) (imp v3 v2))) :=
  (detach h (cd_67 h (imp (imp v0 v1) v1) v0 v2 v3) (cd_65 h v0 v1 (imp (imp (imp (imp v0 v1) v1) v2) (imp v3 v2))))

private theorem cd_69 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp (imp v0 v1) v1) v2) (imp v0 v2)) :=
  (detach h (cd_68 h v0 v1 v2 v0) (cd_45 h v0 (imp (imp (imp v0 v1) v1) v2) v2))

private theorem cd_70 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp v0 v1) (imp v2 (imp v1 v3))) (imp v4 (imp v2 (imp v1 v3)))) :=
  (detach h (cd_41 h v2 v1 v3 v0) (cd_0 h (imp v2 (imp v1 v3)) v1 (imp v0 v1) v4))

private theorem cd_71 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) (imp v2 (imp v1 v3))) (imp v2 (imp v1 v3))) :=
  (detach h (cd_70 h v0 v1 v2 v3 (imp (imp v0 v1) (imp v2 (imp v1 v3)))) (cd_28 h (imp (imp v0 v1) (imp v2 (imp v1 v3))) (imp v2 (imp v1 v3))))

private theorem cd_72 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp v0 (imp v1 (imp (imp (imp v2 v0) v3) (imp v4 v3)))) :=
  (detach h (cd_67 h (imp v2 v0) v1 v3 v4) (cd_50 h v2 v0 (imp v1 (imp (imp (imp v2 v0) v3) (imp v4 v3)))))

private theorem cd_73 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp v0 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) (imp v4 v3))) :=
  (detach h (cd_72 h (imp (imp v0 v2) v2) v0 v1 v3 v4) (cd_65 h v0 v2 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) (imp v4 v3))))

private theorem cd_74 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v4) (imp v2 v4)) :=
  (detach h (cd_73 h (imp v1 v2) v0 v3 v4 v2) (cd_71 h v1 v2 (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v4) v4))

private theorem cd_75 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 v1) v2) (imp (imp (imp v3 v0) v2) v2)) :=
  (detach h (cd_74 h (imp (imp v0 v1) v2) v3 v0 v2 v1) (cd_52 h (imp v0 v1) v2 (imp (imp v3 v0) v2) v1))

private theorem cd_76 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp (imp (imp v0 v1) v1) v2) v0) (imp (imp v0 v1) v1)) :=
  (detach h (cd_62 h v0 v1) (cd_47 h v0 (imp (imp v0 v1) v1) v2))

private theorem cd_77 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp v0 v1) (imp v2 v0)) (imp v2 v0)) :=
  (detach h (cd_30 h v0 v1 v2 (imp (imp v0 v1) (imp v2 v0))) (cd_28 h (imp (imp v0 v1) (imp v2 v0)) (imp v2 v0)))

private theorem cd_78 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp v1 (imp (imp v0 v2) v2))) :=
  (detach h (cd_63 h v0 (imp v1 (imp (imp v0 v2) v2)) v2) (cd_66 h v0 v1 (imp (imp v0 v2) v2) v0))

private theorem cd_79 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp v1 (imp (imp (imp v2 v0) v3) v3))) :=
  (detach h (cd_78 h (imp v2 v0) v1 v3) (cd_50 h v2 v0 (imp v1 (imp (imp (imp v2 v0) v3) v3))))

private theorem cd_80 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) v3)) :=
  (detach h (cd_79 h (imp (imp v0 v2) v2) v0 v1 v3) (cd_65 h v0 v2 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) v3)))

private theorem cd_81 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v1) v1) :=
  (detach h (cd_80 h (imp v1 v2) v0 v3 v1) (cd_77 h v1 v2 (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v1)))

private theorem cd_82 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 (imp (imp (imp v0 v1) v2) v2)) (imp (imp (imp v0 v1) v2) v2)) :=
  (detach h (cd_81 h (imp v0 (imp (imp (imp v0 v1) v2) v2)) v0 v1 v2) (cd_76 h v0 (imp (imp (imp v0 v1) v2) v2) v0))

private theorem cd_83 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 (imp v1 v2)) (imp v3 v1)) (imp v3 v1)) :=
  (detach h (cd_20 h v0 v1 v2 v3 (imp (imp v0 (imp v1 v2)) (imp v3 v1))) (cd_28 h (imp (imp v0 (imp v1 v2)) (imp v3 v1)) (imp v3 v1)))

private theorem cd_84 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v4) v4)) v2) v2) :=
  (detach h (cd_80 h (imp v1 (imp v2 v3)) v0 v4 v2) (cd_83 h v1 v2 v3 (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v4) v4)) v2)))

private theorem cd_85 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp v0 v1) (imp (imp (imp v2 (imp v0 v3)) v1) v1)) :=
  (detach h (cd_84 h (imp v0 v1) v2 v0 v3 v1) (cd_52 h v0 v1 (imp (imp v2 (imp v0 v3)) v1) v0))

private theorem cd_86 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp (imp (imp v0 v1) (imp v0 v2)) v1) v1) :=
  (detach h (cd_85 h v0 v1 (imp v0 v1) v2) (cd_82 h (imp v0 v1) (imp v0 v2) v1))

private theorem cd_87 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp v0 (imp (imp v1 v2) (imp v1 v3))) v2) v2) :=
  (detach h (cd_86 h v1 v2 v3) (cd_75 h (imp (imp v1 v2) (imp v1 v3)) v2 v2 v0))

private theorem cd_88 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 (imp v1 v2)) (imp (imp v1 v0) (imp v1 v2))) :=
  (detach h (cd_87 h (imp v0 (imp v1 v2)) v1 v0 v2) (cd_52 h v0 (imp v1 v2) (imp v1 v0) v0))

private theorem cd_89 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp v0 v1) (imp v0 (imp (imp v1 v2) (imp v3 v2)))) :=
  (detach h (cd_67 h v1 v0 v2 v3) (cd_88 h v1 v0 (imp (imp v1 v2) (imp v3 v2))))

private theorem cd_90 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp v0 v1) (imp (imp v1 v2) (imp v3 v2)))) :=
  (detach h (cd_89 h (imp v0 v1) v1 v2 v3) (cd_69 h v0 v1 (imp (imp v0 v1) (imp (imp v1 v2) (imp v3 v2)))))

private theorem cd_91 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 v1) (imp (imp v1 v2) (imp v0 v2))) :=
  (detach h (cd_90 h v0 v1 v2 v0) (cd_35 h v0 (imp v0 v1) (imp v1 v2) v2))

private theorem cd_92 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp v0 (imp (imp (imp v1 v0) v2) v2)) :=
  (detach h (cd_62 h (imp v1 v0) v2) (cd_50 h v1 v0 (imp (imp (imp v1 v0) v2) v2)))

private theorem cd_93 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1) (imp v4 v1)) :=
  (detach h (cd_92 h (imp v1 v2) v0 v3) (cd_0 h v1 v2 (imp (imp (imp v0 (imp v1 v2)) v3) v3) v4))

private theorem cd_94 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1) v1) :=
  (detach h (cd_93 h v0 v1 v2 v3 (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1)) (cd_28 h (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1) v1))

private theorem cd_95 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v2) v4)) v2) v2) :=
  (detach h (cd_94 h v0 (imp (imp v1 (imp v2 v3)) v2) v4 v2) (cd_54 h (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v2) v4)) v2) v2 (imp (imp v1 (imp v2 v3)) v2) v1 v3))

private theorem cd_96 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp v0 v1) (imp (imp (imp v2 (imp v0 v3)) v0) v1)) :=
  (detach h (cd_95 h (imp v0 v1) v2 v0 v3 v1) (cd_52 h v0 v1 (imp (imp v2 (imp v0 v3)) v0) v0))

private theorem cd_97 (h : Implicational imp T) (v0 v1 v2 v3 v4 : α) :
    T (imp (imp (imp v0 (imp v1 v2)) v1) (imp (imp v1 v3) (imp v4 v3))) :=
  (detach h (cd_51 h v1 v3 v4) (cd_96 h v1 (imp (imp v1 v3) (imp v4 v3)) v0 v2))

private theorem cd_98 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) (imp v0 v3)) :=
  (detach h (cd_97 h (imp (imp (imp v0 v1) (imp v2 v1)) v3) v0 v3 v1 v2) (cd_52 h (imp (imp v0 v1) (imp v2 v1)) v3 v0 v0))

private theorem cd_99 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 v1) (imp v0 (imp v2 v1))) :=
  (detach h (cd_69 h v0 v1 (imp v2 v1)) (cd_98 h (imp v0 v1) v1 v2 (imp v0 (imp v2 v1))))

private theorem cd_100 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp v0 v1) (imp v2 (imp v0 (imp v3 v1)))) :=
  (detach h (cd_99 h v0 v1 v3) (cd_99 h (imp v0 v1) (imp v0 (imp v3 v1)) v2))

private theorem cd_101 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp v0 (imp v1 v2)) (imp v0 (imp v1 (imp v3 v2)))) :=
  (detach h (cd_100 h v1 v2 v0 v3) (cd_88 h (imp v1 v2) v0 (imp v1 (imp v3 v2))))

private theorem cd_102 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp v0 (imp (imp v0 (imp v1 v2)) (imp v1 (imp v3 v2)))) :=
  (detach h (cd_101 h (imp v0 (imp v1 v2)) v1 v2 v3) (cd_69 h v0 (imp v1 v2) (imp (imp v0 (imp v1 v2)) (imp v1 (imp v3 v2)))))

private theorem cd_103 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 (imp v1 v2)) (imp v1 (imp v0 v2))) :=
  (detach h (cd_102 h v0 v1 v2 v0) (cd_35 h v0 (imp v0 (imp v1 v2)) v1 v2))

private theorem cd_104 (h : Implicational imp T) (v0 v1 v2 v3 : α) :
    T (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) (imp (imp v2 v0) v3)) :=
  (detach h (cd_91 h v2 v0 v1) (cd_91 h (imp v2 v0) (imp (imp v0 v1) (imp v2 v1)) v3))

private theorem cd_105 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 v1) (imp (imp v0 (imp v1 v2)) (imp v0 v2))) :=
  (detach h (cd_88 h (imp v1 v2) v0 v2) (cd_104 h v1 v2 v0 (imp (imp v0 (imp v1 v2)) (imp v0 v2))))

private theorem cd_106 (h : Implicational imp T) (v0 v1 v2 : α) :
    T (imp (imp v0 (imp v1 v2)) (imp (imp v0 v1) (imp v0 v2))) :=
  (detach h (cd_105 h v0 v1 v2) (cd_103 h (imp v0 v1) (imp v0 (imp v1 v2)) (imp v0 v2)))

/-- K follows from rho8 alone (source certificate 16). -/
theorem k (h : Implicational imp T) (a b : α) : T (imp a (imp b a)) :=
  cd_16 h a b

/-- Peirce follows from rho8 alone (source certificate 25). -/
theorem peirce (h : Implicational imp T) (a b : α) :
    T (imp (imp (imp a b) a) a) := cd_25 h a b

/-- Implication composition (source certificate 91). -/
theorem composition (h : Implicational imp T) (a b c : α) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) := cd_91 h a b c

/-- S follows from rho8 alone (source certificate 106). -/
theorem s (h : Implicational imp T) (a b c : α) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := cd_106 h a b c

end SetTheory.BusyBeaver.ZFC.Lukasiewicz

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF

private theorem implicational (Ax : NF → Prop) :
    Lukasiewicz.Implicational NF.imp (Thm Ax) where
  mp := Thm.mp
  rho8 := Thm.rho8

/-- Ex falso uses K, S and the original rho6, not rho8 alone. -/
theorem ex_falso {Ax : NF → Prop} (a : NF) : Thm Ax (imp bot a) := by
  let x := all 0 (neg (all 0 a))
  let e := ex 0 (all 0 a)
  have hk := Lukasiewicz.k (implicational Ax)
  have hs := Lukasiewicz.s (implicational Ax)
  have hbe : Thm Ax (imp bot e) := hk bot x
  have hbea : Thm Ax (imp bot (imp e a)) :=
    .mp (hk (imp e a) bot) (.rho6 0 a)
  exact .mp (.mp (hs bot e a) hbea) hbe

/-- The required classical basis is derived from the actual Tarski rows. -/
theorem classical (Ax : NF → Prop) : Kalmar.Classical NF.imp NF.bot (Thm Ax) where
  mp := Thm.mp
  k := Lukasiewicz.k (implicational Ax)
  s := Lukasiewicz.s (implicational Ax)
  peirce := Lukasiewicz.peirce (implicational Ax)
  efq := ex_falso

/-- Unconditional completeness for named formulas with primitive falsity. -/
theorem complete {Ax : NF → Prop} (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) → ∀ e : Nat → D, Sat mem e f) :
    Thm Ax f :=
  completeness (classical Ax) (classical (fun _ => False)) f hval

end SetTheory.BusyBeaver.ZFC.Tarski
