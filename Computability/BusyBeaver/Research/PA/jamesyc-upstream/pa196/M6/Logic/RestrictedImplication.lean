module

public section

namespace M6.Logic.RestrictedImplication

universe u v

/-- A proof interpretation of the restricted implicational axiom and modus ponens. -/
structure Rules {A : Type u} (imp : A → A → A) (le : A → A → Prop)
    (Proof : A → Type v) where
  mp {a b : A} : Proof (imp a b) → Proof a → Proof b
  row (a b c u : A) : le u a →
    Proof (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))
  refl (a : A) : le a a
  boundLeft {u a : A} (b : A) : le u a → le u (imp a b)
  boundRight {u b : A} (a : A) : le u b → le u (imp a b)

variable {A : Type u} {imp : A → A → A} {le : A → A → Prop} {Proof : A → Type v}
variable (rules : Rules imp le Proof)
local infixr:60 " ⟹ " => imp

/- Condensed detachment instantiates two proved formulas and applies modus
   ponens. Intermediate formulas from the derivation cited in
   formalization.yaml guided the search for these steps. -/

private def step1 (a b c : A) :
    Proof (((a ⟹ b) ⟹ b) ⟹ (b ⟹ a) ⟹ c ⟹ a) :=
  rules.row b c a b (rules.refl _)

private def step2 (a b c d : A) (h1 : le b c) :
    Proof (((a ⟹ b) ⟹ c) ⟹ (c ⟹ a) ⟹ d ⟹ a) :=
  rules.row c d a b (h1)

private def step3 (a b c d e : A) (h1 : le d a) :
    Proof ((((a ⟹ b) ⟹ c ⟹ b) ⟹ b ⟹ d) ⟹ e ⟹ b ⟹ d) :=
  rules.mp
    (step2 rules (b ⟹ d) a ((a ⟹ b) ⟹ c ⟹ b) e (rules.boundLeft _ (rules.boundLeft _ (rules.refl _))))
    (step2 rules b d a c (h1))

private def step4 (a b c d e f : A) (h1 : le c d) :
    Proof (((a ⟹ b ⟹ c) ⟹ (d ⟹ b) ⟹ e ⟹ b) ⟹ f ⟹ (d ⟹ b) ⟹ e ⟹ b) :=
  rules.mp
    (step2 rules ((d ⟹ b) ⟹ e ⟹ b) (b ⟹ c) (a ⟹ b ⟹ c) f (rules.boundRight _ (rules.refl _)))
    (step3 rules d b e c a (h1))

private def step5 (a b c d : A) :
    Proof (a ⟹ ((b ⟹ c) ⟹ b) ⟹ d ⟹ b) :=
  rules.mp
    (step4 rules (b ⟹ b ⟹ c) b c (b ⟹ c) d a (rules.boundRight _ (rules.refl _)))
    (step1 rules b (b ⟹ c) d)

private def step6 (a b c : A) :
    Proof (((a ⟹ b) ⟹ a) ⟹ c ⟹ a) :=
  rules.mp
    (step5 rules (((a ⟹ a) ⟹ a) ⟹ (a ⟹ a) ⟹ a ⟹ a) a b c)
    (step1 rules a a a)

private def step7 (a b c d : A) :
    Proof (((a ⟹ b) ⟹ b ⟹ c) ⟹ d ⟹ b ⟹ c) :=
  rules.mp
    (step2 rules (b ⟹ c) b (a ⟹ b) d (rules.boundRight _ (rules.refl _)))
    (step6 rules b c a)

private def step8 (a b c d e : A) :
    Proof (((a ⟹ b ⟹ c) ⟹ d ⟹ b) ⟹ e ⟹ d ⟹ b) :=
  rules.mp
    (step2 rules (d ⟹ b) (b ⟹ c) (a ⟹ b ⟹ c) e (rules.boundRight _ (rules.refl _)))
    (step7 rules d b c a)

private def step9 (a b c d : A) :
    Proof (a ⟹ (((b ⟹ c) ⟹ d) ⟹ c) ⟹ b ⟹ c) :=
  rules.mp
    (step8 rules (c ⟹ (b ⟹ c) ⟹ d) (b ⟹ c) d (((b ⟹ c) ⟹ d) ⟹ c) a)
    (step1 rules c ((b ⟹ c) ⟹ d) b)

private def step10 (a b c d e f : A) :
    Proof (((a ⟹ b ⟹ c) ⟹ d ⟹ c ⟹ e) ⟹ f ⟹ d ⟹ c ⟹ e) :=
  rules.mp
    (step2 rules (d ⟹ c ⟹ e) (b ⟹ c) (a ⟹ b ⟹ c) f (rules.boundRight _ (rules.refl _)))
    (step8 rules d c e b a)

private def step11 (a b c : A) :
    Proof ((((a ⟹ b) ⟹ c) ⟹ b) ⟹ a ⟹ b) :=
  rules.mp
    (step9 rules (((a ⟹ a) ⟹ a) ⟹ (a ⟹ a) ⟹ a ⟹ a) a b c)
    (step1 rules a a a)

private def step12 (a b c d : A) :
    Proof (((a ⟹ b) ⟹ (a ⟹ b) ⟹ c) ⟹ d ⟹ (a ⟹ b) ⟹ c) :=
  rules.mp
    (step2 rules ((a ⟹ b) ⟹ c) b (a ⟹ b) d (rules.boundRight _ (rules.refl _)))
    (step11 rules a b c)

/-- Introduce an antecedent that the conclusion does not use. -/
def k (a b : A) :
    Proof (a ⟹ b ⟹ a) :=
  rules.mp
    (step11 rules a (b ⟹ a) a)
    (step6 rules a (b ⟹ a) b)

private def step14 (a b c d : A) :
    Proof (((a ⟹ b ⟹ c) ⟹ b) ⟹ d ⟹ b) :=
  rules.mp
    (step2 rules b c (a ⟹ b ⟹ c) d (rules.boundRight _ (rules.boundRight _ (rules.refl _))))
    (k rules (b ⟹ c) a)

private def step15 (a b c : A) :
    Proof (a ⟹ ((b ⟹ c) ⟹ b) ⟹ b) :=
  rules.mp
    (step12 rules (b ⟹ c) b b a)
    (step6 rules b c ((b ⟹ c) ⟹ b))

/-- Peirce's law for classical implication. -/
def peirce (a b : A) :
    Proof (((a ⟹ b) ⟹ a) ⟹ a) :=
  rules.mp
    (step15 rules (((a ⟹ a) ⟹ a) ⟹ (a ⟹ a) ⟹ a ⟹ a) a b)
    (step1 rules a a a)

private def step17 (a b c : A) :
    Proof ((a ⟹ a ⟹ b) ⟹ c ⟹ a ⟹ b) :=
  rules.mp
    (step1 rules (a ⟹ b) a c)
    (peirce rules a b)

private def step18 (a b c : A) :
    Proof (a ⟹ (b ⟹ b ⟹ c) ⟹ b ⟹ c) :=
  rules.mp
    (step12 rules b (b ⟹ c) (b ⟹ c) a)
    (step17 rules b c (b ⟹ b ⟹ c))

private def step19 (a b : A) :
    Proof ((a ⟹ a ⟹ b) ⟹ a ⟹ b) :=
  rules.mp
    (step18 rules (((a ⟹ a) ⟹ a) ⟹ (a ⟹ a) ⟹ a ⟹ a) a b)
    (step1 rules a a a)

private def step20 (a b c : A) :
    Proof (((a ⟹ b ⟹ c) ⟹ b) ⟹ b) :=
  rules.mp
    (step19 rules ((a ⟹ b ⟹ c) ⟹ b) b)
    (step14 rules a b c ((a ⟹ b ⟹ c) ⟹ b))

private def step21 (a b c d : A) :
    Proof ((a ⟹ b ⟹ a ⟹ c) ⟹ d ⟹ b ⟹ a ⟹ c) :=
  rules.mp
    (step1 rules (b ⟹ a ⟹ c) a d)
    (step20 rules b a c)

private def step22 (a b c : A) :
    Proof ((a ⟹ b ⟹ a ⟹ c) ⟹ b ⟹ a ⟹ c) :=
  rules.mp
    (step19 rules (a ⟹ b ⟹ a ⟹ c) (b ⟹ a ⟹ c))
    (step21 rules a b c (a ⟹ b ⟹ a ⟹ c))

private def step23 (a b c : A) (h1 : le c a) :
    Proof ((a ⟹ b) ⟹ ((b ⟹ c) ⟹ a) ⟹ b) :=
  rules.mp
    (step22 rules ((b ⟹ c) ⟹ a) (a ⟹ b) b)
    (step2 rules b c a ((b ⟹ c) ⟹ a) (h1))

private def step24 (a b c d : A) (h1 : le d (b ⟹ b ⟹ c)) :
    Proof ((((a ⟹ b ⟹ c) ⟹ d) ⟹ b ⟹ b ⟹ c) ⟹ a ⟹ b ⟹ c) :=
  rules.mp
    (step23 rules (b ⟹ b ⟹ c) (a ⟹ b ⟹ c) d (h1))
    (step17 rules b c a)

private def step25 (a b c d : A) :
    Proof (a ⟹ ((b ⟹ c) ⟹ d) ⟹ c ⟹ d) :=
  rules.mp
    (step10 rules (d ⟹ b ⟹ c) b c ((b ⟹ c) ⟹ d) d a)
    (step1 rules d (b ⟹ c) c)

private def step26 (a b c : A) :
    Proof (((a ⟹ b) ⟹ c) ⟹ b ⟹ c) :=
  rules.mp
    (step25 rules (((a ⟹ a) ⟹ a) ⟹ (a ⟹ a) ⟹ a ⟹ a) a b c)
    (step1 rules a a a)

private def step27 (a b c : A) :
    Proof (a ⟹ (a ⟹ b) ⟹ c ⟹ b) :=
  rules.mp
    (step26 rules (b ⟹ a) a ((a ⟹ b) ⟹ c ⟹ b))
    (step1 rules b a c)

private def step28 (a b c : A) :
    Proof (a ⟹ b ⟹ c ⟹ a) :=
  rules.mp
    (step26 rules c a (b ⟹ c ⟹ a))
    (k rules (c ⟹ a) b)

private def step29 (a b c d : A) (h1 : le d c) :
    Proof ((((a ⟹ b ⟹ c) ⟹ d) ⟹ c) ⟹ a ⟹ b ⟹ c) :=
  rules.mp
    (step23 rules c (a ⟹ b ⟹ c) d (h1))
    (step28 rules c a b)

private def step30 (a b c d e : A) :
    Proof (((((a ⟹ b) ⟹ c) ⟹ d ⟹ c) ⟹ a) ⟹ e ⟹ a) :=
  rules.mp
    (step2 rules a b (((a ⟹ b) ⟹ c) ⟹ d ⟹ c) e
      (rules.boundLeft _ (rules.boundLeft _ (rules.boundRight _ (rules.refl _)))))
    (step27 rules (a ⟹ b) c d)

private def step31 (a b c d : A) (h1 : le d a) :
    Proof (((((a ⟹ b) ⟹ c ⟹ b) ⟹ d) ⟹ a) ⟹ (a ⟹ b) ⟹ c ⟹ b) :=
  rules.mp
    (step23 rules a ((a ⟹ b) ⟹ c ⟹ b) d (h1))
    (step27 rules a b c)

private def step32 (a b c d : A) :
    Proof (((((a ⟹ b) ⟹ c) ⟹ d ⟹ c) ⟹ a) ⟹ a) :=
  rules.mp
    (step19 rules ((((a ⟹ b) ⟹ c) ⟹ d ⟹ c) ⟹ a) a)
    (step30 rules a b c d ((((a ⟹ b) ⟹ c) ⟹ d ⟹ c) ⟹ a))

private def step33 (a b c d e : A) :
    Proof ((a ⟹ ((a ⟹ b) ⟹ c) ⟹ d ⟹ c) ⟹ e ⟹ ((a ⟹ b) ⟹ c) ⟹ d ⟹ c) :=
  rules.mp
    (step1 rules (((a ⟹ b) ⟹ c) ⟹ d ⟹ c) a e)
    (step32 rules a b c d)

private def step34 (a b c d e f : A) :
    Proof (((a ⟹ ((b ⟹ c) ⟹ d) ⟹ e ⟹ d) ⟹ b) ⟹ f ⟹ b) :=
  rules.mp
    (step2 rules b (((b ⟹ c) ⟹ d) ⟹ e ⟹ d) (a ⟹ ((b ⟹ c) ⟹ d) ⟹ e ⟹ d) f
      (rules.boundRight _ (rules.refl _)))
    (step33 rules b c d e a)

private def step35 (a b c d e : A) :
    Proof (((a ⟹ ((b ⟹ c) ⟹ d) ⟹ e ⟹ d) ⟹ b) ⟹ b) :=
  rules.mp
    (step19 rules ((a ⟹ ((b ⟹ c) ⟹ d) ⟹ e ⟹ d) ⟹ b) b)
    (step34 rules a b c d e ((a ⟹ ((b ⟹ c) ⟹ d) ⟹ e ⟹ d) ⟹ b))

private def step36 (a b c d : A) :
    Proof ((a ⟹ b ⟹ c) ⟹ ((a ⟹ d) ⟹ c) ⟹ b ⟹ c) :=
  rules.mp
    (step31 rules a (b ⟹ c) ((a ⟹ d) ⟹ c) a (rules.refl _))
    (step35 rules (a ⟹ b ⟹ c) a d c b)

private def step37 (a b c d : A) :
    Proof (((a ⟹ b) ⟹ c ⟹ d) ⟹ (a ⟹ d) ⟹ c ⟹ d) :=
  rules.mp
    (step36 rules a (a ⟹ d) (c ⟹ d) b)
    (step27 rules a d c)

private def step38 (a b c d : A) :
    Proof (a ⟹ b ⟹ (a ⟹ c) ⟹ d ⟹ c) :=
  rules.mp
    (step29 rules a b ((a ⟹ c) ⟹ d ⟹ c) (d ⟹ c) (rules.boundRight _ (rules.refl _)))
    (step37 rules a (b ⟹ (a ⟹ c) ⟹ d ⟹ c) d c)

private def step39 (a b : A) :
    Proof (a ⟹ (a ⟹ b) ⟹ b) :=
  rules.mp
    (step24 rules a (a ⟹ b) b ((a ⟹ b) ⟹ b) (rules.boundRight _ (rules.refl _)))
    (step37 rules a ((a ⟹ b) ⟹ b) (a ⟹ b) b)

private def step40 (a b c : A) :
    Proof (a ⟹ ((b ⟹ a) ⟹ c) ⟹ c) :=
  rules.mp
    (step26 rules b a (((b ⟹ a) ⟹ c) ⟹ c))
    (step39 rules (b ⟹ a) c)

private def step41 (a b c : A) :
    Proof (((a ⟹ b) ⟹ c) ⟹ (a ⟹ c) ⟹ c) :=
  rules.mp
    (step36 rules a (a ⟹ c) c b)
    (step39 rules a c)

private def step42 (a b c d : A) :
    Proof (((a ⟹ b) ⟹ c) ⟹ ((d ⟹ a) ⟹ c) ⟹ c) :=
  rules.mp
    (step36 rules a ((d ⟹ a) ⟹ c) c b)
    (step40 rules a d c)

private def step43 (a b c d : A) :
    Proof ((a ⟹ b) ⟹ ((c ⟹ a ⟹ d) ⟹ b) ⟹ b) :=
  rules.mp
    (step37 rules a d ((c ⟹ a ⟹ d) ⟹ b) b)
    (step40 rules (a ⟹ d) c b)

private def step44 (a b c d : A) :
    Proof ((a ⟹ b ⟹ c ⟹ a ⟹ d) ⟹ b ⟹ c ⟹ a ⟹ d) :=
  rules.mp
    (step41 rules a (c ⟹ a ⟹ d) (b ⟹ c ⟹ a ⟹ d))
    (step21 rules a c d b)

private def step45 (a b c : A) :
    Proof ((a ⟹ ((a ⟹ b) ⟹ c) ⟹ c) ⟹ ((a ⟹ b) ⟹ c) ⟹ c) :=
  rules.mp
    (step41 rules a b (((a ⟹ b) ⟹ c) ⟹ c))
    (step39 rules (a ⟹ b) c)

private def step46 (a b c : A) :
    Proof ((((a ⟹ b) ⟹ a ⟹ c) ⟹ b) ⟹ b) :=
  rules.mp
    (step45 rules (a ⟹ b) (a ⟹ c) b)
    (step43 rules a b (a ⟹ b) c)

private def step47 (a b c d : A) :
    Proof (((a ⟹ (b ⟹ c) ⟹ b ⟹ d) ⟹ c) ⟹ c) :=
  rules.mp
    (step42 rules ((b ⟹ c) ⟹ b ⟹ d) c c a)
    (step46 rules b c d)

private def step48 (a b c : A) :
    Proof ((a ⟹ b ⟹ c) ⟹ (b ⟹ a) ⟹ b ⟹ c) :=
  rules.mp
    (step31 rules a (b ⟹ c) (b ⟹ a) a (rules.refl _))
    (step47 rules (a ⟹ b ⟹ c) b a c)

private def step49 (a b c d : A) :
    Proof ((a ⟹ b) ⟹ a ⟹ (b ⟹ c) ⟹ d ⟹ c) :=
  rules.mp
    (step48 rules b a ((b ⟹ c) ⟹ d ⟹ c))
    (step38 rules b a c d)

private def step50 (a b c d : A) :
    Proof (a ⟹ (((a ⟹ b) ⟹ b) ⟹ c) ⟹ d ⟹ c) :=
  rules.mp
    (step49 rules a ((a ⟹ b) ⟹ b) c d)
    (step39 rules a b)

private def step51 (a b c : A) :
    Proof ((((a ⟹ b) ⟹ b) ⟹ c) ⟹ a ⟹ c) :=
  rules.mp
    (step22 rules a (((a ⟹ b) ⟹ b) ⟹ c) c)
    (step50 rules a b c a)

private def step52 (a b c d : A) :
    Proof (a ⟹ (a ⟹ b) ⟹ (b ⟹ c) ⟹ d ⟹ c) :=
  rules.mp
    (step51 rules a b ((a ⟹ b) ⟹ (b ⟹ c) ⟹ d ⟹ c))
    (step49 rules (a ⟹ b) b c d)

/-- Compose two implications. -/
def composition (a b c : A) :
    Proof ((a ⟹ b) ⟹ (b ⟹ c) ⟹ a ⟹ c) :=
  rules.mp
    (step44 rules a (a ⟹ b) (b ⟹ c) c)
    (step52 rules a b c a)

private def step54 (a b c d : A) :
    Proof ((((a ⟹ b) ⟹ c ⟹ b) ⟹ d) ⟹ (c ⟹ a) ⟹ d) :=
  rules.mp
    (composition rules (c ⟹ a) ((a ⟹ b) ⟹ c ⟹ b) d)
    (composition rules c a b)

private def step55 (a b c : A) :
    Proof ((a ⟹ b) ⟹ (a ⟹ b ⟹ c) ⟹ a ⟹ c) :=
  rules.mp
    (step54 rules b c a ((a ⟹ b ⟹ c) ⟹ a ⟹ c))
    (step48 rules (b ⟹ c) a c)

/-- Exchange two antecedents. -/
def exchange (a b c : A) :
    Proof ((a ⟹ b ⟹ c) ⟹ b ⟹ a ⟹ c) :=
  rules.mp
    (step54 rules (b ⟹ c) c a (b ⟹ a ⟹ c))
    (step51 rules b c (a ⟹ c))

/-- Distribute a common antecedent through modus ponens. -/
def s (a b c : A) :
    Proof ((a ⟹ b ⟹ c) ⟹ (a ⟹ b) ⟹ a ⟹ c) :=
  rules.mp
    (exchange rules (a ⟹ b) (a ⟹ b ⟹ c) (a ⟹ c))
    (step55 rules a b c)

/-- Prefix the same antecedent on both sides of a proved implication. -/
def liftRight {a b : A} (h : Proof (a ⟹ b)) (x : A) :
    Proof ((x ⟹ a) ⟹ x ⟹ b) :=
  let swap := rules.mp (exchange rules (x ⟹ a) (a ⟹ b) (x ⟹ b))
    (composition rules x a b)
  rules.mp swap h

/-- Peirce's law and composition give the unrestricted schema. -/
def rho8All (a b c u : A) :
    Proof (((c ⟹ u) ⟹ a) ⟹ (a ⟹ c) ⟹ b ⟹ c) :=
  let finish := rules.mp
    (rules.mp (composition rules ((c ⟹ u) ⟹ c) c (b ⟹ c)) (peirce rules c u))
    (k rules c b)
  let lifted := liftRight rules (liftRight rules finish (a ⟹ c)) ((c ⟹ u) ⟹ a)
  rules.mp lifted (composition rules (c ⟹ u) a c)

end M6.Logic.RestrictedImplication
