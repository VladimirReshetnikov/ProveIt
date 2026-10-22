import BusyBeaver.ZFC.L2Dom
import BusyBeaver.ZFC.EnumDom

/-!
The AX routine of `dagDom` (node 236) as a checked word of register macros.

Each atom is a macro node whose run contract `L2Dom` transfers from `dag222`. One induction
composes the contracts along the word, a kernel check binds the word to the literal program,
and symbolic evaluation identifies its complete effect with EnumDom's AX step (`ax_eval`).
-/

namespace SetTheory.BusyBeaver.ZFC.L2Dom

open RMDag DagDom Code254 KCode222
open L2K (AS enc Clean ofNat_P)

attribute [local irreducible] Code254.P

set_option maxRecDepth 4096

/-- Push `x`, saving the current formula. -/
def pushA (x : Nat) (st : AS) : AS := { st with tw := x, ws := P st.tw st.ws }

/-- Pop a formula and combine it with the current one. -/
def popA (op : Nat → Nat → Nat) (st : AS) : AS :=
  { st with tw := op (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }

/-- The gate: clear the bundle when `c = b` or `c = a`, and clear `axiomcode`, `param1`,
`param2`. -/
def gateF (st : AS) : AS :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

theorem l457 (st : AS) (hc : Clean st) : Rn (.node 457) st (gateF st) := by
  have := seqAS (n := 457) rfl (loop192 st) (seqAS (n := 458) rfl (ifeq_clear _)
    (seqAS (n := 459) rfl (loop211 _) (seqAS (n := 460) rfl (loop197 _) (ifeq_clear _))))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st
  simp only at h1 h2
  subst h1; subst h2
  simp only [gateF, Nat.zero_add]
  split <;> split <;> simp_all <;> omega

/-- The register macros of the AX word. -/
inductive AXAtom where
  | par1 | par2 | par3 | push | cons | wel | wal | weq | wn | wa | wex | readp2 | readp1

def AXAtom.node : AXAtom → Nat
  | .par1 => 166 | .par2 => 121 | .par3 => 168 | .push => 171 | .cons => 119 | .wel => 181
  | .wal => 180 | .weq => 182 | .wn => 218 | .wa => 178 | .wex => 183 | .readp2 => 176
  | .readp1 => 175

def AXAtom.effect : AXAtom → AS → AS
  | .par1, st => pushA st.p1 st
  | .par2, st => pushA st.p2 st
  | .par3, st => pushA st.ac st
  | .push, st => pushA 0 st
  | .cons, st => popA Code254.wim st
  | .wel, st => popA Code254.wel st
  | .wal, st => popA Code254.wal st
  | .weq, st => popA Code254.weq st
  | .wa, st => popA Code254.wa st
  | .wex, st => popA Code254.wex st
  | .wn, st => { st with tw := Code254.wn st.tw }
  | .readp2, st => { st with pl := (Cantor.ofNat st.pl).2, p2 := st.p2 + (Cantor.ofNat st.pl).1 }
  | .readp1, st => { st with pl := (Cantor.ofNat st.pl).2, p1 := st.p1 + (Cantor.ofNat st.pl).1 }

theorem AXAtom.run (st : AS) (hc : Clean st) : ∀ a : AXAtom, Rn (.node a.node) st (a.effect st)
  | .par1 => L2Dom.par1 st hc
  | .par2 => L2Dom.par2 st hc
  | .par3 => L2Dom.par3 st hc
  | .push => L2Dom.pushwff st hc
  | .cons => L2Dom.cons st hc
  | .wel => L2Dom.wel_m st hc
  | .wal => L2Dom.wal_m st hc
  | .weq => L2Dom.weq_m st hc
  | .wn => L2Dom.wn_m st hc
  | .wa => L2Dom.wa_m st hc
  | .wex => L2Dom.wex_m st hc
  | .readp2 => L2Dom.read_p2 st hc
  | .readp1 => L2Dom.read_p1 st hc

/-- Each pair names a macro and the next program node; the suffix is the gate. -/
def axWordCheck : Nat → List (AXAtom × Nat) → Bool
  | n, [] => decide (n = 457)
  | n, (a, next) :: rest =>
    decide (dagDom.nodes n = (.node a.node, .node next)) && axWordCheck next rest

def axWordEval : List (AXAtom × Nat) → AS → AS
  | [], st => gateF st
  | (a, _) :: rest, st => axWordEval rest (a.effect st)

/-- No macro touches the scratch registers. -/
theorem axWordClean (word : List (AXAtom × Nat)) (st : AS) (hc : Clean st) :
    Clean (axWordEval word st) := by
  induction word generalizing st with
  | nil => exact hc
  | cons a rest ih => exact ih _ (by cases a.1 <;> exact hc)

theorem axWordRun (word : List (AXAtom × Nat)) {n : Nat}
    (h : axWordCheck n word = true) (st : AS) (hc : Clean st) :
    Rn (.node n) st (axWordEval word st) := by
  induction word generalizing n st with
  | nil =>
    simp only [axWordCheck, decide_eq_true_eq] at h
    subst n
    exact l457 st hc
  | cons a rest ih =>
    rcases a with ⟨a, next⟩
    simp only [axWordCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact seqAS h.1 (AXAtom.run st hc a) (ih h.2 _ (by cases a <;> exact hc))

def axWord : List (AXAtom × Nat) := [
  (.par1, 467), (.par2, 468), (.wal, 469), (.par3, 470), (.par1, 471), (.readp2, 472),
  (.readp1, 473), (.cons, 474), (.par1, 475), (.cons, 476), (.par1, 477), (.par3, 478),
  (.cons, 479), (.par2, 480), (.par3, 481), (.cons, 482), (.cons, 483), (.cons, 319),
  (.par3, 320), (.par1, 321), (.weq, 322), (.par3, 323), (.par2, 324), (.weq, 325),
  (.par1, 326), (.par2, 327), (.wel, 328), (.par1, 329), (.par2, 330), (.weq, 331),
  (.wal, 332), (.cons, 333), (.cons, 334), (.par1, 335), (.par1, 336), (.par3, 337),
  (.wal, 338), (.wex, 339), (.par3, 340), (.cons, 341), (.par3, 342), (.par1, 343),
  (.weq, 344), (.par3, 345), (.par2, 346), (.wel, 347), (.par1, 348), (.par2, 349),
  (.wel, 350), (.cons, 351), (.cons, 352), (.par1, 353), (.par2, 354), (.par3, 355),
  (.wal, 356), (.wal, 357), (.par2, 358), (.par1, 359), (.par3, 360), (.wal, 361),
  (.wal, 362), (.cons, 363), (.par1, 364), (.par2, 365), (.weq, 366), (.par3, 367),
  (.par1, 368), (.wel, 369), (.par3, 370), (.par2, 371), (.wel, 372), (.cons, 373),
  (.cons, 374), (.par1, 375), (.par2, 376), (.par3, 377), (.cons, 378), (.wal, 379),
  (.par1, 380), (.par2, 381), (.wal, 382), (.par1, 383), (.par3, 384), (.wal, 385),
  (.cons, 386), (.cons, 387), (.par1, 388), (.par1, 389), (.par2, 390), (.weq, 391),
  (.wex, 392), (.par1, 393), (.par2, 394), (.wel, 395), (.par3, 396), (.par1, 397),
  (.par2, 398), (.wel, 399), (.wal, 400), (.cons, 401), (.par3, 402), (.par2, 403),
  (.par2, 404), (.par3, 405), (.wel, 406), (.par1, 407), (.par3, 408), (.par1, 409),
  (.par3, 410), (.par3, 411), (.par1, 412), (.wel, 413), (.par3, 414), (.par2, 415),
  (.wel, 416), (.cons, 417), (.wal, 418), (.par2, 419), (.par3, 420), (.par2, 421),
  (.par3, 422), (.par2, 423), (.par3, 424), (.wel, 425), (.wn, 426), (.cons, 427),
  (.wal, 428), (.wn, 429), (.cons, 430), (.wal, 431), (.cons, 432), (.wal, 433),
  (.wn, 434), (.cons, 435), (.wal, 436), (.wn, 437), (.cons, 438), (.wal, 439),
  (.par2, 440), (.par3, 441), (.par2, 442), (.par3, 443), (.par2, 444), (.par3, 445),
  (.wel, 446), (.wn, 447), (.cons, 448), (.wal, 449), (.wn, 450), (.cons, 451),
  (.wal, 452), (.wn, 453), (.cons, 454), (.wal, 455), (.cons, 456), (.wn, 457)]

theorem axWord_checked : axWordCheck 236 axWord = true := by decide +kernel

def f236 (st : AS) : AS := axWordEval axWord st
theorem l236 (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  axWordRun axWord axWord_checked st hc
theorem c236 (st : AS) (hc : Clean st) : Clean (f236 st) := axWordClean axWord st hc

/-- **The AX routine is EnumDom's AX step.** -/
theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumDom.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        EnumDom.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a
          t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  simp only [f236, axWord, axWordEval, AXAtom.effect, pushA, popA, gateF, ofNat_P,
    EnumDom.gate, EnumDom.axStack, bundle222, nks, clos, req, vrel, growG,
    rho1, rho2, rho3, rho4, rho5, rho6, rho8, wex]

#print axioms l236
#print axioms ax_eval
end SetTheory.BusyBeaver.ZFC.L2Dom
