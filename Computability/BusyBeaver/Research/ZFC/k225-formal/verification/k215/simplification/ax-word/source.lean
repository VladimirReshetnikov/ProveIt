import BusyBeaver.ZFC.L2Perm
import BusyBeaver.ZFC.EnumPerm

/-!
The AX routine as a checked word of existing register macros.
One induction composes their run contracts. The literal word is checked against
dagPerm, and symbolic evaluation identifies its complete effect with EnumPerm.
-/

namespace SetTheory.BusyBeaver.ZFC.L2Perm

open RMDag DagPerm Code254 KCode222
open L2K (AS enc Clean ofNat_P)

attribute [local irreducible] Code254.P

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

def pushF (st : AS) : AS := { st with tw := 0, ws := P st.tw st.ws }
def par1F (st : AS) : AS := { st with tw := st.p1, ws := P st.tw st.ws }
def par2F (st : AS) : AS := { st with tw := st.p2, ws := P st.tw st.ws }
def par3F (st : AS) : AS := { st with tw := st.ac, ws := P st.tw st.ws }
def consF (st : AS) : AS :=
  { st with tw := wim (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def welF (st : AS) : AS :=
  { st with tw := wel (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def walF (st : AS) : AS :=
  { st with tw := wal (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def weqF (st : AS) : AS :=
  { st with tw := weq (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def wnF (st : AS) : AS := { st with tw := wn st.tw }
def waF (st : AS) : AS :=
  { st with tw := wa (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def wexF (st : AS) : AS :=
  { st with tw := wex (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def readp2F (st : AS) : AS :=
  { st with pl := (Cantor.ofNat st.pl).2, p2 := st.p2 + (Cantor.ofNat st.pl).1 }
def readp1F (st : AS) : AS :=
  { st with pl := (Cantor.ofNat st.pl).2, p1 := st.p1 + (Cantor.ofNat st.pl).1 }

theorem pushL (st : AS) (hc : Clean st) : Rn (.node 171) st (pushF st) := pushwff st hc
theorem par1L (st : AS) (hc : Clean st) : Rn (.node 166) st (par1F st) := par1 st hc
theorem par2L (st : AS) (hc : Clean st) : Rn (.node 121) st (par2F st) := par2 st hc
theorem par3L (st : AS) (hc : Clean st) : Rn (.node 168) st (par3F st) := par3 st hc
theorem consL (st : AS) (hc : Clean st) : Rn (.node 119) st (consF st) := cons st hc
theorem welL (st : AS) (hc : Clean st) : Rn (.node 181) st (welF st) := wel_m st hc
theorem walL (st : AS) (hc : Clean st) : Rn (.node 180) st (walF st) := wal_m st hc
theorem weqL (st : AS) (hc : Clean st) : Rn (.node 182) st (weqF st) := weq_m st hc
theorem wnL (st : AS) (hc : Clean st) : Rn (.node 218) st (wnF st) := wn_m st hc
theorem waL (st : AS) (hc : Clean st) : Rn (.node 178) st (waF st) := wa_m st hc
theorem wexL (st : AS) (hc : Clean st) : Rn (.node 183) st (wexF st) := wex_m st hc
theorem readp2L (st : AS) (hc : Clean st) : Rn (.node 176) st (readp2F st) := read_p2 st hc
theorem readp1L (st : AS) (hc : Clean st) : Rn (.node 175) st (readp1F st) := read_p1 st hc

theorem pushC (st : AS) (hc : Clean st) : Clean (pushF st) := hc
theorem par1C (st : AS) (hc : Clean st) : Clean (par1F st) := hc
theorem par2C (st : AS) (hc : Clean st) : Clean (par2F st) := hc
theorem par3C (st : AS) (hc : Clean st) : Clean (par3F st) := hc
theorem consC (st : AS) (hc : Clean st) : Clean (consF st) := hc
theorem welC (st : AS) (hc : Clean st) : Clean (welF st) := hc
theorem walC (st : AS) (hc : Clean st) : Clean (walF st) := hc
theorem weqC (st : AS) (hc : Clean st) : Clean (weqF st) := hc
theorem wnC (st : AS) (hc : Clean st) : Clean (wnF st) := hc
theorem waC (st : AS) (hc : Clean st) : Clean (waF st) := hc
theorem wexC (st : AS) (hc : Clean st) : Clean (wexF st) := hc
theorem readp2C (st : AS) (hc : Clean st) : Clean (readp2F st) := hc
theorem readp1C (st : AS) (hc : Clean st) : Clean (readp1F st) := hc

/-- The gate: clear the bundle when `c = b` or `c = a`, and clear `axiomcode`, `param1`,
`param2`. -/
def gateF (st : AS) : AS :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

theorem gateC (st : AS) (hc : Clean st) : Clean (gateF st) := hc

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


inductive AXAtom where
  | par1 | par2 | par3 | push | cons | wel | wal | weq | wn | wa | wex | readp2 | readp1
  deriving DecidableEq

def AXAtom.node : AXAtom → Nat
  | .par1 => 166
  | .par2 => 121
  | .par3 => 168
  | .push => 171
  | .cons => 119
  | .wel => 181
  | .wal => 180
  | .weq => 182
  | .wn => 218
  | .wa => 178
  | .wex => 183
  | .readp2 => 176
  | .readp1 => 175

def AXAtom.effect : AXAtom → AS → AS
  | .par1 => par1F
  | .par2 => par2F
  | .par3 => par3F
  | .push => pushF
  | .cons => consF
  | .wel => welF
  | .wal => walF
  | .weq => weqF
  | .wn => wnF
  | .wa => waF
  | .wex => wexF
  | .readp2 => readp2F
  | .readp1 => readp1F

theorem AXAtom.clean (a : AXAtom) (st : AS) (hc : Clean st) :
    Clean (a.effect st) := by
  cases a <;> exact hc

theorem AXAtom.run (a : AXAtom) (st : AS) (hc : Clean st) :
    Rn (.node a.node) st (a.effect st) := by
  cases a
  · exact par1L st hc
  · exact par2L st hc
  · exact par3L st hc
  · exact pushL st hc
  · exact consL st hc
  · exact welL st hc
  · exact walL st hc
  · exact weqL st hc
  · exact wnL st hc
  · exact waL st hc
  · exact wexL st hc
  · exact readp2L st hc
  · exact readp1L st hc

/-- Each pair names a macro and the next program node; the suffix is the gate. -/
def axWordCheck : Nat → List (AXAtom × Nat) → Bool
  | n, [] => decide (n = 457)
  | n, (a, next) :: rest =>
    decide (dagPerm.nodes n = (.node a.node, .node next)) && axWordCheck next rest

def axWordEval : List (AXAtom × Nat) → AS → AS
  | [], st => gateF st
  | (a, _) :: rest, st => axWordEval rest (a.effect st)

theorem axWordClean (word : List (AXAtom × Nat)) (st : AS) (hc : Clean st) :
    Clean (axWordEval word st) := by
  induction word generalizing st with
  | nil => exact gateC st hc
  | cons a rest ih => exact ih _ (a.1.clean st hc)

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
    exact seqAS h.1 (a.run st hc) (ih h.2 _ (a.clean st hc))

def axWord : List (AXAtom × Nat) := [
  (.par1, 467), (.par2, 468), (.wal, 469), (.par3, 470), (.par1, 471), (.readp2, 485),
  (.cons, 486), (.readp1, 474), (.par1, 475), (.cons, 476), (.par1, 477), (.par3, 478),
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

/-- **The AX routine is EnumPerm's AX step.** -/
theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumPerm.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        EnumPerm.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a
          t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  simp only [f236, axWord, axWordEval, AXAtom.effect, gateF,
    pushF, par1F, par2F, par3F, consF, welF, walF, weqF, wnF, waF, wexF,
    readp1F, readp2F, ofNat_P, Nat.zero_add,
    EnumPerm.gate, EnumPerm.axStack, bundle222, nks, clos, req, vrel, growG,
    rho1, rho2, rho3, rho4, rho5, rho6, rho8, wa, wex]

#print axioms l236
#print axioms ax_eval
end SetTheory.BusyBeaver.ZFC.L2Perm
