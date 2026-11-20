/- Exact certificate arithmetic and its kernel-checked proof interface. -/
import MoserWorm.UpperBound.Certificate.Kernel.Bridge

namespace MoserWorm.UpperBound.Certificate.Kernel

open MoserWorm.UpperBound.Certificate MoserWorm.UpperBound.Certificate.Partition

/-- Decode a kernel frontier obligation. -/
def decodeOb (ob : KOb) : Ob := (decodeTree ob.1, ob.2.1, ob.2.2)

theorem cutFrontier_decode :
    ∀ (d : ℕ) (t : KTree) (as : List (ℕ × Fin 2)) (r : ℕ × ℕ × ℕ × ℕ),
      cutFrontier d (decodeTree t) as r =
        (kCutFrontier d t as r).map decodeOb := by
  intro d
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro t as r
    match t with
    | .pl m c0 c1 =>
      rw [decodeTree]
      change cutFrontier d (decodeTree c0) _ _ ++ cutFrontier d (decodeTree c1) _ _
        = _
      rw [ih c0, ih c1, kCutFrontier, List.map_append]
    | .split cells =>
      rw [decodeTree_split]
      change (cells.map (fun x => (x.1, decodeTree x.2))).flatMap
          (fun x => cutFrontier d x.2 as x.1) = _
      rw [List.flatMap_map, kCutFrontier, List.map_flatMap]
      congr 1
      funext x
      exact ih x.2 as x.1
    | .leaf mu =>
      rw [decodeTree]
      simp only [cutFrontier, kCutFrontier, List.map_cons, List.map_nil,
        decodeOb, decodeTree]

theorem cutTop_decode (ctx : Ctx) (esz : ℕ) (hesz : esz = ctx.eRows.size) :
    ∀ (d : ℕ) (t : KTree) (as : List (ℕ × Fin 2)) (r : ℕ × ℕ × ℕ × ℕ),
      cutTop ctx d (decodeTree t) as r = kCutTop esz d t as r := by
  intro d
  induction d with
  | zero => intros; rfl
  | succ d ih =>
    intro t as r
    match t with
    | .pl m c0 c1 =>
      rw [decodeTree]
      change ((decide (2 * m + 1 < ctx.eRows.size)) && _ &&
        cutTop ctx d (decodeTree c0) _ _ && cutTop ctx d (decodeTree c1) _ _) = _
      rw [ih c0, ih c1, hesz]
      rfl
    | .split cells =>
      rw [decodeTree_split]
      change (splitStruct (cells.map (fun x => (x.1, decodeTree x.2))) r &&
        (cells.map (fun x => (x.1, decodeTree x.2))).all
          (fun x => cutTop ctx d x.2 as x.1)) = _
      rw [kSplitStruct_eq, List.all_map, kCutTop]
      congr 1
      exact all_congr _ _ _ (fun x _ => ih x.2 as x.1)
    | .leaf mu =>
      rw [decodeTree]
      rfl

/-- `kCheckObs` is the batched `kCheckTree` (the tries are shared). -/
theorem kCheckObs_eq (c : KCtx) (fuel : ℕ) (obs : List KOb) :
    kCheckObs c fuel obs =
      obs.all (fun ob => kCheckTree c fuel ob.1 ob.2.1 ob.2.2) := rfl

/-- `kCheckObs` splits over append (the generated modules check their
obligation batch in sub-batches, so each `decide +kernel` declaration stays
small and the kernel's per-declaration memory stays bounded). -/
theorem kCheckObs_append (c : KCtx) (fuel : ℕ) (l1 l2 : List KOb) :
    kCheckObs c fuel (l1 ++ l2) =
      (kCheckObs c fuel l1 && kCheckObs c fuel l2) := by
  unfold kCheckObs
  rw [List.all_append]

/-- Soundness of one range module's kernel fact. -/
theorem checkObs_sound (c : KCtx) (fuel : ℕ) (obs : List KOb)
    (h : kCheckObs c fuel obs = true) :
    ∀ ob ∈ obs, checkTree (decodeCtx c) fuel (decodeTree ob.1)
      ob.2.1 ob.2.2 = true := by
  rw [kCheckObs_eq, List.all_eq_true] at h
  intro ob hob
  rw [← kCheckTree_eq_checkTree]
  exact h ob hob

/-- A batch with lookup tries supplied explicitly, avoiding repeated construction. -/
def kCheckPrepared (c : KCtx) (nt : KVec KQ2) (et : KVec (Option KRow))
    (fuel : ℕ) (obs : List KOb) : Bool :=
  obs.all (fun ob =>
    kCheckTreeCore (3 + c.kR + c.kL) nt et c.eRows.length c.kR c.kL c.target
      fuel ob.1 ob.2.1 ob.2.2)

/-- The supplied tries are checked once against the complete context. -/
theorem checkPrepared_sound (c : KCtx) (nt : KVec KQ2) (et : KVec (Option KRow))
    (hnt : nt = KVec.ofList kQ2z
      ((List.range (3 + c.kR + c.kL)).map (kNormalOf c.kR c.right c.left)))
    (het : et = KVec.ofList none c.eRows)
    (fuel : ℕ) (obs : List KOb) (h : kCheckPrepared c nt et fuel obs = true) :
    ∀ ob ∈ obs, checkTree (decodeCtx c) fuel (decodeTree ob.1)
      ob.2.1 ob.2.2 = true := by
  subst nt
  subst et
  exact checkObs_sound c fuel obs h

/-- Reassembly: full-fuel `checkTree` from the kernel-checked skeleton and
the per-obligation facts. -/
theorem checkTree_of_kernel_parts (c : KCtx) (d : ℕ) (hd : d ≤ 999)
    (t : KTree) (rect : ℕ × ℕ × ℕ × ℕ)
    (htop : kCutTop c.eRows.length d t [] rect = true)
    (hobs : ∀ ob ∈ kCutFrontier d t [] rect,
      checkTree (decodeCtx c) (1000 - d) (decodeTree ob.1) ob.2.1 ob.2.2 = true) :
    checkTree (decodeCtx c) 1000 (decodeTree t) [] rect = true := by
  have hesz : c.eRows.length = (decodeCtx c).eRows.size := by
    unfold decodeCtx
    simp
  have h := checkTree_of_cut (decodeCtx c) d (1000 - d) (decodeTree t) [] rect
    (by omega) ?_ ?_
  · rwa [show 1000 - d + d = 1000 by omega] at h
  · rw [cutTop_decode (decodeCtx c) c.eRows.length hesz]
    exact htop
  · intro x hx
    rw [cutFrontier_decode] at hx
    obtain ⟨ob, hob, rfl⟩ := List.mem_map.mp hx
    exact hobs ob hob

end MoserWorm.UpperBound.Certificate.Kernel
