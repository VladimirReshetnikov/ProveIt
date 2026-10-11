import GowersSzemeredi.Proofs05IntegerRepresentatives
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

/-! Split an unreduced increasing arithmetic sequence at the boundaries of
the intervals `[q*N,(q+1)*N)`. Each resulting cell has genuine integer
representatives. The construction works for composite moduli as well. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def integerRunIndices (N a d L q : Nat) : Finset Nat :=
  (Finset.range L).filter fun i => (a + i * d) / N = q

theorem mem_integerRunIndices {N a d L q i : Nat} :
    i ∈ integerRunIndices N a d L q ↔ i < L ∧ (a + i * d) / N = q := by
  simp [integerRunIndices]

theorem integerRunIndices_between {N a d L q lo hi i : Nat}
    (hlo : lo ∈ integerRunIndices N a d L q)
    (hhi : hi ∈ integerRunIndices N a d L q) (hli : lo ≤ i) (hih : i ≤ hi) :
    i ∈ integerRunIndices N a d L q := by
  rw [mem_integerRunIndices] at hlo hhi ⊢
  have hl := Nat.div_le_div_right
    (Nat.add_le_add_left (Nat.mul_le_mul_right d hli) a) (c := N)
  have hh := Nat.div_le_div_right
    (Nat.add_le_add_left (Nat.mul_le_mul_right d hih) a) (c := N)
  exact ⟨by omega, by omega⟩

/-- A fixed quotient gives a consecutive interval of parameter indices. -/
theorem integerRunIndices_eq_Icc {N a d L q : Nat}
    (h : (integerRunIndices N a d L q).Nonempty) :
    integerRunIndices N a d L q =
      Finset.Icc ((integerRunIndices N a d L q).min' h)
        ((integerRunIndices N a d L q).max' h) := by
  classical
  ext i
  constructor
  · intro hi
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hi, Finset.le_max' _ _ hi⟩
  · intro hi
    obtain ⟨hli, hih⟩ := Finset.mem_Icc.mp hi
    exact integerRunIndices_between (Finset.min'_mem _ h) (Finset.max'_mem _ h) hli hih

/-- The modular image of a single run is an ordinary positive-step
progression in `[0,N)`, without losing any of its points or changing its step. -/
theorem integerRun_has_representatives {N : Nat} [NeZero N]
    (a d L q : Nat) (hd : 0 < d) :
    ∃ Q : NatAP, Q.IsProper ∧ Q.step = d ∧
      Q.length = (integerRunIndices N a d L q).card ∧
      Q.carrier ⊆ Finset.range N ∧
      Q.carrier.image (fun x : Nat => (x : ZMod N)) =
        (integerRunIndices N a d L q).image
          (fun i : Nat => ((a + i * d : Nat) : ZMod N)) := by
  classical
  let s := integerRunIndices N a d L q
  change ∃ Q : NatAP, Q.IsProper ∧ Q.step = d ∧ Q.length = s.card ∧
    Q.carrier ⊆ Finset.range N ∧
    Q.carrier.image (fun x : Nat => (x : ZMod N)) =
      s.image (fun i : Nat => ((a + i * d : Nat) : ZMod N))
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hlo : lo ∈ s := Finset.min'_mem _ hs
    have hhi : hi ∈ s := Finset.max'_mem _ hs
    have hlohi : lo ≤ hi := Finset.min'_le _ _ hhi
    have hinterval : s = Finset.Icc lo hi := integerRunIndices_eq_Icc hs
    let Q : NatAP := ⟨(a + lo * d) % N, d, hi + 1 - lo⟩
    have hvalue (i : Nat) (hli : lo ≤ i) (hih : i ≤ hi) :
        (a + lo * d) % N + (i - lo) * d = (a + i * d) % N := by
      have hiS : i ∈ s := integerRunIndices_between hlo hhi hli hih
      have hqlo := (mem_integerRunIndices.mp hlo).2
      have hqi := (mem_integerRunIndices.mp hiS).2
      have hloeq := Nat.div_add_mod (a + lo * d) N
      have hieq := Nat.div_add_mod (a + i * d) N
      have hdecomp : a + i * d = a + lo * d + (i - lo) * d := by
        calc
          a + i * d = a + (lo + (i - lo)) * d := by rw [Nat.add_sub_of_le hli]
          _ = _ := by ring
      rw [hqlo] at hloeq
      rw [hqi] at hieq
      have hieq' := hieq.trans hdecomp
      omega
    have hbound (j : Nat) (hj : j < Q.length) : Q.start + j * Q.step < N := by
      have hhi' : lo + j ≤ hi := by dsimp [Q] at hj; omega
      have h := hvalue (lo + j) (by omega) hhi'
      simp only [Nat.add_sub_cancel_left] at h
      dsimp [Q]
      rw [h]
      exact Nat.mod_lt _ (NeZero.pos N)
    have hQproper : Q.IsProper := by
      refine ⟨hd, ?_⟩
      unfold NatAP.carrier
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        apply Fin.ext
        exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)
    refine ⟨Q, hQproper, rfl, ?_, ?_, ?_⟩
    · rw [hinterval, Nat.card_Icc]
    · intro x hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hbound j j.isLt)
    · ext x
      constructor
      · rintro hx
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
        have hjlen : j.val < hi + 1 - lo := j.isLt
        have hjhi : lo + j.val ≤ hi := by omega
        have hji : lo + j.val ∈ s :=
          integerRunIndices_between hlo hhi (by omega) hjhi
        refine Finset.mem_image.mpr ⟨lo + j.val, hji, ?_⟩
        have h := hvalue (lo + j.val) (by omega) hjhi
        simp only [Nat.add_sub_cancel_left] at h
        change ((a + (lo + j.val) * d : Nat) : ZMod N) =
          (((a + lo * d) % N + j.val * d : Nat) : ZMod N)
        rw [h]
        simp
      · rintro hx
        obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hx
        have hli : lo ≤ i := Finset.min'_le _ _ hiS
        have hih : i ≤ hi := Finset.le_max' _ _ hiS
        have hjlen : i - lo < Q.length := by dsimp [Q]; omega
        apply Finset.mem_image.mpr
        refine ⟨Q.start + (i - lo) * Q.step, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨⟨i - lo, hjlen⟩, Finset.mem_univ _, rfl⟩
        · change (((a + lo * d) % N + (i - lo) * d : Nat) : ZMod N) =
            ((a + i * d : Nat) : ZMod N)
          rw [hvalue i hli hih]
          simp
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    refine ⟨⟨0, d, 0⟩, ⟨hd, by simp [NatAP.carrier]⟩, rfl, ?_, ?_, ?_⟩
    · simp [hempty]
    · simp [NatAP.carrier]
    · simp [NatAP.carrier, hempty]

/-- An injective modular arithmetic sequence can be partitioned exactly at
wrap boundaries. All cells have genuine integer representatives and the
same prescribed positive integer step. The explicit cell budget is the
total number of quotient intervals reached by the unreduced sequence. -/
theorem integerRun_partition {N : Nat} [NeZero N]
    (a d L : Nat) (hd : 0 < d)
    (hinj : Set.InjOn (fun i : Nat => ((a + i * d : Nat) : ZMod N))
      (Finset.range L : Set Nat)) :
    ∃ M : Nat, ∃ Q : Fin M → NatAP,
      M = (a + (L - 1) * d) / N + 1 ∧
      M * N ≤ a + (L - 1) * d + N ∧
      IsPartition (fun j => ((Q j).toModAP N).carrier)
        ((Finset.range L).image (fun i : Nat => ((a + i * d : Nat) : ZMod N))) ∧
      (∀ j, (Q j).IsProper ∧ (Q j).step = d ∧
        (Q j).carrier ⊆ Finset.range N ∧
        ((Q j).toModAP N).HasIntegerRepresentatives) := by
  classical
  let M := (a + (L - 1) * d) / N + 1
  choose Q hQ hstep hlen hsub himage using
    fun q : Fin M => integerRun_has_representatives (N := N) a d L q.val hd
  have hcarrier (q : Fin M) :
      ((Q q).toModAP N).carrier =
        (integerRunIndices N a d L q.val).image
          (fun i : Nat => ((a + i * d : Nat) : ZMod N)) := by
    rw [NatAP.toModAP_carrier, himage q]
  refine ⟨M, Q, rfl, ?_, ?_, ?_⟩
  · dsimp [M]
    rw [Nat.add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) N
  · constructor
    · intro x
      constructor
      · rintro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        have hiL := Finset.mem_range.mp hi
        have hibound : i ≤ L - 1 := by omega
        have hquot : (a + i * d) / N < M := by
          have hle := Nat.div_le_div_right
            (Nat.add_le_add_left (Nat.mul_le_mul_right d hibound) a) (c := N)
          dsimp [M]
          omega
        refine ⟨⟨(a + i * d) / N, hquot⟩, ?_⟩
        simp only [hcarrier]
        exact Finset.mem_image.mpr ⟨i, mem_integerRunIndices.mpr ⟨hiL, rfl⟩, rfl⟩
      · rintro ⟨q, hx⟩
        simp only [hcarrier] at hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr
          ⟨i, Finset.mem_range.mpr (mem_integerRunIndices.mp hi).1, rfl⟩
    · intro q r hqr
      rw [Finset.disjoint_left]
      intro x hxq hxr
      simp only [hcarrier] at hxq hxr
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxq
      obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hxr
      obtain ⟨hiL, hiq⟩ := mem_integerRunIndices.mp hi
      obtain ⟨hjL, hjr⟩ := mem_integerRunIndices.mp hj
      have hij : i = j := hinj (Finset.mem_range.mpr hiL) (Finset.mem_range.mpr hjL)
        (hix.trans hjx.symm)
      have hqreq : q = r := Fin.ext (hiq.symm.trans (hij ▸ hjr))
      exact bne_iff_ne.mp hqr hqreq
  · intro q
    exact ⟨hQ q, hstep q, hsub q,
      (Q q).toModAP_hasIntegerRepresentatives (hQ q) (hsub q)⟩

end LeanProofs.GowersSzemeredi
