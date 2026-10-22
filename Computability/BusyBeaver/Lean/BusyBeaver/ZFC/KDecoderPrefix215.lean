import BusyBeaver.ZFC.DecoderSourceBinding
import BusyBeaver.ZFC.KZipTape
import BusyBeaver.ZFC.KSim

/-! Exact zipper entry for the shared decoder.  This module retains the entire
consumed source word.  It stops before the terminal primitive transition: no
primitive, register, return, or whole-machine coverage claim is made here. -/
namespace SetTheory.BusyBeaver.ZFC.KDecoderPrefix215
open KZip KRuntimeCore KSim FramedWindow DecoderCertificate DecoderPaths
open DecoderSourceBinding K215Decoder RegisterPath SiteCoverage

/-- The complete symbolic continuation at the final primitive-read bit. -/
def leafPort (pre : List Bool) (bit : Bool) (q : Nat) : SConf :=
  (q, false, pre.reverse.map .bit ++ [.bit true],
    [.bit bit, .run false 1 (D0 - (pre.length + 1)), .bit true, .box (.plain .none)])

theorem conc_leafPort (n : Nat) (vs : List Nat) (pre : List Bool) (bit : Bool) (q : Nat) :
    conc n vs (leafPort pre bit q) =
      zc q (pre.reverse ++ [true])
        (bit :: List.replicate (n + (D0 - (pre.length + 1))) false ++ true :: sepsR vs) := by
  simp only [leafPort, conc, flat_append, flat_bits]
  simp [flat, segList, boxList, Nat.one_mul]

/-- Moving over a known bit only changes the zipper cut, not the integer tape. -/
theorem rel_cons_right {q q' : Nat} {a : Int} {t : FramedWindow.Tape} {l r : List Bool} {bit : Bool}
    (hr : KZipTape.Rel ⟨q,a,t⟩ (zc q l (bit :: r))) :
    KZipTape.Rel ⟨q',a+1,t⟩ (zc q' (bit :: l) r) := by
  have h := KZipTape.rel_right hr q'
  simpa only [zc, headD_trim, tail_trim, trim_cons_trim, List.headD_cons, List.tail_cons] using h

/-- An entire source prefix is retained, in reverse order, to the left of the
head.  No finiteness assumption is imposed on the related integer tape. -/
theorem rel_word (pre : List Bool) {q : Nat} {a : Int} {t : FramedWindow.Tape} {l r : List Bool}
    (hr : KZipTape.Rel ⟨q,a,t⟩ (zc q l (pre ++ r))) (q' : Nat) :
    KZipTape.Rel ⟨q',a+(pre.length : Int),t⟩ (zc q' (pre.reverse ++ l) r) := by
  induction pre generalizing a l with
  | nil =>
    have h : KZipTape.Rel ⟨q',a,t⟩ (zc q' l r) := ⟨rfl,hr.2⟩
    simpa using h
  | cons bit pre ih =>
    have h := ih (rel_cons_right (q' := q) hr)
    have ha : a+1+(pre.length : Int) = a+((bit::pre).length : Int) := by
      simp only [List.length_cons]; omega
    simpa only [ha, List.reverse_cons, List.append_assoc, List.singleton_append] using h

/-- Every displayed zipper prefix is read at the corresponding integer cut. -/
theorem reads_of_rel (word : List Bool) {q : Nat} {a : Int} {t : FramedWindow.Tape} {l r : List Bool}
    (hr : KZipTape.Rel ⟨q,a,t⟩ (zc q l (word ++ r))) : Reads t a word := by
  induction word generalizing a l with
  | nil => trivial
  | cons bit word ih =>
    refine ⟨?_, ih (rel_cons_right (q' := q) hr)⟩
    have h := (hr.2 0).1
    simp only [Int.natCast_zero, Int.add_zero] at h
    change t a = (trim (bit :: (word ++ r))).getD 0 false at h
    rwa [← List.headD_eq_getD, headD_trim] at h

/-- The role graph is deterministic even when several roles share a physical
state.  The full role path, not the state or its short suffix, determines entry. -/
theorem rolePath_unique {rs : Array Role} {first last last' : Nat} {pre : List Bool}
    (h : RolePath rs first pre last) (h' : RolePath rs first pre last') : last = last' := by
  induction h generalizing last' with
  | nil => cases h'; rfl
  | cons hat hedge ht ih =>
    cases h' with
    | cons hat' hedge' ht' =>
      have hr := Option.some.inj (hat.symm.trans hat')
      cases hr
      have he := hedge.symm.trans hedge'
      cases he
      exact ih ht'

private theorem snoc_unique {pre pre' : List Bool} {bit bit' : Bool}
    (h : pre ++ [bit] = pre' ++ [bit']) : pre = pre' ∧ bit = bit' := by
  have hr : bit :: pre.reverse = bit' :: pre'.reverse := by
    simpa using congrArg List.reverse h
  obtain ⟨hb,hpre⟩ := List.cons.inj hr
  exact ⟨by simpa using congrArg List.reverse hpre, hb⟩

theorem routed_control_unique {M : Table} {nodes : Array Node} {rs : Array Role}
    {first q q' op arg op' arg' : Nat} {word : List Bool} {bit bit' : Bool}
    (h : RoutedEntry M nodes rs first word q bit op arg)
    (h' : RoutedEntry M nodes rs first word q' bit' op' arg') : q = q' ∧ bit = bit' := by
  obtain ⟨pre,rid,r,n,action,hsplit,hpath,hat,hq,_,_,_⟩ := h
  obtain ⟨pre',rid',r',n',action',hsplit',hpath',hat',hq',_,_,_⟩ := h'
  obtain ⟨hpre,hbit⟩ := snoc_unique (hsplit.symm.trans hsplit')
  cases hpre
  cases hbit
  have hrid := rolePath_unique hpath hpath'
  cases hrid
  have hr := Option.some.inj (hat.symm.trans hat')
  cases hr
  exact ⟨hq.symm.trans hq',rfl⟩

/-- The full-tape hypothesis already supplied by the source-binding theorem.
The concrete endpoints below discharge it; it is not an additional assumption
on any primitive or register operation. -/
def FullEntry (word : List Bool) (e : RegisterPath.Edge) : Prop :=
  ∀ t : FramedWindow.Tape, t (-1) = true → Reads t 0 word →
    ∃ op arg steps q bit,
      e = primitive op arg ∧ word.length-1 ≤ steps ∧ steps ≤ 7*(word.length-1) ∧
      FramedWindow.run (fullStep formal) steps ⟨84,0,t⟩ =
        some ⟨q,(word.length : Int)-1,t⟩ ∧
      t ((word.length : Int)-1) = bit ∧
      RoutedEntry formal sourceNodes roles 0 word q bit op arg

/-- Exact entry on arbitrary gap and register values, with the full source
continuation present.  There is no register-validity or length hypothesis. -/
theorem entry_run {word : List Bool} {e : RegisterPath.Edge} (entry : FullEntry word e)
    (n : Nat) (vs : List Nat) :
    ∃ pre bit q op arg steps,
      word = pre ++ [bit] ∧ e = primitive op arg ∧
      RoutedEntry formal sourceNodes roles 0 word q bit op arg ∧
      pre.length ≤ steps ∧ steps ≤ 7*pre.length ∧
      KZip.run KTableCore.tm215 steps (conc n vs (start word)) =
        some (conc n vs (leafPort pre bit q)) := by
  let rest := List.replicate (n + (D0-word.length)) false ++ true :: sepsR vs
  let z := zc 84 [true] (word ++ rest)
  let t := KZipTape.tape z
  have hrel : KZipTape.Rel ⟨84,0,t⟩ z := KZipTape.rel_full z
  have hm : t (-1) = true := by
    have h := (hrel.2 0).2
    change t (-1) = (trim [true]).getD 0 false at h
    rwa [← List.headD_eq_getD, headD_trim] at h
  have hw : Reads t 0 word := reads_of_rel word hrel
  obtain ⟨op,arg,steps,q,bit,he,lo,hi,hs,hbit,hentry⟩ := entry t hm hw
  obtain ⟨pre,hsplit⟩ : ∃ pre, word = pre ++ [bit] := by
    obtain ⟨pre,_,_,_,_,hsplit,_,_,_,_,_,_⟩ := hentry
    exact ⟨pre,hsplit⟩
  have hlen : word.length-1 = pre.length := by simp [hsplit]
  have hhead : (word.length : Int)-1 = (pre.length : Int) := by simp [hsplit]
  have hrel' : KZipTape.Rel ⟨84,0,t⟩ (zc 84 [true] (pre ++ (bit :: rest))) := by
    simpa only [z,hsplit,List.append_assoc,List.singleton_append] using hrel
  have hend : KZipTape.Rel ⟨q,(pre.length : Int),t⟩
      (zc q (pre.reverse ++ [true]) (bit :: rest)) := by
    simpa only [Int.zero_add] using rel_word pre hrel' q
  have hs' : FramedWindow.run (fullStep (KZipTape.table KTableCore.tm215)) steps
      ⟨84,0,t⟩ = some ⟨q,(pre.length : Int),t⟩ := by
    simpa only [formal,hhead] using hs
  have hz := KZipTape.run_reflect hrel hend
    ⟨trim_trim _,trim_trim _⟩ ⟨trim_trim _,trim_trim _⟩ hs'
  have hstart : conc n vs (start word) = z := by
    simpa only [z,rest,List.append_assoc] using conc_start n vs word
  have hport : conc n vs (leafPort pre bit q) =
      zc q (pre.reverse ++ [true]) (bit :: rest) := by
    simp only [conc_leafPort,rest,hsplit,List.length_append,List.length_singleton,List.cons_append]
  exact ⟨pre,bit,q,op,arg,steps,hsplit,he,hentry,hlen ▸ lo,hlen ▸ hi,
    by simpa only [hstart,hport] using hz⟩

/-- A single source-determined entry port works for every gap and register list.
Only the run clock is existential inside these universal quantifiers. -/
theorem entry_uniform {word : List Bool} {e : RegisterPath.Edge} (entry : FullEntry word e) :
    ∃ pre bit q op arg,
      word = pre ++ [bit] ∧ e = primitive op arg ∧
      RoutedEntry formal sourceNodes roles 0 word q bit op arg ∧
      ∀ n vs, ∃ steps, pre.length ≤ steps ∧ steps ≤ 7*pre.length ∧
        KZip.run KTableCore.tm215 steps (conc n vs (start word)) =
          some (conc n vs (leafPort pre bit q)) := by
  obtain ⟨pre,bit,q,op,arg,_,hsplit,he,hr,_,_,_⟩ := entry_run entry 0 []
  refine ⟨pre,bit,q,op,arg,hsplit,he,hr,?_⟩
  intro n vs
  obtain ⟨pre',bit',q',_,_,steps,hsplit',_,hr',lo,hi,hz⟩ := entry_run entry n vs
  obtain ⟨hq,hbit⟩ := routed_control_unique hr hr'
  cases hq
  cases hbit
  have hpre := (snoc_unique (hsplit.symm.trans hsplit')).1
  cases hpre
  exact ⟨steps,lo,hi,hz⟩

/-- Every literal source leaf has a uniform exact zipper decoder prefix. -/
theorem leaf_prefix {word : List Bool} {e : RegisterPath.Edge}
    (leaf : LeafAt KSource215.t215 word e) :
    ∃ pre bit q op arg,
      word = pre ++ [bit] ∧ e = primitive op arg ∧
      RoutedEntry formal sourceNodes roles 0 word q bit op arg ∧
      ∀ n vs, ∃ steps, pre.length ≤ steps ∧ steps ≤ 7*pre.length ∧
        KZip.run KTableCore.tm215 steps (conc n vs (start word)) =
          some (conc n vs (leafPort pre bit q)) := by
  apply entry_uniform
  intro t hm hw
  simpa only [Int.zero_sub,Int.zero_add] using upstream_leaf_reaches_routed leaf 0 t hm hw

/-- Includes the walk's implicit zero padding and exact consumed length.  The
unconsumed instruction suffix is not substituted for the consumed word. -/
theorem walk_prefix (P : List Bool) (e : RegisterPath.Edge) (d : Nat)
    (walks : RegisterPath.walk KSource215.p215 (KSource215.p215.nnodes+1)
      KSource215.p215.root P 0 = some (e,d)) :
    ∃ pre bit q op arg,
      consume P d = pre ++ [bit] ∧ e = primitive op arg ∧
      RoutedEntry formal sourceNodes roles 0 (consume P d) q bit op arg ∧
      ∀ n vs, ∃ steps, pre.length ≤ steps ∧ steps ≤ 7*pre.length ∧
        KZip.run KTableCore.tm215 steps (conc n vs (start (consume P d))) =
          some (conc n vs (leafPort pre bit q)) := by
  apply entry_uniform
  intro t hm hw
  have hlen : (consume P d).length = d := by unfold consume; simp
  simpa only [hlen,Int.zero_sub,Int.zero_add] using upstream_walk_reaches_routed P e d walks 0 t hm hw

#print axioms rel_word
#print axioms entry_uniform
#print axioms leaf_prefix
#print axioms walk_prefix
end SetTheory.BusyBeaver.ZFC.KDecoderPrefix215
