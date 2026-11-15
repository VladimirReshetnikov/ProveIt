import PA194SourceHaltSite
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceHaltUnique
open M6.Source M6.Source.PathTrie PA194.SourceTree PA194SourceProgram PA194SourceHaltSite

theorem uniqueIndex {α : Type} (p : α → Bool) (x : α) (l : List α) (i j : Nat)
    (hp : p x = true) (hf : l.filter p = [x])
    (hi : l[i]? = some x) (hj : l[j]? = some x) : i=j := by
  induction l generalizing i j with
  | nil => cases i <;> simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
        subst a
        simp only [List.filter_cons,hp,↓reduceIte,List.cons.injEq,true_and] at hf
        have hm : x ∈ l := List.mem_of_getElem? hj
        have hm' : x ∈ l.filter p := List.mem_filter.mpr ⟨hm,hp⟩
        rw [hf] at hm'
        simp at hm'
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hj
        subst a
        simp only [List.filter_cons,hp,↓reduceIte,List.cons.injEq,true_and] at hf
        have hm : x ∈ l := List.mem_of_getElem? hi
        have hm' : x ∈ l.filter p := List.mem_filter.mpr ⟨hm,hp⟩
        rw [hf] at hm'
        simp at hm'
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        have hpa : p a = false := by
          cases ha : p a with
          | false => rfl
          | true =>
            simp only [List.filter_cons,ha,↓reduceIte,List.cons.injEq] at hf
            rcases hf with ⟨rfl,hf⟩
            have hm : a ∈ l := List.mem_of_getElem? hi
            have hm' : a ∈ l.filter p := List.mem_filter.mpr ⟨hm,hp⟩
            rw [hf] at hm'
            simp at hm'
        have hfl : l.filter p = [x] := by simpa [hpa] using hf
        exact congrArg Nat.succ (ih i j hfl hi hj)

theorem resolveHaltOp (s : Site) (h : resolve sites s = some .halt) : s.op = .halt := by
  cases he : s.op with
  | inc r => simp only [resolve,he,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h; obtain ⟨_,_,h⟩ := h; cases h
  | dec r => simp only [resolve,he,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h; obtain ⟨_,_,_,_,_,_,h⟩ := h; cases h
  | breakTo k => simp only [resolve,he,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h; obtain ⟨_,_,_,_,h⟩ := h; cases h
  | continueTo k => simp only [resolve,he,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff,Option.some.injEq] at h; obtain ⟨_,_,_,_,h⟩ := h; cases h
  | halt => rfl

theorem resolvedHaltIndex (i : Nat) (h : resolveAt sites i = some .halt) : i=10 := by
  simp only [resolveAt,Option.bind_eq_bind,Option.pure_def,Option.bind_eq_some_iff] at h
  obtain ⟨s,hs,hr⟩ := h
  have hop := resolveHaltOp s hr
  have hm : s ∈ sites.toList := by
    have hlist : sites.toList[i]? = some s := by rwa [Array.getElem?_toList]
    exact List.mem_of_getElem? hlist
  have hm' : s ∈ sites.toList.filter (fun s => s.op == .halt) := by
    apply List.mem_filter.mpr
    exact ⟨hm,by simp [hop]⟩
  rw [uniqueHaltLeaf] at hm'
  have hsite : s = haltSite := by simpa using hm'
  subst s
  have hi : sites.toList[i]? = some haltSite := by rwa [Array.getElem?_toList]
  have h10 : sites.toList[10]? = some haltSite := by
    rw [Array.getElem?_toList,←PA194SourceProgram.nthSite_sites]
    exact haltSiteAt10
  exact uniqueIndex (fun s : Site => s.op == .halt) haltSite sites.toList i 10 rfl uniqueHaltLeaf hi h10
#print axioms uniqueIndex
#print axioms resolveHaltOp
#print axioms resolvedHaltIndex
end PA194SourceHaltUnique
