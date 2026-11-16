import PA194SourceSite3672Controller
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SourcePathDepth
open M6.Source
open M6.Source.PathTrie

def height : Tree → Nat
  | .leaf _ => 0
  | .node l r => 1 + max (height l) (height r)

theorem nthSiteDepth (t : Tree) (i : Nat) (s : Site)
    (h : nthSite t i = some s) : s.path.length ≤ height t := by
  induction t generalizing i s with
  | leaf op =>
      simp only [nthSite.eq_1] at h
      split at h
      · cases h; simp [height]
      · contradiction
  | node l r ihl ihr =>
      simp only [nthSite.eq_2] at h
      split at h
      · cases hs : nthSite l i with
        | none => simp [hs] at h
        | some v =>
          simp only [hs,Option.map_some,Option.some.injEq] at h
          subst s
          have hv := ihl i v hs
          have hm := Nat.le_max_left (height l) (height r)
          simp only [prepend,List.length_cons,height]
          omega
      · cases hs : nthSite r (i - size l) with
        | none => simp [hs] at h
        | some v =>
          simp only [hs,Option.map_some,Option.some.injEq] at h
          subst s
          have hv := ihr (i - size l) v hs
          have hm := Nat.le_max_right (height l) (height r)
          simp only [prepend,List.length_cons,height]
          omega

theorem pinnedHeight : height PA194.SourceTree.trie = 36 := by decide +kernel

theorem sourcePathBound (i : Nat) : (PA194SourceProgram.path i).length ≤ 36 := by
  unfold PA194SourceProgram.path
  cases hs : nthSite PA194.SourceTree.trie i with
  | none => simp [hs]
  | some v =>
    simp only [hs,Option.map_some,Option.getD_some]
    have h := nthSiteDepth PA194.SourceTree.trie i v hs
    rwa [pinnedHeight] at h
#print axioms nthSiteDepth
#print axioms pinnedHeight
#print axioms sourcePathBound
end PA194SourcePathDepth
