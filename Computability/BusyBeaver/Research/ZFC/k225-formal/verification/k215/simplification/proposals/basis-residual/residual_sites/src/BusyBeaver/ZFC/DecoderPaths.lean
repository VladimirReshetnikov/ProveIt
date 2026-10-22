import BusyBeaver.ZFC.K215Decoder

/-! Source paths produce concrete tape runs.  This is the missing composition
between source-DAG traversal and the independently checked framed blocks. -/
namespace SetTheory.BusyBeaver.ZFC.DecoderPaths
set_option maxRecDepth 8192
set_option maxHeartbeats 0
open FramedWindow DecoderCertificate

/-- `w` is present starting at the given absolute tape position. -/
def Reads (t : Tape) (a : Int) : List Bool → Prop
  | [] => True
  | b :: w => t a = b ∧ Reads t (a+1) w

theorem reads_get {t : Tape} {a : Int} {w : List Bool} (h : Reads t a w) :
    ∀ {i : Nat} {b : Bool}, w[i]? = some b → t (a+i) = b := by
  induction w generalizing a with
  | nil => intro i b hi; simp at hi
  | cons x w ih =>
    intro i b hi
    cases i with
    | zero => simpa using (show t a = b from by simpa using h.1.trans (Option.some.inj hi))
    | succ i =>
      have ht := ih h.2 (by simpa using hi : w[i]? = some b)
      have he : a + 1 + (i : Int) = a + ↑(i+1) := by omega
      simpa only [he] using ht

theorem reads_append {t : Tape} {a : Int} {u v : List Bool} :
    Reads t a (u ++ v) ↔ Reads t a u ∧ Reads t (a+u.length) v := by
  induction u generalizing a with
  | nil => simp [Reads]
  | cons b u ih =>
    simp only [List.cons_append, Reads, List.length_cons, ih]
    have e : a + 1 + (u.length : Int) = a + ↑(u.length+1) := by omega
    rw [e]
    exact and_assoc.symm

theorem reads_drop {t : Tape} {a : Int} {w : List Bool} (h : Reads t a w) (n : Nat) :
    Reads t (a+n) (w.drop n) := by
  induction n generalizing w a with
  | zero => simpa using h
  | succ n ih =>
    cases w with
    | nil => trivial
    | cons b w =>
      have ht := ih h.2
      have e : a + 1 + (n : Int) = a + ↑(n+1) := by omega
      simpa [e] using ht

/-- A context is right-aligned immediately before the current head. -/
def Before (t : Tape) (a : Int) (w : List Bool) : Prop := Reads t (a-w.length) w

theorem before_snoc {t : Tape} {a : Int} {w : List Bool} {b : Bool}
    (h : Before t a w) (hb : t a = b) : Before t (a+1) (w++[b]) := by
  unfold Before at h ⊢
  have e : a+1-((w++[b]).length : Int) = a-w.length := by simp; omega
  rw [e, reads_append]
  refine ⟨h, ?_⟩
  simpa [Reads] using hb

theorem before_drop {t : Tape} {a : Int} {w : List Bool} (h : Before t a w) (n : Nat)
    (hn : n ≤ w.length) : Before t a (w.drop n) := by
  have ht := reads_drop h n
  have he : a-(w.length : Int)+(n : Int) = a-((w.drop n).length : Int) := by
    simp only [List.length_drop]; omega
  simpa only [Before, he] using ht

theorem before_tail2 {t : Tape} {a : Int} {w : List Bool} (h : Before t a w) :
    Before t a (tail2 w) := before_drop h _ (by omega)

theorem lookup_member {xs : Cells} {i : Int} {b : Bool} (h : lookup xs i = some b) :
    (i,b) ∈ xs := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    rcases x with ⟨j,c⟩
    by_cases hij : i=j
    · subst j
      have hb : c=b := by simpa [lookup] using h
      subst b; simp
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookup,hij] using h))

theorem overlay_fixed {xs : Cells} {t : Tape}
    (h : ∀ p ∈ xs, t p.1 = p.2) : overlay xs t = t := by
  funext i
  unfold overlay
  cases hi : lookup xs i with
  | none => rfl
  | some b => exact (h (i,b) (lookup_member hi)).symm

theorem before_window {t : Tape} {a : Int} {w : List Bool}
    (hne : 0 < w.length) (h : Before t (a+1) w) :
    overlay (cells w) (fun i => t (i+a)) = (fun i => t (i+a)) := by
  apply overlay_fixed
  intro p hp
  obtain ⟨⟨b,i⟩, hi, rfl⟩ := List.mem_map.mp hp
  have ht := reads_get h (List.mk_mem_zipIdx_iff_getElem?.mp hi)
  have e : (i : Int) - ↑(w.length-1) + a = a+1-(w.length : Int)+i := by omega
  simpa only [e] using ht

/-- Pure, decidable semantics of the existing structural edge checker. -/
def EdgeSpec (M : Table) (nodes : Array Node) (roles : Array Role)
    (blocks : Array Block) (r : Role) (bit : Bool) : Prop :=
  match nodes[r.node]? with
  | some (.fork l u) =>
    let child := if bit then u else l
    child < r.node ∧
    match (if bit then r.one else r.zero) with
    | .primitive n a =>
      match nodes[child]? with
      | some (.leaf _ _) => child = n ∧ M r.state bit = some a
      | _ => False
    | .internal k j =>
      match nodes[child]?, roles[k]?, blocks[j]? with
      | some (.fork _ _), some s, some b =>
        s.node = child ∧ s.suffix = tail2 (r.suffix++[bit]) ∧
        b.entry = r.state ∧ b.exit = s.state ∧
        b.word.length ≤ (r.suffix++[bit]).length ∧
        b.word = (r.suffix++[bit]).drop ((r.suffix++[bit]).length-b.word.length)
      | _,_,_ => False
  | _ => False

theorem edgeSpec_of_check (M : Table) (nodes : Array Node) (roles : Array Role)
    (blocks : Array Block) (r : Role) (bit : Bool)
    (h : edgeCheck M nodes roles blocks r bit = true) : EdgeSpec M nodes roles blocks r bit := by
  cases hn : nodes[r.node]? with
  | none => simp [edgeCheck,hn] at h
  | some node =>
    cases node with
    | leaf op arg => simp [edgeCheck,hn] at h
    | fork l u =>
      by_cases hlt : (if bit then u else l) < r.node
      · cases he : (if bit then r.one else r.zero) with
        | primitive n a =>
          cases hc : nodes[if bit then u else l]? with
          | none => simp [edgeCheck,hn,hlt,he,hc] at h
          | some cn =>
            cases cn <;> simp_all [edgeCheck,EdgeSpec]
        | internal k j =>
          cases hc : nodes[if bit then u else l]? with
          | none => simp [edgeCheck,hn,hlt,he,hc] at h
          | some cn =>
            cases cn with
            | leaf op arg => simp [edgeCheck,hn,hlt,he,hc] at h
            | fork l' u' =>
              cases hr : roles[k]? with
              | none => simp [edgeCheck,hn,hlt,he,hc,hr] at h
              | some s =>
                cases hb : blocks[j]? with
                | none => simp [edgeCheck,hn,hlt,he,hc,hr,hb] at h
                | some b =>
                  simp [edgeCheck,hn,hlt,he,hc,hr,hb] at h
                  simpa only [EdgeSpec,hn,he,hc,hr,hb,List.length_append,List.length_singleton] using And.intro hlt h
      · simp [edgeCheck,hn,hlt] at h

theorem edges_of_structure (M : Table) (nodes : Array Node) (roles : Array Role)
    (blocks : Array Block) (root : Nat)
    (h : structuralCheck M nodes roles blocks root = true)
    (rid : Nat) (r : Role) (hr : roles[rid]? = some r) :
    EdgeSpec M nodes roles blocks r false ∧ EdgeSpec M nodes roles blocks r true := by
  unfold structuralCheck at h
  cases h0 : roles[0]? with
  | none => simp [h0] at h
  | some r0 =>
    simp only [h0,Bool.and_eq_true] at h
    have hm : r ∈ roles.toList := by simpa using Array.mem_of_getElem? hr
    have hh := (List.all_eq_true.mp h.2) r hm
    simp only [roleCheck,Bool.and_eq_true] at hh
    exact ⟨edgeSpec_of_check M nodes roles blocks r false hh.1.2,
      edgeSpec_of_check M nodes roles blocks r true hh.2⟩


/-- A source path uses exactly the supplied bits and ends at the specified leaf. -/
inductive SourcePath (nodes : Array Node) : Nat → List Bool → Nat → Nat → Prop
  | leaf {n op arg} (h : nodes[n]? = some (.leaf op arg)) : SourcePath nodes n [] op arg
  | fork {n l u b w op arg} (h : nodes[n]? = some (.fork l u))
      (tail : SourcePath nodes (if b then u else l) w op arg) :
      SourcePath nodes n (b::w) op arg

/-- Exact accepted pre language of the role graph.  A state or two-bit
suffix alone is not a sufficient primitive/return context. -/
inductive RolePath (roles : Array Role) : Nat → List Bool → Nat → Prop
  | nil (rid : Nat) : RolePath roles rid [] rid
  | cons {rid : Nat} {r : Role} {bit : Bool} {next block : Nat}
      {pre : List Bool} {last : Nat}
      (roleAt : roles[rid]? = some r)
      (edge : (if bit then r.one else r.zero) = .internal next block)
      (tail : RolePath roles next pre last) :
      RolePath roles rid (bit :: pre) last

/-- Routed entry retains the consumed pre and its exact role route, so primitive
contracts may quantify the whole continuation rather than only its suffix. -/
def RoutedEntry (M : Table) (nodes : Array Node) (roles : Array Role)
    (first : Nat) (word : List Bool) (q : Nat) (bit : Bool) (op arg : Nat) : Prop :=
  ∃ (pre : List Bool) (rid : Nat) (r : Role) (n : Nat) (action : Action),
    word = pre ++ [bit] ∧ RolePath roles first pre rid ∧
    roles[rid]? = some r ∧ r.state = q ∧
    (if bit then r.one else r.zero) = .primitive n action ∧
    nodes[n]? = some (.leaf op arg) ∧ M q bit = some action

/-- Source-path traversal creates all window witnesses required by `Chain`.
Only the marker/context and the actual source bits are assumed on the tape. -/
theorem source_path_chain_routed
    (M : Table) (nodes : Array Node) (roles : Array Role) (blocks : Array Block)
    (good : ∀ (rid : Nat) (r : Role), roles[rid]? = some r →
      EdgeSpec M nodes roles blocks r false ∧ EdgeSpec M nodes roles blocks r true)
    (checked : blocks.toList.all (blockCheck M) = true)
    {node : Nat} {w : List Bool} {op arg : Nat} (path : SourcePath nodes node w op arg) :
    ∀ (rid : Nat) (r : Role), roles[rid]? = some r → r.node = node →
    ∀ a t, Before t a r.suffix → Reads t a w →
      ∃ steps q bit,
        Chain blocks.toList t r.state a q (a+(w.length : Int)-1) steps ∧
        t (a+(w.length : Int)-1) = bit ∧ RoutedEntry M nodes roles rid w q bit op arg := by
  induction path with
  | leaf hn =>
    intro rid r hr he a t hs hw
    have hg := (good rid r hr).1
    simp [EdgeSpec,he,hn] at hg
  | @fork node l u bit w op arg hn tail ih =>
    intro rid r hr he a t hs hw
    have hg : EdgeSpec M nodes roles blocks r bit := by
      cases bit
      · exact (good rid r hr).1
      · exact (good rid r hr).2
    simp only [EdgeSpec, he, hn] at hg
    cases hedge : (if bit then r.one else r.zero) with
    | primitive n action =>
      simp only [hedge] at hg
      cases hc : nodes[if bit then u else l]? with
      | none => simp [hc] at hg
      | some cn =>
        cases cn with
        | fork l' u' => simp [hc] at hg
        | leaf op' arg' =>
          simp only [hc] at hg
          cases tail with
          | leaf ht =>
            rw [hc] at ht
            cases ht
            have heq : (if bit then u else l) = n := hg.2.1
            refine ⟨0, r.state, bit, ?_, ?_, ?_⟩
            · simpa using (Chain.done (bs := blocks.toList) (t := t) r.state a)
            · simpa using hw.1
            · exact ⟨[],rid,r,n,action,rfl,RolePath.nil rid,hr,rfl,hedge,heq ▸ hc,hg.2.2⟩
          | fork ht _ => rw [hc] at ht; cases ht
    | internal k j =>
      simp only [hedge] at hg
      cases hc : nodes[if bit then u else l]? with
      | none => simp [hc] at hg
      | some cn =>
        cases cn with
        | leaf op' arg' => simp [hc] at hg
        | fork l' u' =>
          cases hrole : roles[k]? with
          | none => simp [hc,hrole] at hg
          | some s =>
            cases hblock : blocks[j]? with
            | none => simp [hc,hrole,hblock] at hg
            | some b =>
              simp only [hc,hrole,hblock] at hg
              obtain ⟨_, hsnode,hssuffix,hentry,hexit,hlen,hword⟩ := hg
              have hmem : b ∈ blocks.toList := by
                simpa using (Array.mem_of_getElem? hblock)
              have hbcheck := (List.all_eq_true.mp checked) b hmem
              have hbpos : 0 < b.word.length := by
                have hh : (0 < b.steps ∧ 0 < b.word.length) ∧
                    check M b.steps b.entry 0 (cells b.word) b.exit 1 = true := by
                  simpa [blockCheck, Bool.and_eq_true] using hbcheck
                exact hh.1.2
              have hall : Before t (a+1) (r.suffix++[bit]) := before_snoc hs hw.1
              have hbword : Before t (a+1) b.word := by
                rw [hword]
                exact before_drop hall _ (by omega)
              have hsc : Before t (a+1) s.suffix := by
                rw [hssuffix]; exact before_tail2 hall
              obtain ⟨steps,q,last,hchain,ht,hend⟩ := ih k s hrole hsnode (a+1) t hsc hw.2
              have hwindow := before_window hbpos hbword
              have hmore := Chain.more b a q (a+1+(w.length : Int)-1) steps hmem hwindow
                (by simpa [hexit] using hchain)
              have hpos : a+1+(w.length : Int)-1 = a+((bit::w).length : Int)-1 := by
                simp only [List.length_cons]; omega
              refine ⟨b.steps+steps,q,last,?_,?_,?_⟩
              · simpa only [hentry,hpos] using hmore
              · simpa only [hpos] using ht
              · obtain ⟨pre,final,s',leaf,action,hsplit,hroute,hat,hstate,he',hleaf,hrow⟩ := hend
                refine ⟨bit::pre,final,s',leaf,action,?_,RolePath.cons hr hedge hroute,
                  hat,hstate,he',hleaf,hrow⟩
                simp only [hsplit, List.cons_append]

/-- A chain of bounded positive blocks has a bounded duration. -/
theorem chain_bounds {bs : List Block} {t : Tape}
    (durations : ∀ b ∈ bs, 1 ≤ b.steps ∧ b.steps ≤ 7)
    {q q' : Nat} {a a' : Int} {steps : Nat} (hc : Chain bs t q a q' a' steps) :
    ∃ k : Nat, a' = a+k ∧ k ≤ steps ∧ steps ≤ 7*k := by
  induction hc with
  | done => exact ⟨0,by omega,by omega,by omega⟩
  | more b a q' a' n hb hw ht ih =>
    obtain ⟨k,hk,lo,hi⟩ := ih
    obtain ⟨blo,bhi⟩ := durations b hb
    exact ⟨k+1,by omega,by omega,by omega⟩

end SetTheory.BusyBeaver.ZFC.DecoderPaths

namespace SetTheory.BusyBeaver.ZFC.K215SourcePaths
open FramedWindow DecoderCertificate DecoderPaths K215Decoder
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem semantic_edges (rid : Nat) (r : Role) (hr : roles[rid]? = some r) :
    EdgeSpec formal sourceNodes roles blocks r false ∧
      EdgeSpec formal sourceNodes roles blocks r true :=
  edges_of_structure formal sourceNodes roles blocks sourceRoot structure_checked rid r hr

def rootRole : Role := ⟨201,84,[true],.internal 1 0,.internal 9 1⟩
theorem root_role : roles[0]? = some rootRole := by decide +kernel

theorem duration_checked : blocks.toList.all (fun b => decide (1 ≤ b.steps ∧ b.steps ≤ 7)) = true :=
  by decide +kernel

theorem durations (b : Block) (hb : b ∈ blocks.toList) : 1 ≤ b.steps ∧ b.steps ≤ 7 :=
  of_decide_eq_true ((List.all_eq_true.mp duration_checked) b hb)

/-- For every valid source path and arbitrary surrounding infinite tape, the
literal K215 decoder reaches the exact primitive entry, preserving all cells.
No per-block window assumptions remain. -/
theorem reaches_primitive_routed {w : List Bool} {op arg : Nat}
    (path : SourcePath sourceNodes sourceRoot w op arg)
    (a : Int) (t : Tape) (marker : t (a-1) = true) (word : Reads t a w) :
    ∃ steps q bit,
      w.length-1 ≤ steps ∧ steps ≤ 7*(w.length-1) ∧
      run (fullStep formal) steps ⟨84,a,t⟩ = some ⟨q,a+(w.length : Int)-1,t⟩ ∧
      t (a+(w.length : Int)-1) = bit ∧ RoutedEntry formal sourceNodes roles 0 w q bit op arg := by
  have hc : Before t a rootRole.suffix := by simpa [Before,Reads,rootRole] using marker
  obtain ⟨steps,q,bit,hchain,ht,hend⟩ :=
    source_path_chain_routed formal sourceNodes roles blocks semantic_edges all_blocks_checked
      path 0 rootRole root_role rfl a t hc word
  obtain ⟨k,hk,hlo,hhi⟩ := chain_bounds durations hchain
  have he : k = w.length-1 := by omega
  subst k
  exact ⟨steps,q,bit,hlo,hhi,chain_sound formal blocks.toList all_blocks_checked t hchain,ht,hend⟩


#print axioms semantic_edges
#print axioms reaches_primitive_routed
end SetTheory.BusyBeaver.ZFC.K215SourcePaths
