import DecoderCertificate

/-! Semantic propagation of the finite suffix context.

This extends the incoming FramedWindow/DecoderCertificate component: successful
local blocks no longer need separate arbitrary-tape window witnesses at every
edge. A finite coverage check transports one initial context along an entire
internal decoder route. There is no register-box or primitive-return claim here.
-/
namespace DecoderContext
open FramedWindow DecoderCertificate

/-- A partial window's listed facts hold of the complete tape. -/
def Matches (xs : Cells) (t : Tape) : Prop :=
  ∀ i b, lookup xs i = some b → t i = b

def MatchesAt (xs : Cells) (a : Int) (t : Tape) : Prop :=
  Matches xs (fun i => t (i+a))

theorem matches_overlay {xs : Cells} {t : Tape} (h : Matches xs t) :
    overlay xs t = t := by
  funext i
  cases hi : lookup xs i with
  | none => simp [overlay, hi]
  | some b => simpa [overlay, hi] using (h i b hi).symm

theorem matches_cons {xs : Cells} {t : Tape} {i : Int} {b : Bool}
    (h : Matches xs t) (hi : t i = b) : Matches ((i,b)::xs) t := by
  intro j v hj
  by_cases hji : j = i
  · subst j
    have hv : b = v := by simpa [lookup] using hj
    exact hi.trans hv
  · exact h j v (by simpa [lookup, hji] using hj)

theorem lookup_mem {xs : Cells} {i : Int} {b : Bool}
    (h : lookup xs i = some b) : (i,b) ∈ xs := by
  induction xs with
  | nil => simp [lookup] at h
  | cons x xs ih =>
    rcases x with ⟨j,v⟩
    by_cases hij : i = j
    · subst j
      have hv : v = b := by simpa [lookup] using h
      subst v
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookup, hij] using h))

/-- Every demanded cell is present with the same value among known facts. -/
def covers (known demanded : Cells) : Bool :=
  demanded.all (fun x => decide (lookup known x.1 = some x.2))

theorem covers_sound {known demanded : Cells} {t : Tape}
    (hc : covers known demanded = true) (hm : Matches known t) :
    Matches demanded t := by
  intro i b hb
  have hh := (List.all_eq_true.mp hc) (i,b) (lookup_mem hb)
  exact hm i b (of_decide_eq_true hh)

def shiftCells (d : Int) (xs : Cells) : Cells :=
  xs.map (fun x => (x.1+d,x.2))

theorem lookup_shift (d : Int) (xs : Cells) (i : Int) :
    lookup (shiftCells d xs) (i+d) = lookup xs i := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨j,b⟩
    have he : i+d = j+d ↔ i = j := by omega
    have ih2 : lookup (xs.map (fun x => (x.1+d,x.2))) (i+d) = lookup xs i := ih
    simp [shiftCells, lookup, he, ih2]

theorem matches_shift_at {xs : Cells} {a d : Int} {t : Tape}
    (h : MatchesAt (shiftCells d xs) a t) : MatchesAt xs (a+d) t := by
  intro i b hi
  have hs : lookup (shiftCells d xs) (i+d) = some b := by
    rw [lookup_shift]; exact hi
  have hh := h (i+d) b hs
  have he : i+d+a = i+(a+d) := by omega
  simpa [he] using hh

/-- The role suffix occupies the cells strictly preceding the head. -/
def beforeCells (word : List Bool) : Cells :=
  word.zipIdx.map (fun (b,i) => ((i : Int) - (word.length : Nat), b))

def context (r : Role) (bit : Bool) : Cells :=
  (0,bit) :: beforeCells r.suffix

def edge (r : Role) (bit : Bool) : Edge := if bit then r.one else r.zero

/-- This supplementary finite check is semantic: the current known cells
supply both the local execution window and the next role's preceding cells. -/
def edgeContextCheck (roles : Array Role) (blocks : Array Block)
    (r : Role) (bit : Bool) : Bool :=
  match edge r bit with
  | .primitive _ _ => true
  | .internal k j =>
    match roles[k]?, blocks[j]? with
    | some s, some b =>
        decide (b.entry = r.state ∧ b.exit = s.state) &&
        covers (context r bit) (cells b.word) &&
        covers (context r bit) (shiftCells 1 (beforeCells s.suffix))
    | _, _ => false

def contextCheck (roles : Array Role) (blocks : Array Block) : Bool :=
  roles.toList.all (fun r => edgeContextCheck roles blocks r false &&
    edgeContextCheck roles blocks r true)

theorem checked_edge {roles : Array Role} {blocks : Array Block}
    (hc : contextCheck roles blocks = true) {r : Role} (hr : r ∈ roles.toList)
    (bit : Bool) : edgeContextCheck roles blocks r bit = true := by
  have hh := (List.all_eq_true.mp hc) r hr
  have hh' : edgeContextCheck roles blocks r false = true ∧
      edgeContextCheck roles blocks r true = true := by
    simpa only [Bool.and_eq_true] using hh
  cases bit
  · exact hh'.1
  · exact hh'.2

theorem internal_context_sound (M : Table) {roles : Array Role} {blocks : Array Block}
    {r s : Role} {b : Block} {bit : Bool} {k j : Nat}
    (he : edge r bit = .internal k j)
    (hs : roles[k]? = some s) (hb : blocks[j]? = some b)
    (hc : edgeContextCheck roles blocks r bit = true)
    (hv : blockCheck M b = true)
    (a : Int) (t : Tape)
    (hm : MatchesAt (beforeCells r.suffix) a t) (ht : t a = bit) :
    (0 < b.steps ∧ run (fullStep M) b.steps ⟨r.state,a,t⟩ =
      some ⟨s.state,a+1,t⟩) ∧
      MatchesAt (beforeCells s.suffix) (a+1) t := by
  have hh : (b.entry = r.state ∧ b.exit = s.state) ∧
      covers (context r bit) (cells b.word) = true ∧
      covers (context r bit) (shiftCells 1 (beforeCells s.suffix)) = true := by
    simpa [edgeContextCheck, he, hs, hb, Bool.and_eq_true, and_assoc] using hc
  have hk : MatchesAt (context r bit) a t :=
    matches_cons hm (by simpa using ht)
  have hw : overlay (cells b.word) (fun i => t (i+a)) = (fun i => t (i+a)) :=
    matches_overlay (covers_sound hh.2.1 hk)
  have hn : MatchesAt (beforeCells s.suffix) (a+1) t :=
    matches_shift_at (covers_sound hh.2.2 hk)
  have runb := block_sound M b hv a t hw
  rw [hh.1.1, hh.1.2] at runb
  exact ⟨runb, hn⟩

/-- A finite route specifies only role/edge indices, never tape-window proofs. -/
inductive Route (roles : Array Role) (blocks : Array Block) :
    Role → List Bool → Role → Nat → Prop
  | done (r : Role) : Route roles blocks r [] r 0
  | more {r s f : Role} {bit : Bool} {k j n : Nat} {b : Block} {bits : List Bool}
      (member : r ∈ roles.toList)
      (edge_eq : edge r bit = .internal k j)
      (next_role : roles[k]? = some s) (next_block : blocks[j]? = some b)
      (tail : Route roles blocks s bits f n) :
      Route roles blocks r (bit::bits) f (b.steps+n)

/-- The input pointer bits occur successively on the unchanged whole tape. -/
def Reads (t : Tape) (a : Int) : List Bool → Prop
  | [] => True
  | b::bs => t a = b ∧ Reads t (a+1) bs

theorem route_sound (M : Table) {roles : Array Role} {blocks : Array Block}
    (hall : blocks.toList.all (blockCheck M) = true)
    (hc : contextCheck roles blocks = true)
    {r f : Role} {bits : List Bool} {n : Nat}
    (route : Route roles blocks r bits f n)
    (a : Int) (t : Tape)
    (hm : MatchesAt (beforeCells r.suffix) a t) (ht : Reads t a bits) :
    run (fullStep M) n ⟨r.state,a,t⟩ =
      some ⟨f.state,a+(bits.length : Int),t⟩ ∧
    MatchesAt (beforeCells f.suffix) (a+(bits.length : Int)) t := by
  induction route generalizing a with
  | done r =>
    constructor
    · simp [run]
    · simpa using hm
  | @more r s f bit k j n b bits hr he hs hb tail ih =>
    have hbmem : b ∈ blocks.toList := by
      simpa using Array.mem_of_getElem? hb
    have hv := (List.all_eq_true.mp hall) b hbmem
    have one := internal_context_sound M he hs hb (checked_edge hc hr bit) hv a t hm ht.1
    have rest := ih (a+1) one.2 ht.2
    have hp : a+1+(bits.length : Int) = a+((bit::bits).length : Int) := by simp; omega
    constructor
    · rw [run_add, one.1.2]
      simpa [hp] using rest.1
    · simpa [hp] using rest.2

/-- A nonempty internal route cannot be certified by zero machine time. -/
theorem route_positive (M : Table) {roles : Array Role} {blocks : Array Block}
    (hall : blocks.toList.all (blockCheck M) = true)
    {r f : Role} {bits : List Bool} {n : Nat}
    (route : Route roles blocks r bits f n) (hne : bits ≠ []) : 0 < n := by
  cases route with
  | done => contradiction
  | @more r s f bit k j n b bits hr he hs hb tail =>
    have hbmem : b ∈ blocks.toList := by simpa using Array.mem_of_getElem? hb
    have hv := (List.all_eq_true.mp hall) b hbmem
    have hp : 0 < b.steps ∧ 0 < b.word.length := by
      have h : decide (0 < b.steps ∧ 0 < b.word.length) = true ∧
          check M b.steps b.entry 0 (cells b.word) b.exit 1 = true := by
        simpa only [blockCheck, Bool.and_eq_true] using hv
      exact of_decide_eq_true h.1
    omega

/-- Follow a supplied pointer prefix through internal decoder edges only. -/
def follow (roles : Array Role) (blocks : Array Block) :
    Role → List Bool → Option (Role × Nat)
  | r, [] => some (r,0)
  | r, bit::bits => do
      let .internal k j := edge r bit | none
      let s ← roles[k]?
      let b ← blocks[j]?
      let (f,n) ← follow roles blocks s bits
      return (f,b.steps+n)

theorem follow_route {roles : Array Role} {blocks : Array Block}
    {r f : Role} {bits : List Bool} {n : Nat}
    (hr : r ∈ roles.toList) (hf : follow roles blocks r bits = some (f,n)) :
    Route roles blocks r bits f n := by
  induction bits generalizing r f n with
  | nil =>
      have h : r = f ∧ 0 = n := by simpa [follow] using hf
      rcases h with ⟨rfl,rfl⟩
      exact Route.done _
  | cons bit bits ih =>
      cases he : edge r bit with
      | primitive node action => simp [follow, he] at hf
      | internal k j =>
          cases hs : roles[k]? with
          | none => simp [follow, he, hs] at hf
          | some s =>
              cases hb : blocks[j]? with
              | none => simp [follow, he, hs, hb] at hf
              | some b =>
                  cases ht : follow roles blocks s bits with
                  | none => simp [follow, he, hs, hb, ht] at hf
                  | some fn =>
                      rcases fn with ⟨f',n'⟩
                      have h : f' = f ∧ b.steps+n' = n := by
                        simpa [follow, he, hs, hb, ht] using hf
                      rcases h with ⟨rfl,rfl⟩
                      have hsm : s ∈ roles.toList := by
                        simpa using Array.mem_of_getElem? hs
                      exact Route.more hr he hs hb (ih hsm ht)

/-- Successful finite lookup plus one marker context establishes all full-tape
window hypotheses; callers supply no intermediate semantic assertions. -/
theorem follow_sound (M : Table) {roles : Array Role} {blocks : Array Block}
    (hall : blocks.toList.all (blockCheck M) = true)
    (hc : contextCheck roles blocks = true)
    {r f : Role} {bits : List Bool} {n : Nat}
    (hr : r ∈ roles.toList) (hf : follow roles blocks r bits = some (f,n))
    (a : Int) (t : Tape)
    (hm : MatchesAt (beforeCells r.suffix) a t) (ht : Reads t a bits) :
    run (fullStep M) n ⟨r.state,a,t⟩ =
      some ⟨f.state,a+(bits.length : Int),t⟩ ∧
    MatchesAt (beforeCells f.suffix) (a+(bits.length : Int)) t :=
  route_sound M hall hc (follow_route hr hf) a t hm ht

/-- Read a source-tree path whose endpoint remains internal. -/
def nodeFollow (nodes : Array Node) : Nat → List Bool → Option Nat
  | n, [] =>
      match nodes[n]? with
      | some (.fork _ _) => some n
      | _ => none
  | n, bit::rest =>
      match nodes[n]? with
      | some (.fork l u) => nodeFollow nodes (if bit then u else l) rest
      | _ => none

theorem nodeFollow_fork {nodes : Array Node} {n m : Nat} {bits : List Bool}
    (h : nodeFollow nodes n bits = some m) : ∃ l u, nodes[n]? = some (.fork l u) := by
  cases hn : nodes[n]? with
  | none => cases bits <;> simp [nodeFollow,hn] at h
  | some nd =>
      cases nd with
      | leaf op arg => cases bits <;> simp [nodeFollow,hn] at h
      | fork l u => exact ⟨l,u,rfl⟩

/-- Finite linkage between internal source children and decoder roles.
Leaf branches remain the domain of the existing primitive-runtime proof. -/
def sourceEdgeCheck (nodes : Array Node) (roles : Array Role) (blocks : Array Block)
    (r : Role) (bit : Bool) : Bool :=
  match nodes[r.node]? with
  | some (.fork l u) =>
      let child := if bit then u else l
      match nodes[child]? with
      | some (.leaf _ _) => true
      | some (.fork _ _) =>
          match edge r bit with
          | .primitive _ _ => false
          | .internal k j =>
              match roles[k]?, blocks[j]? with
              | some s, some _ => decide (s.node = child)
              | _, _ => false
      | _ => false
  | _ => false

def sourceCheck (nodes : Array Node) (roles : Array Role) (blocks : Array Block) : Bool :=
  roles.toList.all (fun r => sourceEdgeCheck nodes roles blocks r false &&
    sourceEdgeCheck nodes roles blocks r true)

theorem source_checked_edge {nodes : Array Node} {roles : Array Role} {blocks : Array Block}
    (hc : sourceCheck nodes roles blocks = true) {r : Role} (hr : r ∈ roles.toList)
    (bit : Bool) : sourceEdgeCheck nodes roles blocks r bit = true := by
  have hh := (List.all_eq_true.mp hc) r hr
  have hh' : sourceEdgeCheck nodes roles blocks r false = true ∧
      sourceEdgeCheck nodes roles blocks r true = true := by
    simpa only [Bool.and_eq_true] using hh
  cases bit
  · exact hh'.1
  · exact hh'.2

/-- Every internal source path has a decoder route; only 234 role certificates
are used, independently of the number of unfolded source occurrences. -/
theorem source_path_follow {nodes : Array Node} {roles : Array Role} {blocks : Array Block}
    (hc : sourceCheck nodes roles blocks = true)
    {r : Role} {bits : List Bool} {m : Nat} (hr : r ∈ roles.toList)
    (hn : nodeFollow nodes r.node bits = some m) :
    ∃ f n, follow roles blocks r bits = some (f,n) ∧ f.node = m := by
  induction bits generalizing r m with
  | nil =>
      obtain ⟨l,u,hs⟩ := nodeFollow_fork hn
      have hm : r.node = m := by simpa [nodeFollow,hs] using hn
      exact ⟨r,0,rfl,hm⟩
  | cons bit bits ih =>
      obtain ⟨l,u,hs⟩ := nodeFollow_fork hn
      have hrest : nodeFollow nodes (if bit then u else l) bits = some m := by
        simpa [nodeFollow,hs] using hn
      obtain ⟨cl,cu,hchild⟩ := nodeFollow_fork hrest
      have hec := source_checked_edge hc hr bit
      cases he : edge r bit with
      | primitive nd act => simp [sourceEdgeCheck,hs,hchild,he] at hec
      | internal k j =>
          cases hk : roles[k]? with
          | none => simp [sourceEdgeCheck,hs,hchild,he,hk] at hec
          | some s =>
              cases hj : blocks[j]? with
              | none => simp [sourceEdgeCheck,hs,hchild,he,hk,hj] at hec
              | some b =>
                  have hsn : s.node = (if bit then u else l) := by
                    simpa [sourceEdgeCheck,hs,hchild,he,hk,hj] using hec
                  have hsm : s ∈ roles.toList := by simpa using Array.mem_of_getElem? hk
                  obtain ⟨f,n,hf,hm⟩ := ih hsm (by simpa [hsn] using hrest)
                  refine ⟨f,b.steps+n,?_,hm⟩
                  simp [follow,he,hk,hj,hf]

#print axioms internal_context_sound
#print axioms route_sound
#print axioms route_positive
#print axioms follow_sound
#print axioms source_path_follow
end DecoderContext
