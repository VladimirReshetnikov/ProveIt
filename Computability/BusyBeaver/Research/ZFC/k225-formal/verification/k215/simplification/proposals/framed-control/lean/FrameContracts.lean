import K215FrameEngine
import BusyBeaver.ZFC.KPathFrame
import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.DecoderPaths

/-!
Source and whole-tape interfaces for framed K215 control templates.
The source operation, its suffix, and the selected decoder state remain explicit.
The role selector reuses the method of Source193's KResidualRouting215.
-/
namespace SetTheory.BusyBeaver.ZFC.KFrameContracts
open KZip KRuntimeCore KLeftFrame KFramedTemplates KTableCore RegisterPath

structure Meta where
  q : Nat
  suffix : List Bool
  result : List Bool
  isBreak : Bool
  argument : Nat
  deriving DecidableEq, Repr, Inhabited

def action (m : Meta) : RegisterPath.Edge :=
  if m.isBreak then .brk m.argument else .cont m.argument

def sourceResult (m : Meta) (P : List Bool) : List Bool :=
  if m.isBreak then breakPath m.argument P else continuePath m.argument P

def sourceGuard (m : Meta) : Prop :=
  if m.isBreak then
    m.argument ≤ m.suffix.count false ∧
      false ∈ stripPath false m.argument m.suffix ∧
      breakPath m.argument m.suffix = m.result
  else
    m.argument ≤ m.suffix.count true ∧
      continuePath m.argument m.suffix = m.result

instance (m : Meta) : Decidable (sourceGuard m) := by
  unfold sourceGuard
  split <;> infer_instance

def localStart (m : Meta) : SConf :=
  (m.q, false, m.suffix.reverse.tail.map Seg.bit,
    [.bit (m.suffix.reverse.headD false), .run false 1 16,
      .bit true, .box (.plain .none)])

def canonicalRight (m : Meta) : List Seg :=
  m.result.map Seg.bit ++
    [.run false 1 (16 + m.suffix.length - m.result.length),
      .bit true, .box (.plain .none)]

/-- The exact zipper entry of a primitive: head on the final path bit,
    preceding path bits to its left, then the leading marker and blank exterior.
    The gap argument is the actual number of blank cells. -/
def leafPort (q : Nat) (word : List Bool) (gap : Nat) (vs : List Nat) : Conf :=
  zc q (word.reverse.tail ++ [true])
    (word.reverse.headD false ::
      (List.replicate gap false ++ true :: sepsR vs))

private theorem flat_append (n : Nat) (vs : List Nat) (xs ys : List Seg) :
    flat n vs (xs ++ ys) = flat n vs xs ++ flat n vs ys := List.flatMap_append

/-- The symbolic frame is exactly the complete primitive-entry tape. -/
theorem localStart_leafPort (m : Meta) (hs : m.suffix ≠ [])
    (P : List Bool) (n : Nat) (vs : List Nat) :
    conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) (localStart m)) =
      leafPort m.q (P ++ m.suffix) (n + 16) vs := by
  cases hr : m.suffix.reverse with
  | nil =>
    have he : m.suffix = [] := by simpa using congrArg List.reverse hr
    exact (hs he).elim
  | cons b tail =>
    have hfull : (P ++ m.suffix).reverse = b :: (tail ++ P.reverse) := by
      simp only [List.reverse_append, hr, List.cons_append]
    simp only [localStart, addLeft, conc, hr, List.tail_cons, List.headD_cons,
      leafPort, hfull, flat_append, flat_bits, List.append_assoc]
    simp [flat, segList, boxList]

def Shape (m : Meta) (t : LocalTemplate) : Prop :=
  m.suffix ≠ [] ∧ m.result.length ≤ m.suffix.length ∧ sourceGuard m ∧
    t.start = localStart m ∧ norm t.right = norm (canonicalRight m)

instance (m : Meta) (t : LocalTemplate) : Decidable (Shape m t) := by
  unfold Shape
  infer_instance

theorem source_frame {m : Meta} (h : sourceGuard m) (P : List Bool) :
    sourceResult m (P ++ m.suffix) = P ++ m.result := by
  cases hb : m.isBreak with
  | false =>
      have hs : m.argument ≤ m.suffix.count true ∧
          continuePath m.argument m.suffix = m.result := by
        simpa [sourceGuard, hb] using h
      simpa [sourceResult, hb, hs.2] using
        KPathFrame.continuePath_append P m.suffix m.argument hs.1
  | true =>
      have hs : m.argument ≤ m.suffix.count false ∧
          false ∈ stripPath false m.argument m.suffix ∧
          breakPath m.argument m.suffix = m.result := by
        simpa [sourceGuard, hb] using h
      simpa [sourceResult, hb, hs.2.2] using
        KPathFrame.breakPath_append P m.suffix m.argument hs.1 hs.2.1

theorem flat_canonical (m : Meta) (n : Nat) (vs : List Nat) :
    flat n vs (canonicalRight m) = m.result ++
      List.replicate (n + (16 + m.suffix.length - m.result.length)) false ++
        true :: sepsR vs := by
  unfold canonicalRight
  rw [show flat n vs (m.result.map Seg.bit ++
      [.run false 1 (16 + m.suffix.length - m.result.length),
       .bit true, .box (.plain .none)]) =
      flat n vs (m.result.map Seg.bit) ++
      flat n vs [.run false 1 (16 + m.suffix.length - m.result.length),
       .bit true, .box (.plain .none)] by exact List.flatMap_append]
  rw [flat_bits]
  simp [flat, segList, boxList, List.append_assoc]

/-- This is a concrete-machine theorem: the register-engine and Home
    hypotheses are discharged by the maintained engine proofs. -/
theorem whole_contract {m : Meta} {t : LocalTemplate}
    (ht : t ∈ templates) (hs : Shape m t)
    (P : List Bool) (n : Nat) {vs : List Nat} (hv : Valid none vs)
    (hw : wordEnd tm215 t.returnState (P.reverse ++ [true]) = some 2) :
    Reach1 tm215
      (conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) (localStart m)))
      (zc 84 [true] (P ++ m.result ++
        List.replicate (n + (16 + m.suffix.length - m.result.length)) false ++
          true :: sepsR vs)) := by
  have hp := K215FrameEngine.template_sound215 ht n hv P hw
  rw [hs.2.2.2.1] at hp
  have hr : flat n vs t.right = flat n vs (canonicalRight m) := by
    rw [← flatT_norm, hs.2.2.2.2, flatT_norm]
  rw [hr, flat_canonical] at hp
  simpa only [List.append_assoc] using hp

/-- Follow only internal role edges, rejecting a premature primitive. -/
def followRoles (rs : Array DecoderCertificate.Role) : Nat → List Bool → Option Nat
  | rid, [] => some rid
  | rid, b :: pre => do
      let r ← rs[rid]?
      match (if b then r.one else r.zero) with
      | .primitive _ _ => none
      | .internal next _ => followRoles rs next pre

def portState (rs : Array DecoderCertificate.Role) (first : Nat)
    (pre : List Bool) : Option Nat := do
  let rid ← followRoles rs first pre
  let r ← rs[rid]?
  pure r.state

theorem followRoles_of_path {rs : Array DecoderCertificate.Role}
    {first last : Nat} {pre : List Bool}
    (h : DecoderPaths.RolePath rs first pre last) :
    followRoles rs first pre = some last := by
  induction h with
  | nil rid => rfl
  | cons hat hedge ht ih =>
      simpa [followRoles, hat, hedge] using ih

theorem portState_of_path {rs : Array DecoderCertificate.Role}
    {first last : Nat} {pre : List Bool} {r : DecoderCertificate.Role}
    (h : DecoderPaths.RolePath rs first pre last) (hat : rs[last]? = some r) :
    portState rs first pre = some r.state := by
  simp [portState, followRoles_of_path h, hat]

structure Caller where
  word : List Bool
  «prefix» : List Bool
  templateIndex : Nat
  deriving DecidableEq, Repr

def CallerOK (m : Meta) (t : LocalTemplate) (c : Caller) : Prop :=
  c.word = c.prefix ++ m.suffix ∧ c.word.length ≤ 48 ∧
    RegisterPath.walk KSource215.p215 (KSource215.p215.nnodes + 1)
      KSource215.p215.root c.word 0 = some (action m, c.word.length) ∧
    portState K215Decoder.roles 0 c.word.dropLast = some m.q ∧
    wordEnd tm215 t.returnState (c.prefix.reverse ++ [true]) = some 2

instance (m : Meta) (t : LocalTemplate) (c : Caller) : Decidable (CallerOK m t c) := by
  unfold CallerOK
  infer_instance

/-- Every certified caller has both the intended source action and its
    positive concrete run, uniformly in gaps and all valid register values. -/
theorem caller_contract {m : Meta} {t : LocalTemplate} {c : Caller}
    (ht : t ∈ templates) (hs : Shape m t) (hc : CallerOK m t c)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    sourceResult m c.word = c.prefix ++ m.result ∧
    Reach1 tm215
      (conc n vs (addLeft (c.prefix.reverse.map Seg.bit ++ [.bit true]) (localStart m)))
      (zc 84 [true] (c.prefix ++ m.result ++
        List.replicate (n + (16 + m.suffix.length - m.result.length)) false ++
          true :: sepsR vs)) := by
  constructor
  · rw [hc.1]
    exact source_frame hs.2.2.1 c.prefix
  · exact whole_contract ht hs c.prefix n hv hc.2.2.2.2

/-- The same caller theorem with an explicit, complete primitive-entry tape. -/
theorem caller_contract_port {m : Meta} {t : LocalTemplate} {c : Caller}
    (ht : t ∈ templates) (hs : Shape m t) (hc : CallerOK m t c)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    sourceResult m c.word = c.prefix ++ m.result ∧
    Reach1 tm215
      (leafPort m.q c.word (n + 16) vs)
      (zc 84 [true] (c.prefix ++ m.result ++
        List.replicate (n + (16 + m.suffix.length - m.result.length)) false ++
          true :: sepsR vs)) := by
  have h := caller_contract ht hs hc n hv
  rw [localStart_leafPort m hs.1, ← hc.1] at h
  exact h

/-- The gap convention used by production source simulation, with no
    subtraction or frame condition suppressed: 64 minus the whole path length. -/
theorem caller_contract_standard {m : Meta} {t : LocalTemplate} {c : Caller}
    (ht : t ∈ templates) (hs : Shape m t) (hc : CallerOK m t c)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    sourceResult m c.word = c.prefix ++ m.result ∧
    Reach1 tm215
      (leafPort m.q c.word (n + (64 - c.word.length)) vs)
      (zc 84 [true] (sourceResult m c.word ++
        List.replicate (n + (64 - (sourceResult m c.word).length)) false ++
          true :: sepsR vs)) := by
  have h := caller_contract_port ht hs hc (n + 48 - c.word.length) hv
  have hlen := hc.2.1
  have hshort := hs.2.1
  have hword : c.word.length = c.prefix.length + m.suffix.length := by
    simp only [hc.1, List.length_append]
  have hinput : n + 48 - c.word.length + 16 = n + (64 - c.word.length) := by omega
  have houtput : (n + 48 - c.word.length) +
      (16 + m.suffix.length - m.result.length) =
      n + (64 - (c.prefix ++ m.result).length) := by
    simp only [List.length_append]
    omega
  rw [hinput, houtput] at h
  rw [h.1]
  exact ⟨rfl, h.2⟩

#print axioms source_frame
#print axioms flat_canonical
#print axioms localStart_leafPort
#print axioms whole_contract
#print axioms portState_of_path
#print axioms caller_contract
#print axioms caller_contract_standard
end SetTheory.BusyBeaver.ZFC.KFrameContracts
