import BusyBeaver.ZFC.KLeftFrame215
import BusyBeaver.ZFC.KControlFrame

/-! Whole-tape framed contracts, checked against the existing source path actions.
The finite checks bind every symbolic runtime template to its exact source suffix,
output suffix, routed state, and unchanged register file. -/
namespace SetTheory.BusyBeaver.ZFC.KFramedControl215
open KZip KRuntimeCore KLeftFrame KLeftFrame215 KTableCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Descriptor where
  index : Fin 35
  state : Nat
  suffix : List Bool
  result : List Bool
  action : RegisterPath.Edge

def runtime (d : Descriptor) : Template :=
  templates.get ⟨d.index.val, by rw [template_count]; exact d.index.isLt⟩

theorem runtime_mem (d : Descriptor) : runtime d ∈ templates := List.get_mem _ _

/-- The head is on the final suffix bit; lists on the left are nearest-first. -/
def suffixStart (q : Nat) (s : List Bool) : SConf :=
  (q, false, s.reverse.tail.map Seg.bit,
    [.bit (s.reverse.headD false), .run false 1 16, .bit true, .box (.plain .none)])

def outputRight (s e : List Bool) : List Seg :=
  e.map Seg.bit ++ [.run false 1 (16 + s.length - e.length), .bit true, .box (.plain .none)]

def suffixPort (q : Nat) (p s : List Bool) (n : Nat) (vs : List Nat) : Conf :=
  zc q (s.reverse.tail ++ p.reverse ++ [true])
    (s.reverse.headD false :: (List.replicate (n + 16) false ++ true :: sepsR vs))

def dispatch (p s e : List Bool) (n : Nat) (vs : List Nat) : Conf :=
  zc 84 [true] (p ++ e ++ List.replicate (n + 16 + s.length - e.length) false ++ true :: sepsR vs)

theorem suffixStart_conc (q : Nat) (p s : List Bool) (n : Nat) (vs : List Nat) :
    conc n vs (addLeft (p.reverse.map Seg.bit ++ [.bit true]) (suffixStart q s)) =
      suffixPort q p s n vs := by
  simp only [suffixStart, addLeft, conc, flat_append, flat_bits, flat_cons,
    segList, flat_nil, boxList, suffixPort, Nat.one_mul, List.append_nil,
    List.singleton_append, List.append_assoc]

theorem outputRight_flat (p s e : List Bool) (n : Nat) (vs : List Nat)
    (he : e.length ≤ s.length) :
    zc 84 [true] (p ++ flat n vs (outputRight s e)) = dispatch p s e n vs := by
  have hn : n + (16 + s.length - e.length) = n + 16 + s.length - e.length := by omega
  simp only [outputRight, flat_append, flat_bits, flat_cons, flat_nil,
    segList, Nat.one_mul, boxList, List.append_nil]
  rw [hn]
  simp only [dispatch, List.singleton_append, List.append_assoc]

def aligned (d : Descriptor) : Bool :=
  decide ((runtime d).start = suffixStart d.state d.suffix ∧
    norm (runtime d).right = norm (outputRight d.suffix d.result) ∧
    KControlFrame.controlSuffix d.action d.suffix = some d.result ∧
    d.result.length ≤ d.suffix.length ∧ d.suffix ≠ [])

/-- An aligned checked runtime body implements its actual source action under
every caller prefix, with exact whole-tape endpoints and positive progress. -/
theorem aligned_contract (B : BoxLemmas tm215) (rows : KHome.Rows tm215)
    (hb : KHome.Boundary tm215) (d : Descriptor) (hd : aligned d = true)
    (p : List Bool) {k : Nat}
    (hp : KHome.scanBound 0 (p.reverse.map Seg.bit) = some k)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    Reach1 tm215 (suffixPort d.state p d.suffix n vs)
      (dispatch p d.suffix d.result n vs) ∧
    ∀ r : RegisterPath.Registers,
      RegisterPath.execute d.action (p ++ d.suffix) r = some ⟨p ++ d.result, r⟩ := by
  obtain ⟨hs, hr, ha, hlen, _⟩ := of_decide_eq_true hd
  constructor
  · have ht := template_home B rows hb (runtime_mem d) p hp n hv
    rw [hs, suffixStart_conc] at ht
    have he : flat n vs (runtime d).right = flat n vs (outputRight d.suffix d.result) := by
      rw [← flatT_norm, hr, flatT_norm]
    rw [he, outputRight_flat p d.suffix d.result n vs hlen] at ht
    exact ht
  · exact KControlFrame.controlSuffix_frame ha p

-- BEGIN GENERATED DESCRIPTORS
def descriptors : List Descriptor := [
  ⟨⟨0, by decide⟩, 62, [true, false, true, true, true], [true, false], .cont 3⟩,
  ⟨⟨1, by decide⟩, 13, [true, true, true], [true], .cont 2⟩,
  ⟨⟨2, by decide⟩, 108, [true, false, false, true], [true, true], .brk 1⟩,
  ⟨⟨3, by decide⟩, 42, [true, true, true], [true], .cont 2⟩,
  ⟨⟨4, by decide⟩, 138, [true, true, true], [true], .cont 2⟩,
  ⟨⟨5, by decide⟩, 141, [true, true, true], [true], .cont 2⟩,
  ⟨⟨6, by decide⟩, 42, [true, false, false, false, false, false, true, true], [true, false, false, false, false, false], .cont 2⟩,
  ⟨⟨7, by decide⟩, 57, [true, false, true, true], [true, false], .cont 2⟩,
  ⟨⟨8, by decide⟩, 62, [true, false, false, true, true, true], [true, false, false], .cont 3⟩,
  ⟨⟨9, by decide⟩, 57, [true, true, true], [true], .cont 2⟩,
  ⟨⟨10, by decide⟩, 80, [true, false, true, true, true], [true, false], .cont 3⟩,
  ⟨⟨11, by decide⟩, 72, [true, true, true], [true], .cont 2⟩,
  ⟨⟨12, by decide⟩, 126, [true, true, true], [true], .cont 2⟩,
  ⟨⟨13, by decide⟩, 42, [true, false, false, true, true], [true, false, false], .cont 2⟩,
  ⟨⟨14, by decide⟩, 47, [true, true, true], [true], .cont 2⟩,
  ⟨⟨15, by decide⟩, 83, [true, false, false, false, true, true, true], [true, false, false, false], .cont 3⟩,
  ⟨⟨16, by decide⟩, 139, [true, true, true], [true], .cont 2⟩,
  ⟨⟨17, by decide⟩, 42, [true, false, false, false, false, true, true], [true, false, false, false, false], .cont 2⟩,
  ⟨⟨18, by decide⟩, 83, [true, false, false, false, false, false, true, true, true], [true, false, false, false, false, false], .cont 3⟩,
  ⟨⟨19, by decide⟩, 83, [true, false, false, false, false, true, true, true], [true, false, false, false, false], .cont 3⟩,
  ⟨⟨20, by decide⟩, 126, [true, false, true, true], [true, false], .cont 2⟩,
  ⟨⟨21, by decide⟩, 83, [true, false, false, true, true, true], [true, false, false], .cont 3⟩,
  ⟨⟨22, by decide⟩, 42, [true, false, false, false, true, true], [true, false, false, false], .cont 2⟩,
  ⟨⟨23, by decide⟩, 62, [true, true, true, true], [true], .cont 3⟩,
  ⟨⟨24, by decide⟩, 108, [true, false, false, false, true, false, true], [true, false, false, false], .cont 2⟩,
  ⟨⟨25, by decide⟩, 103, [false, false, true, true], [true], .brk 1⟩,
  ⟨⟨26, by decide⟩, 122, [true, false, true], [true, false], .cont 1⟩,
  ⟨⟨27, by decide⟩, 108, [true, true, false, true], [true], .cont 2⟩,
  ⟨⟨28, by decide⟩, 103, [false, true, true, false, true, true, true], [true, false, false], .brk 1⟩,
  ⟨⟨29, by decide⟩, 122, [true, true], [true], .cont 1⟩,
  ⟨⟨30, by decide⟩, 42, [true, false, true, true], [true, false], .cont 2⟩,
  ⟨⟨31, by decide⟩, 108, [true, false, false, false, false, true, false, true], [true, false, false, false, false], .cont 2⟩,
  ⟨⟨32, by decide⟩, 103, [false, false, true, true, true], [true], .brk 1⟩,
  ⟨⟨33, by decide⟩, 96, [false, false, true, true, true, true, true], [true], .brk 1⟩,
  ⟨⟨34, by decide⟩, 162, [false, false, true, true], [true], .brk 1⟩]

theorem descriptor_count : descriptors.length = 35 := by decide
theorem descriptor_indices : descriptors.map (fun d => d.index.val) = List.range 35 := by decide
theorem all_aligned : descriptors.all aligned = true := by decide

/-- All 35 literal templates implement the recorded source action for every prefix accepted by Home. -/
theorem control_contract (B : BoxLemmas tm215) (rows : KHome.Rows tm215)
    (hb : KHome.Boundary tm215) {d : Descriptor} (hd : d ∈ descriptors)
    (p : List Bool) {k : Nat}
    (hp : KHome.scanBound 0 (p.reverse.map Seg.bit) = some k)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    Reach1 tm215 (suffixPort d.state p d.suffix n vs)
      (dispatch p d.suffix d.result n vs) ∧
    ∀ r : RegisterPath.Registers,
      RegisterPath.execute d.action (p ++ d.suffix) r = some ⟨p ++ d.result, r⟩ :=
  aligned_contract B rows hb d (List.all_eq_true.mp all_aligned d hd) p hp n hv

#print axioms all_aligned
#print axioms control_contract
-- END GENERATED DESCRIPTORS

#print axioms aligned_contract

end SetTheory.BusyBeaver.ZFC.KFramedControl215
