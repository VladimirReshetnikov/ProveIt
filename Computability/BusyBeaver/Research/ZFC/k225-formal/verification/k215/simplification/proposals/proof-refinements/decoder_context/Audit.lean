import K215Context

open FramedWindow DecoderCertificate DecoderContext K215Decoder K215Context

example {bits : List Bool} {m : Nat}
    (hn : nodeFollow sourceNodes sourceRoot bits = some m)
    (a : Int) (t : Tape) (marker : t (a-1) = true) (ht : Reads t a bits) :
    ∃ (f : Role) (n : Nat), f.node = m ∧
      run (fullStep native) n ⟨84,a,t⟩ =
        some ⟨f.state,a+(bits.length : Int),t⟩ ∧
      MatchesAt (beforeCells f.suffix) (a+(bits.length : Int)) t ∧
      (bits ≠ [] → 0 < n) := every_internal_source_path hn a t marker ht

example {bits : List Bool} {f : Role} {n : Nat}
    (hf : follow roles blocks rootRole bits = some (f,n))
    (hne : bits ≠ []) : 0 < n := prefix_positive hf hne

#print axioms every_internal_source_path
#print axioms prefix_sound
#print axioms prefix_positive
#print axioms context_checked
#print axioms source_checked
#print axioms rejects_missing_predecessor
#print axioms rejects_wrong_predecessor
#print axioms rejects_wrong_next_suffix
#print axioms rejects_missing_target_role
#print axioms rejects_primitive_as_source_parent
