import DescentCore

/- An executable check of the generic kernel, not an elliptic-curve proof. -/
namespace MordellWeilIPRA

def naturalExample : DescentData Nat where
  add := Nat.add
  height := id
  cutoff := 1
  repCount := 2
  baseCount := 2
  rep := Fin.val
  base := Fin.val
  repIndex := fun n => ⟨n % 2, by omega⟩
  baseIndex := fun n => ⟨n % 2, by omega⟩
  child := fun n => n / 2
  baseComplete := by
    intro n hn
    change n % 2 = n
    change n ≤ 1 at hn
    omega
  decompose := by
    intro n _
    change n / 2 + n / 2 + n % 2 = n
    omega
  contract := by
    intro n _
    change 2 * (n / 2) ≤ n + 1
    omega

example : Word.eval Nat.add Fin.val Fin.val
    (naturalExample.coordinates 37) = 37 := by
  exact naturalExample.coordinates_correct 37

#eval naturalExample.coordinates 37
#eval Word.size (naturalExample.coordinates 37)
#eval Word.eval Nat.add Fin.val Fin.val (naturalExample.coordinates 37)

end MordellWeilIPRA
