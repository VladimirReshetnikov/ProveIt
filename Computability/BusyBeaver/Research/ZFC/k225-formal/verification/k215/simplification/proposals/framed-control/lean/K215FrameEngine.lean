import FramedTemplates
import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KHomeReady

/-! Close both concrete engine premises using the same maintained table
agreement as KEndpoint215, and the existing certified Home boundary checker. -/
namespace SetTheory.BusyBeaver.ZFC.K215FrameEngine
open KZip KRuntimeCore KLeftFrame KTableCore KFramedTemplates

theorem boxLemmas215 : BoxLemmas tm215 :=
  KTape.boxLemmas (by decide) (.inr rfl)

theorem homeBoundary215 : KHome.Boundary tm215 :=
  (KHomeReady.ready_sound (M := tm215) (by decide)).2

/-- A concrete K215 macro certificate: no abstract engine or Home premise. -/
theorem template_sound215 {t : LocalTemplate} (ht : t ∈ templates)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) (P : List Bool)
    (hword : wordEnd tm215 t.returnState (P.reverse ++ [true]) = some 2) :
    Reach1 tm215
      (conc n vs (addLeft ((P.reverse.map Seg.bit) ++ [.bit true]) t.start))
      (zc 84 [true] (P ++ flat n vs t.right)) :=
  template_sound ht boxLemmas215 homeBoundary215 n hv P hword

#print axioms boxLemmas215
#print axioms homeBoundary215
#print axioms template_sound215

end SetTheory.BusyBeaver.ZFC.K215FrameEngine
