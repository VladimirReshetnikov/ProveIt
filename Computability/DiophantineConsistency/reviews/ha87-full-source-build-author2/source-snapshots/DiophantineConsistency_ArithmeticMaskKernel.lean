import DiophantineConsistency.CurrentKernelData2011
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The exact coefficient mass of the fixed current kernel, as a pure ℕ fact.
The batch proofs use only Matrix-free table data and can be imported next to
Foundation, whose matrix type clashes with Mathlib's `Matrix`. -/

namespace DiophantineConsistency.ArithmeticMaskKernel

open WangTiles942 CurrentKernel2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/- The exact mass is proved on unsorted row families in16-entry kernel
   batches. No large floor-rank computation is evaluated for this bound. -/
private theorem sum_block (l : List ℕ) (k : ℕ) :
    (l.drop k).sum = ((l.drop k).take 16).sum + (l.drop (k + 16)).sum := by
  have h := congrArg List.sum (List.take_append_drop 16 (l.drop k))
  simpa only [List.sum_append, List.drop_drop, Nat.add_comm] using h.symm

private theorem sum_step (l : List ℕ) (k v w : ℕ)
    (h : ((l.drop k).take 16).sum = v) (ht : (l.drop (k + 16)).sum = w) :
    (l.drop k).sum = v + w :=
  (sum_block l k).trans (congrArg₂ (· + ·) h ht)

private theorem sum_finish (l : List ℕ) (v : ℕ) (h : (l.drop 0).sum = v) : l.sum = v := by
  simpa only [List.drop_zero] using h

private def transitionWeights : List ℕ := ((List.ofFn transitionRow).map (fun row => selectorWeight row.2))

private theorem transitionWeights_0 : ((transitionWeights.drop 0).take 16).sum = 315453641744 := by
  decide +kernel

private theorem transitionWeights_16 : ((transitionWeights.drop 16).take 16).sum = 210563192848 := by
  decide +kernel

private theorem transitionWeights_32 : ((transitionWeights.drop 32).take 16).sum = 282839278608 := by
  decide +kernel

private theorem transitionWeights_48 : ((transitionWeights.drop 48).take 16).sum = 250960346128 := by
  decide +kernel

private theorem transitionWeights_64 : ((transitionWeights.drop 64).take 16).sum = 307667354640 := by
  decide +kernel

private theorem transitionWeights_80 : ((transitionWeights.drop 80).take 16).sum = 200092520464 := by
  decide +kernel

private theorem transitionWeights_96 : ((transitionWeights.drop 96).take 16).sum = 378534092816 := by
  decide +kernel

private theorem transitionWeights_112 : ((transitionWeights.drop 112).take 16).sum = 316324896784 := by
  decide +kernel

private theorem transitionWeights_128 : ((transitionWeights.drop 128).take 16).sum = 276797749264 := by
  decide +kernel

private theorem transitionWeights_144 : ((transitionWeights.drop 144).take 16).sum = 364374589456 := by
  decide +kernel

private theorem transitionWeights_160 : ((transitionWeights.drop 160).take 16).sum = 405914983440 := by
  decide +kernel

private theorem transitionWeights_176 : ((transitionWeights.drop 176).take 16).sum = 299279195152 := by
  decide +kernel

private theorem transitionWeights_192 : ((transitionWeights.drop 192).take 16).sum = 493558448144 := by
  decide +kernel

private theorem transitionWeights_208 : ((transitionWeights.drop 208).take 16).sum = 303439466512 := by
  decide +kernel

private theorem transitionWeights_224 : ((transitionWeights.drop 224).take 16).sum = 396788148240 := by
  decide +kernel

private theorem transitionWeights_240 : ((transitionWeights.drop 240).take 16).sum = 523690328080 := by
  decide +kernel

private theorem transitionWeights_256 : ((transitionWeights.drop 256).take 16).sum = 495571714064 := by
  decide +kernel

private theorem transitionWeights_272 : ((transitionWeights.drop 272).take 16).sum = 511476753424 := by
  decide +kernel

private theorem transitionWeights_288 : ((transitionWeights.drop 288).take 16).sum = 463762865168 := by
  decide +kernel

private theorem transitionWeights_304 : ((transitionWeights.drop 304).take 16).sum = 315117126672 := by
  decide +kernel

private theorem transitionWeights_320 : ((transitionWeights.drop 320).take 16).sum = 507517323280 := by
  decide +kernel

private theorem transitionWeights_336 : ((transitionWeights.drop 336).take 16).sum = 571069186064 := by
  decide +kernel

private theorem transitionWeights_352 : ((transitionWeights.drop 352).take 16).sum = 599993359376 := by
  decide +kernel

private theorem transitionWeights_368 : ((transitionWeights.drop 368).take 16).sum = 560600700944 := by
  decide +kernel

private theorem transitionWeights_384 : ((transitionWeights.drop 384).take 16).sum = 652069584912 := by
  decide +kernel

private theorem transitionWeights_400 : ((transitionWeights.drop 400).take 16).sum = 622340613136 := by
  decide +kernel

private theorem transitionWeights_tail : (transitionWeights.drop 416).sum = 514001221646 := by
  decide +kernel

private theorem transitionWeights_sum : transitionWeights.sum = 11139798681006 :=
  sum_finish transitionWeights 11139798681006
    (sum_step transitionWeights 0 315453641744 10824345039262 transitionWeights_0
    (sum_step transitionWeights 16 210563192848 10613781846414 transitionWeights_16
    (sum_step transitionWeights 32 282839278608 10330942567806 transitionWeights_32
    (sum_step transitionWeights 48 250960346128 10079982221678 transitionWeights_48
    (sum_step transitionWeights 64 307667354640 9772314867038 transitionWeights_64
    (sum_step transitionWeights 80 200092520464 9572222346574 transitionWeights_80
    (sum_step transitionWeights 96 378534092816 9193688253758 transitionWeights_96
    (sum_step transitionWeights 112 316324896784 8877363356974 transitionWeights_112
    (sum_step transitionWeights 128 276797749264 8600565607710 transitionWeights_128
    (sum_step transitionWeights 144 364374589456 8236191018254 transitionWeights_144
    (sum_step transitionWeights 160 405914983440 7830276034814 transitionWeights_160
    (sum_step transitionWeights 176 299279195152 7530996839662 transitionWeights_176
    (sum_step transitionWeights 192 493558448144 7037438391518 transitionWeights_192
    (sum_step transitionWeights 208 303439466512 6733998925006 transitionWeights_208
    (sum_step transitionWeights 224 396788148240 6337210776766 transitionWeights_224
    (sum_step transitionWeights 240 523690328080 5813520448686 transitionWeights_240
    (sum_step transitionWeights 256 495571714064 5317948734622 transitionWeights_256
    (sum_step transitionWeights 272 511476753424 4806471981198 transitionWeights_272
    (sum_step transitionWeights 288 463762865168 4342709116030 transitionWeights_288
    (sum_step transitionWeights 304 315117126672 4027591989358 transitionWeights_304
    (sum_step transitionWeights 320 507517323280 3520074666078 transitionWeights_320
    (sum_step transitionWeights 336 571069186064 2949005480014 transitionWeights_336
    (sum_step transitionWeights 352 599993359376 2349012120638 transitionWeights_352
    (sum_step transitionWeights 368 560600700944 1788411419694 transitionWeights_368
    (sum_step transitionWeights 384 652069584912 1136341834782 transitionWeights_384
    (sum_step transitionWeights 400 622340613136 514001221646 transitionWeights_400
    transitionWeights_tail))))))))))))))))))))))))))

/-- The complete transition-family mass, available without another closed evaluation. -/
theorem transition_mass :
    ((List.ofFn transitionRow).map (fun row => selectorWeight row.2)).sum = 11139798681006 :=
  transitionWeights_sum

private def leftWeights : List ℕ := ((signalRows false).map (fun row => selectorWeight row.2))

private theorem leftWeights_0 : ((leftWeights.drop 0).take 16).sum = 10343357104144 := by
  decide +kernel

private theorem leftWeights_16 : ((leftWeights.drop 16).take 16).sum = 19981263716368 := by
  decide +kernel

private theorem leftWeights_32 : ((leftWeights.drop 32).take 16).sum = 39102458118160 := by
  decide +kernel

private theorem leftWeights_48 : ((leftWeights.drop 48).take 16).sum = 74441449029648 := by
  decide +kernel

private theorem leftWeights_64 : ((leftWeights.drop 64).take 16).sum = 109368123080720 := by
  decide +kernel

private theorem leftWeights_tail : (leftWeights.drop 80).sum = 126259960227850 := by
  decide +kernel

private theorem leftWeights_sum : leftWeights.sum = 379496611276890 :=
  sum_finish leftWeights 379496611276890
    (sum_step leftWeights 0 10343357104144 369153254172746 leftWeights_0
    (sum_step leftWeights 16 19981263716368 349171990456378 leftWeights_16
    (sum_step leftWeights 32 39102458118160 310069532338218 leftWeights_32
    (sum_step leftWeights 48 74441449029648 235628083308570 leftWeights_48
    (sum_step leftWeights 64 109368123080720 126259960227850 leftWeights_64
    leftWeights_tail)))))

private def rightWeights : List ℕ := ((signalRows true).map (fun row => selectorWeight row.2))

private theorem rightWeights_0 : ((rightWeights.drop 0).take 16).sum = 9758167965712 := by
  decide +kernel

private theorem rightWeights_16 : ((rightWeights.drop 16).take 16).sum = 30511450071056 := by
  decide +kernel

private theorem rightWeights_32 : ((rightWeights.drop 32).take 16).sum = 39307543224336 := by
  decide +kernel

private theorem rightWeights_48 : ((rightWeights.drop 48).take 16).sum = 48103636377616 := by
  decide +kernel

private theorem rightWeights_64 : ((rightWeights.drop 64).take 16).sum = 56899729530896 := by
  decide +kernel

private theorem rightWeights_80 : ((rightWeights.drop 80).take 16).sum = 65695822684176 := by
  decide +kernel

private theorem rightWeights_96 : ((rightWeights.drop 96).take 16).sum = 74491915837456 := by
  decide +kernel

private theorem rightWeights_112 : ((rightWeights.drop 112).take 16).sum = 83288008990736 := by
  decide +kernel

private theorem rightWeights_128 : ((rightWeights.drop 128).take 16).sum = 92084102144016 := by
  decide +kernel

private theorem rightWeights_144 : ((rightWeights.drop 144).take 16).sum = 100880195297296 := by
  decide +kernel

private theorem rightWeights_160 : ((rightWeights.drop 160).take 16).sum = 109676288450576 := by
  decide +kernel

private theorem rightWeights_176 : ((rightWeights.drop 176).take 16).sum = 118472381603856 := by
  decide +kernel

private theorem rightWeights_192 : ((rightWeights.drop 192).take 16).sum = 127268474757136 := by
  decide +kernel

private theorem rightWeights_208 : ((rightWeights.drop 208).take 16).sum = 136064567910416 := by
  decide +kernel

private theorem rightWeights_224 : ((rightWeights.drop 224).take 16).sum = 144860661063696 := by
  decide +kernel

private theorem rightWeights_240 : ((rightWeights.drop 240).take 16).sum = 154481387937808 := by
  decide +kernel

private theorem rightWeights_256 : ((rightWeights.drop 256).take 16).sum = 163552358998032 := by
  decide +kernel

private theorem rightWeights_272 : ((rightWeights.drop 272).take 16).sum = 172348452151312 := by
  decide +kernel

private theorem rightWeights_288 : ((rightWeights.drop 288).take 16).sum = 181144545304592 := by
  decide +kernel

private theorem rightWeights_304 : ((rightWeights.drop 304).take 16).sum = 189940638457872 := by
  decide +kernel

private theorem rightWeights_320 : ((rightWeights.drop 320).take 16).sum = 198736731611152 := by
  decide +kernel

private theorem rightWeights_336 : ((rightWeights.drop 336).take 16).sum = 207532824764432 := by
  decide +kernel

private theorem rightWeights_352 : ((rightWeights.drop 352).take 16).sum = 216328917917712 := by
  decide +kernel

private theorem rightWeights_368 : ((rightWeights.drop 368).take 16).sum = 225125011070992 := by
  decide +kernel

private theorem rightWeights_tail : (rightWeights.drop 384).sum = 205024563572750 := by
  decide +kernel

private theorem rightWeights_sum : rightWeights.sum = 3151578377695630 :=
  sum_finish rightWeights 3151578377695630
    (sum_step rightWeights 0 9758167965712 3141820209729918 rightWeights_0
    (sum_step rightWeights 16 30511450071056 3111308759658862 rightWeights_16
    (sum_step rightWeights 32 39307543224336 3072001216434526 rightWeights_32
    (sum_step rightWeights 48 48103636377616 3023897580056910 rightWeights_48
    (sum_step rightWeights 64 56899729530896 2966997850526014 rightWeights_64
    (sum_step rightWeights 80 65695822684176 2901302027841838 rightWeights_80
    (sum_step rightWeights 96 74491915837456 2826810112004382 rightWeights_96
    (sum_step rightWeights 112 83288008990736 2743522103013646 rightWeights_112
    (sum_step rightWeights 128 92084102144016 2651438000869630 rightWeights_128
    (sum_step rightWeights 144 100880195297296 2550557805572334 rightWeights_144
    (sum_step rightWeights 160 109676288450576 2440881517121758 rightWeights_160
    (sum_step rightWeights 176 118472381603856 2322409135517902 rightWeights_176
    (sum_step rightWeights 192 127268474757136 2195140660760766 rightWeights_192
    (sum_step rightWeights 208 136064567910416 2059076092850350 rightWeights_208
    (sum_step rightWeights 224 144860661063696 1914215431786654 rightWeights_224
    (sum_step rightWeights 240 154481387937808 1759734043848846 rightWeights_240
    (sum_step rightWeights 256 163552358998032 1596181684850814 rightWeights_256
    (sum_step rightWeights 272 172348452151312 1423833232699502 rightWeights_272
    (sum_step rightWeights 288 181144545304592 1242688687394910 rightWeights_288
    (sum_step rightWeights 304 189940638457872 1052748048937038 rightWeights_304
    (sum_step rightWeights 320 198736731611152 854011317325886 rightWeights_320
    (sum_step rightWeights 336 207532824764432 646478492561454 rightWeights_336
    (sum_step rightWeights 352 216328917917712 430149574643742 rightWeights_352
    (sum_step rightWeights 368 225125011070992 205024563572750 rightWeights_368
    rightWeights_tail))))))))))))))))))))))))

private theorem sum_indexed {α : Type*} (l : List α) (f : α → ℕ)
    (n : ℕ) (h : l.length = n) :
    (∑ i : Fin n, f (l[i.val]'(by omega))) = (l.map f).sum := by
  subst n
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]

private theorem sum_family_eq {α : Type*} (f : α → ℕ) (a : α)
    (l₁ l₂ l₃ l₄ l₅ : List α) (v₀ v₁ v₂ v₃ v₄ v₅ : ℕ)
    (h₀ : f a = v₀) (h₁ : (l₁.map f).sum = v₁)
    (h₂ : (l₂.map f).sum = v₂) (h₃ : (l₃.map f).sum = v₃)
    (h₄ : (l₄.map f).sum = v₄) (h₅ : (l₅.map f).sum = v₅) :
    (([a] ++ l₁ ++ l₂ ++ (l₃ ++ l₄) ++ l₅).map f).sum =
      v₀ + v₁ + v₂ + (v₃ + v₄) + v₅ := by
  simp only [List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil, add_zero]
  rw [h₀, h₁, h₂, h₃, h₄, h₅]

private theorem copy_mass :
    ((copyRows 1 ++ copyRows 0).map (fun row => selectorWeight row.2)).sum =
      29755760447492 := by decide +kernel

private theorem tail_mass : (tailRows.map (fun row => selectorWeight row.2)).sum =
      240316907829267 := by decide +kernel

private theorem ordered_mass :
    (orderedRows.map (fun row => selectorWeight row.2)).sum = 3812322332357550 :=
  (sum_family_eq (fun row : ℕ × Tile => selectorWeight row.2) (0, start)
    (List.ofFn transitionRow) (copyRows 1 ++ copyRows 0)
    (signalRows true) (signalRows false) tailRows
    34876427265 11139798681006 29755760447492 3151578377695630
    379496611276890 240316907829267
    (by decide) transitionWeights_sum copy_mass rightWeights_sum leftWeights_sum tail_mass).trans
    (by decide)

theorem selector_mass : (∑ i : Fin 942, selectorWeight (tile i)) = 3812322332357550 :=
  (sum_indexed orderedRows (fun row => selectorWeight row.2) 942 ordered_count).trans ordered_mass

private theorem sum_sum_mass {α β : Type*} [Fintype α] [Fintype β]
    (w : α ⊕ β → ℕ) (f : α → ℕ) (g : β → ℕ) (a b : ℕ)
    (hw : w = Sum.elim f g) (hf : (∑ i, f i) = a) (hg : (∑ j, g j) = b) :
    (∑ e, w e) = a + b := by
  rw [hw, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hf, hg]

private theorem sum_double_mass {α : Type*} [Fintype α] (f : α → ℕ) (a : ℕ)
    (h : (∑ i, f i) = a) : (∑ i, 2 * f i) = 2 * a := by
  rw [← Finset.mul_sum, h]

private theorem control_mass :
    (∑ e : Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9)), weight (.inr e)) =
      17592186043392 := by decide +kernel

theorem entry_mass : (∑ e : Entry, weight e) = 3829914518400942 :=
  sum_sum_mass weight (fun i => selectorWeight (tile i)) (fun e => weight (.inr e))
    3812322332357550 17592186043392
    (by funext e; cases e <;> rfl) selector_mass control_mass

theorem coefficient_mass : (∑ t : Term, coefficient t) = 7659829036801887 :=
  sum_sum_mass coefficient (fun _ : Fin 3 => 1) (fun e => 2 * weight e)
    3 (2 * 3829914518400942) (by funext t; cases t <;> rfl)
    (by decide) (sum_double_mass weight 3829914518400942 entry_mass)

end DiophantineConsistency.ArithmeticMaskKernel
