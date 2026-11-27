import GRHArticle.SingularModuli.QuarticAnalyticNumeric

/-!
# Kernel-checking the quartic coefficient enclosures

The root boxes are recorded on the existing rational grid. Checking their
endpoints once lets all five coefficient comparisons reuse the same boxes.
-/

namespace GRHArticle.SingularModuli

private def gridBox (rl ru il iu : ℤ) : RationalComplexBox :=
  let scale := RationalInterval.roundingScale
  ⟨⟨(rl : ℚ) / scale, (ru : ℚ) / scale⟩, ⟨(il : ℚ) / scale, (iu : ℚ) / scale⟩⟩

private theorem box_eq_of_endpoints {A B : RationalComplexBox}
    (hrl : A.re.lo = B.re.lo) (hru : A.re.hi = B.re.hi)
    (hil : A.im.lo = B.im.lo) (hiu : A.im.hi = B.im.hi) : A = B := by
  rcases A with ⟨⟨r₀, r₁⟩, ⟨i₀, i₁⟩⟩
  rcases B with ⟨⟨r₀', r₁'⟩, ⟨i₀', i₁'⟩⟩
  simp only at hrl hru hil hiu
  subst r₀' r₁' i₀' i₁'
  rfl

private def rootBoxes55 : Fin 4 → RationalComplexBox :=
  ![gridBox (-1313668622064863834122912324571545414790411209184327259214070602330)
      (-1313668622064863834122912324571545407989317133286915698915598584453)
      (-172572534357603748248) 172572534357603748248,
    gridBox 74399836383720517421825098767192443886473895265135034010157
      74399836383720517421825098767192443886473902888870817301008
      (-11461366934066361440784736844675183069235956128455972579780516) (-11461366934066361440784736844675183069235956116617634003058522),
    gridBox 74399836383720517421825098767192443886473895265135034010157
      74399836383720517421825098767192443886473902888870817301008
      11461366934066361440784736844675183069235956116617634003058522 11461366934066361440784736844675183069235956128455972579780516,
    gridBox 10765191066681877480921347877570017905873286389488496739930
      10765191066681877480921347877570017905873286599230060070386
      (-104870784407934) 104870773941293]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
private theorem rootBoxes55_eq (i : Fin 4) :
    modularInvariantBox (quartic55QBox i) = rootBoxes55 i := by
  fin_cases i <;> apply box_eq_of_endpoints <;> decide +kernel

theorem quartic55_analyticCoefficient_isolates (n : Fin 5) :
    (quartic55AnalyticCoefficientBox n).re.IsolatesInteger (quartic55PrintedCoefficient n) := by
  simp only [quartic55AnalyticCoefficientBox, rootBoxes55_eq]
  fin_cases n <;> decide +kernel

private def rootBoxes68 : Fin 4 → RationalComplexBox :=
  ![gridBox 17821146558257236317285989152242239035103208060414156709903706998797
      17821146558257236317285989152242256014731416757165863841572173164089
      (-31759326337667175866788) 31759326337667175866788,
    gridBox (-42140746393796828425027276471142244106649551241665443126940736)
      (-42140746393796828425027276471142244106649550956208770619350435)
      (-177888734256) 177888734256,
    gridBox (-208755421260228782062482887787339538066007242746070340221180)
      (-208755421260228782062482887787339538066007238238291313556750)
      (-484380600295345183312124664145987905360953676248056671420391) (-484380600295345183312124664145987905360953671740158616600696),
    gridBox (-208755421260228782062482887787339538066007242746070340221180)
      (-208755421260228782062482887787339538066007238238291313556750)
      484380600295345183312124664145987905360953671740158616600696 484380600295345183312124664145987905360953676248056671420391]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 0 in
private theorem rootBoxes68_eq (i : Fin 4) :
    modularInvariantBox (quartic68QBox i) = rootBoxes68 i := by
  fin_cases i <;> apply box_eq_of_endpoints <;> decide +kernel

theorem quartic68_analyticCoefficient_isolates (n : Fin 5) :
    (quartic68AnalyticCoefficientBox n).re.IsolatesInteger (quartic68PrintedCoefficient n) := by
  simp only [quartic68AnalyticCoefficientBox, rootBoxes68_eq]
  fin_cases n <;> decide +kernel

end GRHArticle.SingularModuli
