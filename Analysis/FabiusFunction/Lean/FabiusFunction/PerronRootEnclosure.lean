import FabiusFunction.CollatzWielandt
import FabiusFunction.BernsteinPositivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FunProp

/-!
# A kernel-checked enclosure for the Perron root `ρ₁`

The comparative audit's feasibility list left one half of its item 4
open: the Collatz–Wielandt *reduction* is formal
(`perron_root_mem_of_two_sided`), but "what is left is exhibiting the
explicit `h` and discharging the two rational positivity checks; no
Sturm module exists yet."  This module discharges that half:

`0.66126798 ≤ ρ₁ ≤ 0.66134921`,

where `ρ₁` is the Perron growth root of the arithmetic-mean transfer
operator `(𝓛₁f)(x) = (sin(πx/2)·f(x/2) + cos(πx/2)·f((x+1)/2))/2` —
the root whose existence is `exists_perron_root` and whose numerical
value is `0.661322602060565…`.

The test function is Document 4's optimized cubic
`h(x) = F(sin πx)`, `F(u) = 1 + 0.376189u - 0.069093u² + 0.015483u³`.
Under `t = tan (πx/4)` the two inequalities `m·h ≤ 𝓛₁h ≤ M·h` become
integer-polynomial inequalities of degree 12 on `t ∈ [0,1]`, and these
are certified **without Sturm sequences**: each is a 32-piece
subdivided Bernstein certificate (`BernsteinPositivity`), machine
generated, with exact integer coefficients — checking it needs only
`ring`-normalization and coefficient-sign evaluation.  The audit's
SymPy enclosure `0.66126807 < ρ₁ < 0.66134891` is `≈ 10⁻⁷` sharper;
its endpoints sit within `10⁻⁸` of the true range of `𝓛₁h/h`, and
certifying them by subdivision would need about two thousand pieces
(quadratic convergence), against thirty-two here.

* `perronTest` — the optimized test function, continuity, positivity.
* `perronNumerA`, `perronNumerB` — the degree-12 integer numerators.
* `perronCert_low`, `perronCert_high` — the Bernstein certificates.
* `tan_quarter_package` — the Weierstrass `t = tan (πx/4)` dictionary.
* `perron_bracket_pointwise` — `m·h ≤ 𝓛₁h ≤ M·h` on `[0,1]`.
* `perron_root_enclosure`, `exists_perron_root_enclosure` — the final
  enclosure.
-/

set_option autoImplicit false

open Real

namespace Fabius

/-- The optimized cubic profile of the audits' Collatz–Wielandt test
function (Document 4, Appendix A). -/
noncomputable def perronTestCubic (u : ℝ) : ℝ :=
  1 + 376189 / 1000000 * u - 69093 / 1000000 * u ^ 2 +
    15483 / 1000000 * u ^ 3

/-- The audits' optimized test function `h(x) = F(sin πx)`. -/
noncomputable def perronTest (x : ℝ) : ℝ :=
  perronTestCubic (Real.sin (π * x))

/-- The test function is continuous. -/
theorem perronTest_continuous : Continuous perronTest := by
  unfold perronTest perronTestCubic
  fun_prop

/-- The test function is strictly positive on `[0,1]`. -/
theorem perronTest_pos {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    0 < perronTest x := by
  obtain ⟨h0, h1⟩ := hx
  have hs0 : 0 ≤ Real.sin (π * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos])
  have hs1 : Real.sin (π * x) ≤ 1 := Real.sin_le_one _
  have hu2 : Real.sin (π * x) ^ 2 ≤ 1 := by nlinarith
  have hu3 : 0 ≤ Real.sin (π * x) ^ 3 := pow_nonneg hs0 3
  unfold perronTest perronTestCubic
  nlinarith
/-- `10^6` times the `t = tan (πx/4)` numerator of `2(1+t²)^6 · (𝓛h)(x)`
for the optimized cubic test function: an integer polynomial of degree 12. -/
noncomputable def perronNumerA (t : ℝ) : ℝ :=
  1322579 + 2000000 * t
      + 6226168 * t ^ 2 + 9447256 * t ^ 3
      + 11082359 * t ^ 4 + 18341768 * t ^ 5
      + 8081168 * t ^ 6 + 18341768 * t ^ 7
      + 667801 * t ^ 8 + 9447256 * t ^ 9
      - 1773832 * t ^ 10 + 2000000 * t ^ 11
      - 539235 * t ^ 12

/-- `10^6` times the `t = tan (πx/4)` numerator of `(1+t²)^6 · h(x)`:
an integer polynomial of degree 12. -/
noncomputable def perronNumerB (t : ℝ) : ℝ :=
  1000000 + 1504756 * t
      + 4894512 * t ^ 2 + 5505180 * t ^ 3
      + 15000000 * t ^ 4 + 36776 * t ^ 5
      + 22210976 * t ^ 6 - 36776 * t ^ 7
      + 15000000 * t ^ 8 - 5505180 * t ^ 9
      + 4894512 * t ^ 10 - 1504756 * t ^ 11
      + 1000000 * t ^ 12

/-- The lower certificate: `10^8·A - 2·66126798·B ≥ 0` on `[0,1]`, by a 32-piece Bernstein certificate with exact integer coefficients. -/
theorem perronCert_low :
    ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ 10 ^ 8 * perronNumerA t - 132253596 * perronNumerB t := by
  intro t ht
  refine nonneg_on_Icc_of_pieces
    (fun u : ℝ => 10 ^ 8 * perronNumerA u - 132253596 * perronNumerB u)
    32 (by norm_num) ?_ (t := t) ht
  intro i hi s hs
  obtain ⟨hs0, hs1⟩ := hs
  have h1s : (0:ℝ) ≤ 1 - s := by linarith
  have hB : ∀ (c : ℝ), 0 ≤ c → ∀ k j : ℕ, 0 ≤ c * s ^ k * (1 - s) ^ j :=
    fun c hc k j => mul_nonneg (mul_nonneg hc (pow_nonneg hs0 k)) (pow_nonneg h1s j)
  simp only [perronNumerA, perronNumerB]
  interval_cases i
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (4962174155827869384704000000 : ℝ) (by norm_num) 0 12)
      (hB (95236500731606408011744018432 : ℝ) (by norm_num) 1 11))
      (hB (692288271804324838991047163904 : ℝ) (by norm_num) 2 10))
      (hB (2784176036709236464150716088320 : ℝ) (by norm_num) 3 9))
      (hB (7161395815527883357389565460480 : ℝ) (by norm_num) 4 8))
      (hB (12637481363912600558083833331712 : ℝ) (by norm_num) 5 7))
      (hB (15847748848904446213943579377664 : ℝ) (by norm_num) 6 6))
      (hB (14318792645271071928654221017088 : ℝ) (by norm_num) 7 5))
      (hB (9289283721518603353047527587840 : ℝ) (by norm_num) 8 4))
      (hB (4231964570638073007402534830080 : ℝ) (by norm_num) 9 3))
      (hB (1287780045621266217434770243584 : ℝ) (by norm_num) 10 2))
      (hB (235371078791304343113945814528 : ℝ) (by norm_num) 11 1))
      (hB (19563318521540673048705266688 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (19563318521540673048705266688 : ℝ) (by norm_num) 0 12)
      (hB (234148565725671810054980585984 : ℝ) (by norm_num) 1 11))
      (hB (1274332401899308353786152729600 : ℝ) (by norm_num) 2 10))
      (hB (4173439605611880421946060216320 : ℝ) (by norm_num) 3 9))
      (hB (9165988347941605993397781483520 : ℝ) (by norm_num) 4 8))
      (hB (14229141115399523496273016930304 : ℝ) (by norm_num) 5 7))
      (hB (16015565683048277172091916484608 : ℝ) (by norm_num) 6 6))
      (hB (13172664082461062430449211736064 : ℝ) (by norm_num) 7 5))
      (hB (7859359777650498078366836326400 : ℝ) (by norm_num) 8 4))
      (hB (3317898479272701992524571607040 : ℝ) (by norm_num) 9 3))
      (hB (940841840874977909376935526400 : ℝ) (by norm_num) 10 2))
      (hB (160913184016644948726132506624 : ℝ) (by norm_num) 11 1))
      (hB (12553662551276733728549765120 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (12553662551276733728549765120 : ℝ) (by norm_num) 0 12)
      (hB (140374717213996660759061856256 : ℝ) (by norm_num) 1 11))
      (hB (714918706045846741739158372352 : ℝ) (by norm_num) 2 10))
      (hB (2192483944812018837512574074880 : ℝ) (by norm_num) 3 9))
      (hB (4508323012378284712392173158400 : ℝ) (by norm_num) 4 8))
      (hB (6546290676328823244125575643136 : ℝ) (by norm_num) 5 7))
      (hB (6880247024341228257255801716736 : ℝ) (by norm_num) 6 6))
      (hB (5271384938000656336685627326464 : ℝ) (by norm_num) 7 5))
      (hB (2920424623177100658189912166400 : ℝ) (by norm_num) 8 4))
      (hB (1140275403505399800475466065920 : ℝ) (by norm_num) 9 3))
      (hB (297630302209565086862797417472 : ℝ) (by norm_num) 10 2))
      (hB (46593325791599971645451830784 : ℝ) (by norm_num) 11 1))
      (hB (3305674949192474858268200960 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (3305674949192474858268200960 : ℝ) (by norm_num) 0 12)
      (hB (32742872989019424952984992256 : ℝ) (by norm_num) 1 11))
      (hB (145275321381179073245662193664 : ℝ) (by norm_num) 2 10))
      (hB (379786877112663925333113200640 : ℝ) (by norm_num) 3 9))
      (hB (646677310494058190422793093120 : ℝ) (by norm_num) 4 8))
      (hB (747106781924098834134993207296 : ℝ) (by norm_num) 5 7))
      (hB (589825249109551612601773850624 : ℝ) (by norm_num) 6 6))
      (hB (310760201407110752568193581056 : ℝ) (by norm_num) 7 5))
      (hB (101915915003094261989701058560 : ℝ) (by norm_num) 8 4))
      (hB (17373982402653777808945315840 : ℝ) (by norm_num) 9 3))
      (hB (749042841349602756425416704 : ℝ) (by norm_num) 10 2))
      (hB (29112901562011451964522496 : ℝ) (by norm_num) 11 1))
      (hB (51314958683324198475005952 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (51314958683324198475005952 : ℝ) (by norm_num) 0 12)
      (hB (1202446106837769311435620352 : ℝ) (by norm_num) 1 11))
      (hB (13655708099382939210607493120 : ℝ) (by norm_num) 2 10))
      (hB (81516363363346347203378544640 : ℝ) (by norm_num) 3 9))
      (hB (291997385908327292914137825280 : ℝ) (by norm_num) 4 8))
      (hB (683932292978620100725169979392 : ℝ) (by norm_num) 5 7))
      (hB (1099388942112167488646181552128 : ℝ) (by norm_num) 6 6))
      (hB (1240897137567746570640112222208 : ℝ) (by norm_num) 7 5))
      (hB (986234189910836935011685990400 : ℝ) (by norm_num) 8 4))
      (hB (542163715540465119336833720320 : ℝ) (by norm_num) 9 3))
      (hB (196704563479919897553129072640 : ℝ) (by norm_num) 10 2))
      (hB (42454424285042421087457453568 : ℝ) (by norm_num) 11 1))
      (hB (4134275372740264593074600960 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (4134275372740264593074600960 : ℝ) (by norm_num) 0 12)
      (hB (56768184660723929146332969472 : ℝ) (by norm_num) 1 11))
      (hB (354155927612416486200759747584 : ℝ) (by norm_num) 2 10))
      (hB (1328278867371465876296405637120 : ℝ) (by norm_num) 3 9))
      (hB (3337729632414946088218912993280 : ℝ) (by norm_num) 4 8))
      (hB (5923370625607051361154049523712 : ℝ) (by norm_num) 5 7))
      (hB (7616674547816881424243474202624 : ℝ) (by norm_num) 6 6))
      (hB (7153724836010754673459727106048 : ℝ) (by norm_num) 7 5))
      (hB (4872830708443027486441989079040 : ℝ) (by norm_num) 8 4))
      (hB (2348529516287656023935112314880 : ℝ) (by norm_num) 9 3))
      (hB (760498335741255517254572048384 : ℝ) (by norm_num) 10 2))
      (hB (148607486295270791828897005568 : ℝ) (by norm_num) 11 1))
      (hB (13256088831655202690645884928 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (13256088831655202690645884928 : ℝ) (by norm_num) 0 12)
      (hB (169538645664454072746604232704 : ℝ) (by norm_num) 1 11))
      (hB (990741088802271607349351546880 : ℝ) (by norm_num) 2 10))
      (hB (3498506557291036854335744901120 : ℝ) (by norm_num) 3 9))
      (hB (8315341485642972257204297400320 : ℝ) (by norm_num) 4 8))
      (hB (14016506175700190362498209480704 : ℝ) (by norm_num) 5 7))
      (hB (17183131094077764283898399326208 : ℝ) (by norm_num) 6 6))
      (hB (15438176306649449142934812606464 : ℝ) (by norm_num) 7 5))
      (hB (10089913944290895678703548313600 : ℝ) (by norm_num) 8 4))
      (hB (4678764490899459405651861514240 : ℝ) (by norm_num) 9 3))
      (hB (1461285269012196633438159467520 : ℝ) (by norm_num) 10 2))
      (hB (276026365025634653694724109824 : ℝ) (by norm_num) 11 1))
      (hB (23849570572468642400458905600 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (23849570572468642400458905600 : ℝ) (by norm_num) 0 12)
      (hB (296363328713612763916289624576 : ℝ) (by norm_num) 1 11))
      (hB (1684991869579955845875380129792 : ℝ) (by norm_num) 2 10))
      (hB (5796384791249660075079697530880 : ℝ) (by norm_num) 3 9))
      (hB (13437298630409925330437452595200 : ℝ) (by norm_num) 4 8))
      (hB (22116527617485796892174194835456 : ℝ) (by norm_num) 5 7))
      (hB (26502215392632676822509909180416 : ℝ) (by norm_num) 6 6))
      (hB (23297405174659658891432636186624 : ℝ) (by norm_num) 7 5))
      (hB (14911909594985348533916480307200 : ℝ) (by norm_num) 8 4))
      (hB (6777809349787581068644313989120 : ℝ) (by norm_num) 9 3))
      (hB (2076639427635971887564557647872 : ℝ) (by norm_num) 10 2))
      (hB (385105194799683799225953419264 : ℝ) (by norm_num) 11 1))
      (hB (32690970879646241591750819840 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (32690970879646241591750819840 : ℝ) (by norm_num) 0 12)
      (hB (399478106311825998976066256896 : ℝ) (by norm_num) 1 11))
      (hB (2234741454269536084815798861824 : ℝ) (by norm_num) 2 10))
      (hB (7567945095178806054418529648640 : ℝ) (by norm_num) 3 9))
      (hB (17280070504499447488347184824320 : ℝ) (by norm_num) 4 8))
      (hB (28026989937651142816723900563456 : ℝ) (by norm_num) 5 7))
      (hB (33111065405602407242314624794624 : ℝ) (by norm_num) 6 6))
      (hB (28709680318811800318182734954496 : ℝ) (by norm_num) 7 5))
      (hB (18133254106461789440782110556160 : ℝ) (by norm_num) 8 4))
      (hB (8136534353363093609407427543040 : ℝ) (by norm_num) 9 3))
      (hB (2462064843491073054684229996544 : ℝ) (by norm_num) 10 2))
      (hB (451109531944815261013702309376 : ℝ) (by norm_num) 11 1))
      (hB (37850058057584320009565422592 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (37850058057584320009565422592 : ℝ) (by norm_num) 0 12)
      (hB (457291861437208419215867832832 : ℝ) (by norm_num) 1 11))
      (hB (2530070467907397794908050754560 : ℝ) (by norm_num) 2 10))
      (hB (8476767669947413278097808087040 : ℝ) (by norm_num) 3 9))
      (hB (19155185223230924252280912711680 : ℝ) (by norm_num) 4 8))
      (hB (30757230994513911646600141094912 : ℝ) (by norm_num) 5 7))
      (hB (35984502557121707631660085772288 : ℝ) (by norm_num) 6 6))
      (hB (30908974477654970878898552373248 : ℝ) (by norm_num) 7 5))
      (hB (19345916902149366663431805337600 : ℝ) (by norm_num) 8 4))
      (hB (8605089176266776087059363921920 : ℝ) (by norm_num) 9 3))
      (hB (2582050779473787552495119892480 : ℝ) (by norm_num) 10 2))
      (hB (469295287879087721168089120768 : ℝ) (by norm_num) 11 1))
      (hB (39073479758599630077186539520 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (39073479758599630077186539520 : ℝ) (by norm_num) 0 12)
      (hB (468468226327303400684387827712 : ℝ) (by norm_num) 1 11))
      (hB (2572953102404160027174405668864 : ℝ) (by norm_num) 2 10))
      (hB (8560287454945025241711736913920 : ℝ) (by norm_num) 3 9))
      (hB (19215631722342434814924588974080 : ℝ) (by norm_num) 4 8))
      (hB (30660753869521046503482124992512 : ℝ) (by norm_num) 5 7))
      (hB (35660008491448682006626473181184 : ℝ) (by norm_num) 6 6))
      (hB (30461434052577882339063933943808 : ℝ) (by norm_num) 7 5))
      (hB (18968417786436386389961810186240 : ℝ) (by norm_num) 8 4))
      (hB (8397625742883656676471863879680 : ℝ) (by norm_num) 9 3))
      (hB (2509088252202196918858030480384 : ℝ) (by norm_num) 10 2))
      (hB (454302996433024384394140395008 : ℝ) (by norm_num) 11 1))
      (hB (37699508095478572008596922368 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (37699508095478572008596922368 : ℝ) (by norm_num) 0 12)
      (hB (450485197858461343812185741824 : ℝ) (by norm_num) 1 11))
      (hB (2467092467882003472456529295360 : ℝ) (by norm_num) 2 10))
      (hB (8188614333937203869108442193920 : ℝ) (by norm_num) 3 9))
      (hB (18347188635524114515736050565120 : ℝ) (by norm_num) 4 8))
      (hB (29236377674706959976905006383104 : ℝ) (by norm_num) 5 7))
      (hB (33977363486186301126760027127808 : ℝ) (by norm_num) 6 6))
      (hB (29018558195456935879014680100864 : ℝ) (by norm_num) 7 5))
      (hB (18077199419716110035303845068800 : ℝ) (by norm_num) 8 4))
      (hB (8011156652094750320871541309440 : ℝ) (by norm_num) 9 3))
      (hB (2397525788895570559661181501440 : ℝ) (by norm_num) 10 2))
      (hB (435087195536510128645549850624 : ℝ) (by norm_num) 11 1))
      (hB (36209943291243050254079098880 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (36209943291243050254079098880 : ℝ) (by norm_num) 0 12)
      (hB (433951443453323077452348522496 : ℝ) (by norm_num) 1 11))
      (hB (2385032515980512996535966892032 : ℝ) (by norm_num) 2 10))
      (hB (7949676300372201017510335610880 : ℝ) (by norm_num) 3 9))
      (hB (17898674441664893198809432064000 : ℝ) (by norm_num) 4 8))
      (hB (28679242298594902145956604542976 : ℝ) (by norm_num) 5 7))
      (hB (33535371898621665539891838058496 : ℝ) (by norm_num) 6 6))
      (hB (28835600274351660519749874089984 : ℝ) (by norm_num) 7 5))
      (hB (18096132328300298069586202624000 : ℝ) (by norm_num) 8 4))
      (hB (8083544865186002500239344312320 : ℝ) (by norm_num) 9 3))
      (hB (2439825520809727905848993052672 : ℝ) (by norm_num) 10 2))
      (hB (446767120352831316344133420544 : ℝ) (by norm_num) 11 1))
      (hB (37535653642579630149032709120 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (37535653642579630149032709120 : ℝ) (by norm_num) 0 12)
      (hB (454088567069079807232651598336 : ℝ) (by norm_num) 1 11))
      (hB (2520361434688461305622693008384 : ℝ) (by norm_num) 2 10))
      (hB (8486949484325815083328732272640 : ℝ) (by norm_num) 3 9))
      (hB (19310696484196609324179695595520 : ℝ) (by norm_num) 4 8))
      (hB (31277766823596334374257636950016 : ℝ) (by norm_num) 5 7))
      (hB (36978695854354713210355370983424 : ℝ) (by norm_num) 6 6))
      (hB (32152841190160152457139588366336 : ℝ) (by norm_num) 7 5))
      (hB (20405665387761600293995440373760 : ℝ) (by norm_num) 8 4))
      (hB (9218176739867524920607577866240 : ℝ) (by norm_num) 9 3))
      (hB (2813548640468383005903673360384 : ℝ) (by norm_num) 10 2))
      (hB (520924490009982089205900640256 : ℝ) (by norm_num) 11 1))
      (hB (44243839916541775389085663232 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (44243839916541775389085663232 : ℝ) (by norm_num) 0 12)
      (hB (540927667987020520132155277312 : ℝ) (by norm_num) 1 11))
      (hB (3033583598215805746092474368000 : ℝ) (by norm_num) 2 10))
      (hB (10318566520417600256958515773440 : ℝ) (by norm_num) 3 9))
      (hB (23708124680289596115489851310080 : ℝ) (by norm_num) 4 8))
      (hB (38761620914878873800654339244032 : ℝ) (by norm_num) 5 7))
      (hB (46238162401241187514875335835648 : ℝ) (by norm_num) 6 6))
      (hB (40546141100703277326461744037888 : ℝ) (by norm_num) 7 5))
      (hB (25938529509403148182042268364800 : ℝ) (by norm_num) 8 4))
      (hB (11805228765421278301772645099520 : ℝ) (by norm_num) 9 3))
      (hB (3628093512723000481068579537920 : ℝ) (by norm_num) 10 2))
      (hB (675997738431061783331868743168 : ℝ) (by norm_num) 11 1))
      (hB (57745166049831988176577095680 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (57745166049831988176577095680 : ℝ) (by norm_num) 0 12)
      (hB (709886246764905932905981553152 : ℝ) (by norm_num) 1 11))
      (hB (4000867104395286126383820447744 : ℝ) (by norm_num) 2 10))
      (hB (13668631281909438177363510558720 : ℝ) (by norm_num) 3 9))
      (hB (31525944407628017702902830202880 : ℝ) (by norm_num) 4 8))
      (hB (51712590494099172311692960858112 : ℝ) (by norm_num) 5 7))
      (hB (61855538988777546964070347833344 : ℝ) (by norm_num) 6 6))
      (hB (54359414700662113305356945850368 : ℝ) (by norm_num) 7 5))
      (hB (34832601265772588091636648509440 : ℝ) (by norm_num) 8 4))
      (hB (15870988027461117577158700564480 : ℝ) (by norm_num) 9 3))
      (hB (4880644688935186973334473539584 : ℝ) (by norm_num) 10 2))
      (hB (909495375213939800891717582848 : ℝ) (by norm_num) 11 1))
      (hB (77664504552229072688023339008 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (77664504552229072688023339008 : ℝ) (by norm_num) 0 12)
      (hB (954452734039557943620842553344 : ℝ) (by norm_num) 1 11))
      (hB (5375175636016986543354848215040 : ℝ) (by norm_num) 2 10))
      (hB (18342451216099033624273978654720 : ℝ) (by norm_num) 3 9))
      (hB (42239841551059845415062911057920 : ℝ) (by norm_num) 4 8))
      (hB (69152453217169328948065813397504 : ℝ) (by norm_num) 5 7))
      (hB (82525789352127471601357483409408 : ℝ) (by norm_num) 6 6))
      (hB (72332876954470496132389104779264 : ℝ) (by norm_num) 7 5))
      (hB (46211940660533801434906099712000 : ℝ) (by norm_num) 8 4))
      (hB (20986708453019107967518342512640 : ℝ) (by norm_num) 9 3))
      (hB (6430748020055280088768996188160 : ℝ) (by norm_num) 10 2))
      (hB (1193733947364402974657136449024 : ℝ) (by norm_num) 11 1))
      (hB (101516797816313248209760424960 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (101516797816313248209760424960 : ℝ) (by norm_num) 0 12)
      (hB (1242669200227114982377113750016 : ℝ) (by norm_num) 1 11))
      (hB (6969035801545112173688746499072 : ℝ) (by norm_num) 2 10))
      (hB (23676347684629156232469910394880 : ℝ) (by norm_num) 3 9))
      (hB (54270060300329273271877701324800 : ℝ) (by norm_num) 4 8))
      (hB (88416737404982921160191268765696 : ℝ) (by norm_num) 5 7))
      (hB (104982810756393499350181436030976 : ℝ) (by norm_num) 6 6))
      (hB (91534102947143367152140928876544 : ℝ) (by norm_num) 7 5))
      (hB (58162252633887773686485322956800 : ℝ) (by norm_num) 8 4))
      (hB (26266131994616724147768889835520 : ℝ) (by norm_num) 9 3))
      (hB (8002148335208622583804005711872 : ℝ) (by norm_num) 10 2))
      (hB (1476650817602250469509443354624 : ℝ) (by norm_num) 11 1))
      (hB (124815424020939644033486028800 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (124815424020939644033486028800 : ℝ) (by norm_num) 0 12)
      (hB (1518919358900300987294221336576 : ℝ) (by norm_num) 1 11))
      (hB (8467102289487178279436563513344 : ℝ) (by norm_num) 2 10))
      (hB (28588801113914397735169097072640 : ℝ) (by norm_num) 3 9))
      (hB (65117656079210165104110454046720 : ℝ) (by norm_num) 4 8))
      (hB (105407123217342274379558587006976 : ℝ) (by norm_num) 5 7))
      (hB (124334597880966114723949069697024 : ℝ) (by norm_num) 6 6))
      (hB (107680648751870946784451320856576 : ℝ) (by norm_num) 7 5))
      (hB (67954875711941371311088022671360 : ℝ) (by norm_num) 8 4))
      (hB (30475081012768461223664245565440 : ℝ) (by norm_num) 9 3))
      (hB (9218709245305577951468138548224 : ℝ) (by norm_num) 10 2))
      (hB (1688892948788752673763938715136 : ℝ) (by norm_num) 11 1))
      (hB (141709772653786583638580047872 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (141709772653786583638580047872 : ℝ) (by norm_num) 0 12)
      (hB (1712141594902125333561982433792 : ℝ) (by norm_num) 1 11))
      (hB (9474444352552677209246619453440 : ℝ) (by norm_num) 2 10))
      (hB (31751855030481896781532892323840 : ℝ) (by norm_num) 3 9))
      (hB (71773788653949313598551416340480 : ℝ) (by norm_num) 4 8))
      (hB (115284280826840469657295004106752 : ℝ) (by norm_num) 5 7))
      (hB (134915979499946302339061365342208 : ℝ) (by norm_num) 6 6))
      (hB (115909110314218338605854651056128 : ℝ) (by norm_num) 7 5))
      (hB (72551290889680026327320625152000 : ℝ) (by norm_num) 8 4))
      (hB (32266272667899131316728359813120 : ℝ) (by norm_num) 9 3))
      (hB (9678026318617345774003903528960 : ℝ) (by norm_num) 10 2))
      (hB (1757775043666476812620443680768 : ℝ) (by norm_num) 11 1))
      (hB (146195990608986489593727549440 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (146195990608986489593727549440 : ℝ) (by norm_num) 0 12)
      (hB (1750928730949198937629017505792 : ℝ) (by norm_num) 1 11))
      (hB (9602716878727289149098215604224 : ℝ) (by norm_num) 2 10))
      (hB (31888687569639107071812588011520 : ℝ) (by norm_num) 3 9))
      (hB (71412308202041506870249316679680 : ℝ) (by norm_num) 4 8))
      (hB (113612501050995137693627304640512 : ℝ) (by norm_num) 5 7))
      (hB (131666067558949917162697317679104 : ℝ) (by norm_num) 6 6))
      (hB (111991313046682070694840732745728 : ℝ) (by norm_num) 7 5))
      (hB (69385069589434564122411822448640 : ℝ) (by norm_num) 8 4))
      (hB (30536368524198511963078352609280 : ℝ) (by norm_num) 9 3))
      (hB (9061335318585525452120659625984 : ℝ) (by norm_num) 10 2))
      (hB (1627758309356557604909103769088 : ℝ) (by norm_num) 11 1))
      (hB (133863693472794533548943694848 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (133863693472794533548943694848 : ℝ) (by norm_num) 0 12)
      (hB (1584970333990511200265544907264 : ℝ) (by norm_num) 1 11))
      (hB (8590667589559015001041512145920 : ℝ) (by norm_num) 2 10))
      (hB (28183610301187703045472913643520 : ℝ) (by norm_num) 3 9))
      (hB (62330277453132597396337296158720 : ℝ) (by norm_num) 4 8))
      (hB (97892212713670170960659993083904 : ℝ) (by norm_num) 5 7))
      (hB (111947032787867494055958779691008 : ℝ) (by norm_num) 6 6))
      (hB (93918352534595156172991542001664 : ℝ) (by norm_num) 7 5))
      (hB (57366680197409083573000762163200 : ℝ) (by norm_num) 8 4))
      (hB (24878696500707163084418887843840 : ℝ) (by norm_num) 9 3))
      (hB (7271034057838999286790185287680 : ℝ) (by norm_num) 10 2))
      (hB (1285737919470309181697725825024 : ℝ) (by norm_num) 11 1))
      (hB (104024524341029612652032163840 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (104024524341029612652032163840 : ℝ) (by norm_num) 0 12)
      (hB (1210850664714401521951046107136 : ℝ) (by norm_num) 1 11))
      (hB (6447274255524015029576708390912 : ℝ) (by norm_num) 2 10))
      (hB (20762805212816920945461744762880 : ℝ) (by norm_num) 3 9))
      (hB (45036452675846432038790781337600 : ℝ) (by norm_num) 4 8))
      (hB (69310260143380035846389483503616 : ℝ) (by norm_num) 5 7))
      (hB (77593535259252910267087933177856 : ℝ) (by norm_num) 6 6))
      (hB (63661169960181678145528997986304 : ℝ) (by norm_num) 7 5))
      (hB (37984681574291942907197441945600 : ℝ) (by norm_num) 8 4))
      (hB (16072285172691630068601814558720 : ℝ) (by norm_num) 9 3))
      (hB (4577038988235921072338246505472 : ℝ) (by norm_num) 10 2))
      (hB (787543533406763842664755541504 : ℝ) (by norm_num) 11 1))
      (hB (61907409699179256777602938880 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (61907409699179256777602938880 : ℝ) (by norm_num) 0 12)
      (hB (698234299373538319997714991616 : ℝ) (by norm_num) 1 11))
      (hB (3594637413870440323000800456704 : ℝ) (by norm_num) 2 10))
      (hB (11165958313094237920498068848640 : ℝ) (by norm_num) 3 9))
      (hB (23299787068879836054387112017920 : ℝ) (by norm_num) 4 8))
      (hB (34393634095664902437345045774336 : ℝ) (by norm_num) 5 7))
      (hB (36809838646394297636465802215424 : ℝ) (by norm_num) 6 6))
      (hB (28765094476128689767829225865216 : ℝ) (by norm_num) 7 5))
      (hB (16280032729744345235274554408960 : ℝ) (by norm_num) 8 4))
      (hB (6503803696031864026963787120640 : ℝ) (by norm_num) 9 3))
      (hB (1739670927946908417498823000064 : ℝ) (by norm_num) 10 2))
      (hB (279540010019766938838568534016 : ℝ) (by norm_num) 11 1))
      (hB (20390693777992301890620096512 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (20390693777992301890620096512 : ℝ) (by norm_num) 0 12)
      (hB (209836640652048306536313782272 : ℝ) (by norm_num) 1 11))
      (hB (972933864902003462174020730880 : ℝ) (by norm_num) 2 10))
      (hB (2678433707824029106018965258240 : ℝ) (by norm_num) 3 9))
      (hB (4853814727220979606515225722880 : ℝ) (by norm_num) 4 8))
      (hB (6062278005291956960882245763072 : ℝ) (by norm_num) 5 7))
      (hB (5304975003277304728299889491968 : ℝ) (by norm_num) 6 6))
      (hB (3237224528633743341812310867968 : ℝ) (by norm_num) 7 5))
      (hB (1343430411724571888637686579200 : ℝ) (by norm_num) 8 4))
      (hB (361410219546038725874881822720 : ℝ) (by norm_num) 9 3))
      (hB (59113181997720119142258585600 : ℝ) (by norm_num) 10 2))
      (hB (5937066241969469548894893568 : ℝ) (by norm_num) 11 1))
      (hB (462285289213617836815180800 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (462285289213617836815180800 : ℝ) (by norm_num) 0 12)
      (hB (5157780699157358534669445632 : ℝ) (by norm_num) 1 11))
      (hB (50541041026786897985778658304 : ℝ) (by norm_num) 2 10))
      (hB (328320956191047749008131512320 : ℝ) (by norm_num) 3 9))
      (hB (1302791270657649731531331604480 : ℝ) (by norm_num) 4 8))
      (hB (3331693774372275965054838259712 : ℝ) (by norm_num) 5 7))
      (hB (5764777234618392587457122238464 : ℝ) (by norm_num) 6 6))
      (hB (6930541942976880778828938149888 : ℝ) (by norm_num) 7 5))
      (hB (5823002613101590342779351203840 : ℝ) (by norm_num) 8 4))
      (hB (3365798319879197977904449454080 : ℝ) (by norm_num) 9 3))
      (hB (1278928560957425118481353539584 : ℝ) (by norm_num) 10 2))
      (hB (288233692493064025948359753728 : ℝ) (by norm_num) 11 1))
      (hB (29243460960565373030538149888 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (29243460960565373030538149888 : ℝ) (by norm_num) 0 12)
      (hB (413609370560504926784555843584 : ℝ) (by norm_num) 1 11))
      (hB (2658061019699275027679510528000 : ℝ) (by norm_num) 2 10))
      (hB (10269851841390275216830619320320 : ℝ) (by norm_num) 3 9))
      (hB (26585510544445788217170170347520 : ℝ) (by norm_num) 4 8))
      (hB (48606338544362926708118728802304 : ℝ) (by norm_num) 5 7))
      (hB (64391374104982876934050615492608 : ℝ) (by norm_num) 6 6))
      (hB (62307061888074092308948291928064 : ℝ) (by norm_num) 7 5))
      (hB (43724905774979971018910679142400 : ℝ) (by norm_num) 8 4))
      (hB (21711010710659236370951851223040 : ℝ) (by norm_num) 9 3))
      (hB (7242786336242531545131493760000 : ℝ) (by norm_num) 10 2))
      (hB (1457975454821315181245115098624 : ℝ) (by norm_num) 11 1))
      (hB (133966568557342410729058795520 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (133966568557342410729058795520 : ℝ) (by norm_num) 0 12)
      (hB (1757222190554902676252295993856 : ℝ) (by norm_num) 1 11))
      (hB (10534500429311993990210483607552 : ℝ) (by norm_num) 2 10))
      (hB (38171276614424697540896182394880 : ℝ) (by norm_num) 3 9))
      (hB (93115876116785248196039964262400 : ℝ) (by norm_num) 4 8))
      (hB (161119083030247590445848400756736 : ℝ) (by norm_num) 5 7))
      (hB (202782720810278650434784917979136 : ℝ) (by norm_num) 6 6))
      (hB (187062767991485666135751224459264 : ℝ) (by norm_num) 7 5))
      (hB (125535240372270782535539517030400 : ℝ) (by norm_num) 8 4))
      (hB (59772653807461336230886553681920 : ℝ) (by norm_num) 9 3))
      (hB (19168465070627088155060283113472 : ℝ) (by norm_num) 10 2))
      (hB (3717512324627516107887355101184 : ℝ) (by norm_num) 11 1))
      (hB (329746590970603228980691599360 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (329746590970603228980691599360 : ℝ) (by norm_num) 0 12)
      (hB (4196405858666961387649243283456 : ℝ) (by norm_num) 1 11))
      (hB (24436293945060986232441053118464 : ℝ) (by norm_num) 2 10))
      (hB (86097936295288566141118201200640 : ℝ) (by norm_num) 3 9))
      (hB (204427916529698909406201244549120 : ℝ) (by norm_num) 4 8))
      (hB (344597925018102251684502066692096 : ℝ) (by norm_num) 5 7))
      (hB (422862365661199632357001473818624 : ℝ) (by norm_num) 6 6))
      (hB (380606987529872539362278139232256 : ℝ) (by norm_num) 7 5))
      (hB (249380286830836191965547857346560 : ℝ) (by norm_num) 8 4))
      (hB (116000443214204807128261506211840 : ℝ) (by norm_num) 9 3))
      (hB (36360287912166518284655970555904 : ℝ) (by norm_num) 10 2))
      (hB (6895514373097374586202122896896 : ℝ) (by norm_num) 11 1))
      (hB (598314819299658629005892529152 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (598314819299658629005892529152 : ℝ) (by norm_num) 0 12)
      (hB (7464041290094432509939297802752 : ℝ) (by norm_num) 1 11))
      (hB (42614083999134155445764894520320 : ℝ) (by norm_num) 2 10))
      (hB (147226234915102336650761718896640 : ℝ) (by norm_num) 3 9))
      (hB (342798529529884842834782052577280 : ℝ) (by norm_num) 4 8))
      (hB (566665064974282337264693780692992 : ℝ) (by norm_num) 5 7))
      (hB (681886872463535430159072137084928 : ℝ) (by norm_num) 6 6))
      (hB (601794352074547716901133274513408 : ℝ) (by norm_num) 7 5))
      (hB (386564630056740665031871604326400 : ℝ) (by norm_num) 8 4))
      (hB (176241622733110959062560956088320 : ℝ) (by norm_num) 9 3))
      (hB (54129229138544424355820990627840 : ℝ) (by norm_num) 10 2))
      (hB (10054415528272628443814984941568 : ℝ) (by norm_num) 11 1))
      (hB (854071508271234190409345269760 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (854071508271234190409345269760 : ℝ) (by norm_num) 0 12)
      (hB (10443300670236992126009301532672 : ℝ) (by norm_num) 1 11))
      (hB (58406965700152424859958473129984 : ℝ) (by norm_num) 2 10))
      (hB (197537398375171445535009844101120 : ℝ) (by norm_num) 3 9))
      (hB (449894513987045028159787121377280 : ℝ) (by norm_num) 4 8))
      (hB (726780344614653338579511746035712 : ℝ) (by norm_num) 5 7))
      (hB (853737481778689393316696493031424 : ℝ) (by norm_num) 6 6))
      (hB (734593321556056534661347807182848 : ℝ) (by norm_num) 7 5))
      (hB (459373686304018927026660194775040 : ℝ) (by norm_num) 8 4))
      (hB (203537428724737939416969999738880 : ℝ) (by norm_num) 9 3))
      (hB (60627704817222365702269902480384 : ℝ) (by norm_num) 10 2))
      (hB (10895473513576244503277203936768 : ℝ) (by norm_num) 11 1))
      (hB (892843359033121380167276464128 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (892843359033121380167276464128 : ℝ) (by norm_num) 0 12)
      (hB (10532767103218668620737431202304 : ℝ) (by norm_num) 1 11))
      (hB (56637934303289030994332402401280 : ℝ) (by norm_num) 2 10))
      (hB (183416806531229213001849760645120 : ℝ) (by norm_num) 3 9))
      (hB (397981201980440430528703045304320 : ℝ) (by norm_num) 4 8))
      (hB (608714487132311377556459648712704 : ℝ) (by norm_num) 5 7))
      (hB (671724383958738407588679498334208 : ℝ) (by norm_num) 6 6))
      (hB (537524743150136499041824579518464 : ℝ) (by norm_num) 7 5))
      (hB (308487967909040591701121014169600 : ℝ) (by norm_num) 8 4))
      (hB (123191715310215313502463317770240 : ℝ) (by norm_num) 9 3))
      (hB (32232105379975878171019045765120 : ℝ) (by norm_num) 10 2))
      (hB (4893496809379372467485696589824 : ℝ) (by norm_num) 11 1))
      (hB (317579145972983640621056000000 : ℝ) (by norm_num) 12 0))]

/-- The upper certificate: `2·66134921·B - 10^8·A ≥ 0` on `[0,1]`, by a 32-piece Bernstein certificate with exact integer coefficients. -/
theorem perronCert_high :
    ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ 132269842 * perronNumerB t - 10 ^ 8 * perronNumerA t := by
  intro t ht
  refine nonneg_on_Icc_of_pieces
    (fun u : ℝ => 132269842 * perronNumerB u - 10 ^ 8 * perronNumerA u)
    32 (by norm_num) ?_ (t := t) ht
  intro i hi s hs
  obtain ⟨hs0, hs1⟩ := hs
  have h1s : (0:ℝ) ≤ 1 - s := by linarith
  have hB : ∀ (c : ℝ), 0 ≤ c → ∀ k j : ℕ, 0 ≤ c * s ^ k * (1 - s) ^ j :=
    fun c hc k j => mul_nonneg (mul_nonneg hc (pow_nonneg hs0 k)) (pow_nonneg h1s j)
  simp only [perronNumerA, perronNumerB]
  interval_cases i
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (13768188608014966587392000000 : ℝ) (by norm_num) 0 12)
      (hB (130408621989228532731096334336 : ℝ) (by norm_num) 1 11))
      (hB (553693663040638567372231278592 : ℝ) (by norm_num) 2 10))
      (hB (1385844516930014526280417935360 : ℝ) (by norm_num) 3 9))
      (hB (2259518047977572259257689047040 : ℝ) (by norm_num) 4 8))
      (hB (2498478605622141796720654155776 : ℝ) (by norm_num) 5 7))
      (hB (1885094451563171528651227267072 : ℝ) (by norm_num) 6 6))
      (hB (945542587933476636669587226624 : ℝ) (by norm_num) 7 5))
      (hB (292115796700854211968310968320 : ℝ) (by norm_num) 8 4))
      (hB (45064836942339893402005667840 : ℝ) (by norm_num) 9 3))
      (hB (1015745133255811266723807232 : ℝ) (by norm_num) 10 2))
      (hB (7479871048182899403135744 : ℝ) (by norm_num) 11 1))
      (hB (140756264742409792932087424 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (140756264742409792932087424 : ℝ) (by norm_num) 0 12)
      (hB (3370670482769652130966962432 : ℝ) (by norm_num) 1 11))
      (hB (38010841862191972813925900800 : ℝ) (by norm_num) 2 10))
      (hB (221335520038817329624254479360 : ℝ) (by norm_num) 3 9))
      (hB (768699042701066291552487464960 : ℝ) (by norm_num) 4 8))
      (hB (1741922022006053004211693985792 : ℝ) (by norm_num) 5 7))
      (hB (2706980731708097375827981123584 : ℝ) (by norm_num) 6 6))
      (hB (2953354094898066183800791990272 : ℝ) (by norm_num) 7 5))
      (hB (2269042923656281665595425587200 : ℝ) (by norm_num) 8 4))
      (hB (1206044089595955108172781649920 : ℝ) (by norm_num) 9 3))
      (hB (423181767385466770313147187200 : ℝ) (by norm_num) 10 2))
      (hB (88355502071603488224413745152 : ℝ) (by norm_num) 11 1))
      (hB (8325835515418466462345461760 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (8325835515418466462345461760 : ℝ) (by norm_num) 0 12)
      (hB (111464550298439706871877337088 : ℝ) (by norm_num) 1 11))
      (hB (677381297880665175435246698496 : ℝ) (by norm_num) 2 10))
      (hB (2472851309497113862447150858240 : ℝ) (by norm_num) 3 9))
      (hB (6044321987910758300401763123200 : ℝ) (by norm_num) 4 8))
      (hB (10428404836532200586245567971328 : ℝ) (by norm_num) 5 7))
      (hB (13030807472525695716898257584128 : ℝ) (by norm_num) 6 6))
      (hB (11888636113916796249367241449472 : ℝ) (by norm_num) 7 5))
      (hB (7863904067782437166992217907200 : ℝ) (by norm_num) 8 4))
      (hB (3679545388882504977786866140160 : ℝ) (by norm_num) 9 3))
      (hB (1156480576573742625920861600256 : ℝ) (by norm_num) 10 2))
      (hB (219298736995377854341448152832 : ℝ) (by norm_num) 11 1))
      (hB (18979697933715971142801534080 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (18979697933715971142801534080 : ℝ) (by norm_num) 0 12)
      (hB (236214013413805453085788665088 : ℝ) (by norm_num) 1 11))
      (hB (1342548617176446212108607235072 : ℝ) (by norm_num) 2 10))
      (hB (4608612366949328796842472222720 : ℝ) (by norm_num) 3 9))
      (hB (10643465652302743952860303605760 : ℝ) (by norm_num) 4 8))
      (hB (17424779578816904225542489899008 : ℝ) (by norm_num) 5 7))
      (hB (20738282696616859866948241457152 : ℝ) (by norm_num) 6 6))
      (hB (18081541383885507494414005567488 : ℝ) (by norm_num) 7 5))
      (hB (11463778646325290433074041978880 : ℝ) (by norm_num) 8 4))
      (hB (5154762518680143103701360312320 : ℝ) (by norm_num) 9 3))
      (hB (1560590069739358467964631252992 : ℝ) (by norm_num) 10 2))
      (hB (285641692589921683977019588608 : ℝ) (by norm_num) 11 1))
      (hB (23906174241196039657851191296 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (23906174241196039657851191296 : ℝ) (by norm_num) 0 12)
      (hB (288106489198783267811409002496 : ℝ) (by norm_num) 1 11))
      (hB (1587702832436835890142914805760 : ℝ) (by norm_num) 2 10))
      (hB (5290733170829285578465051934720 : ℝ) (by norm_num) 3 9))
      (hB (11874131634743250040598759997440 : ℝ) (by norm_num) 4 8))
      (hB (18909524311248599437737948348416 : ℝ) (by norm_num) 5 7))
      (hB (21910870159807395413722195820544 : ℝ) (by norm_num) 6 6))
      (hB (18613808183636451790881953808384 : ℝ) (by norm_num) 7 5))
      (hB (11506494882239509895690148659200 : ℝ) (by norm_num) 8 4))
      (hB (5047862698657010022172873871360 : ℝ) (by norm_num) 9 3))
      (hB (1491789101408430686378315678720 : ℝ) (by norm_num) 10 2))
      (hB (266665072284310070956435921664 : ℝ) (by norm_num) 11 1))
      (hB (21805140977822388028828734080 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (21805140977822388028828734080 : ℝ) (by norm_num) 0 12)
      (hB (256658311183427241735453696256 : ℝ) (by norm_num) 1 11))
      (hB (1381714729298719564947511199232 : ℝ) (by norm_num) 2 10))
      (hB (4498651547930791025716108917760 : ℝ) (by norm_num) 3 9))
      (hB (9865825688994872570503398461440 : ℝ) (by norm_num) 4 8))
      (hB (15353329958453149823103408971776 : ℝ) (by norm_num) 5 7))
      (hB (17385017847803199442508283953152 : ℝ) (by norm_num) 6 6))
      (hB (14431965154573709386899203784704 : ℝ) (by norm_num) 7 5))
      (hB (8717008165385191549429581905920 : ℝ) (by norm_num) 8 4))
      (hB (3735975269210587552184858378240 : ℝ) (by norm_num) 9 3))
      (hB (1078431197288196584806839877632 : ℝ) (by norm_num) 10 2))
      (hB (188249995549222051438220017664 : ℝ) (by norm_num) 11 1))
      (hB (15027467152885167046151634944 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (15027467152885167046151634944 : ℝ) (by norm_num) 0 12)
      (hB (172409216120021957669419220992 : ℝ) (by norm_num) 1 11))
      (hB (904182623566995553350031114240 : ℝ) (by norm_num) 2 10))
      (hB (2865991844802386828770412789760 : ℝ) (by norm_num) 3 9))
      (hB (6114614557347415982403834511360 : ℝ) (by norm_num) 4 8))
      (hB (9249827144762711327786125524992 : ℝ) (by norm_num) 5 7))
      (hB (10172225539056841423368106000384 : ℝ) (by norm_num) 6 6))
      (hB (8193143218521301354976518889472 : ℝ) (by norm_num) 7 5))
      (hB (4796330634173252651821629132800 : ℝ) (by norm_num) 8 4))
      (hB (1989988255826732745125301355520 : ℝ) (by norm_num) 9 3))
      (hB (555374902972721691798065896960 : ℝ) (by norm_num) 10 2))
      (hB (93599023296001267155183658752 : ℝ) (by norm_num) 11 1))
      (hB (7202979059043197888485148800 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (7202979059043197888485148800 : ℝ) (by norm_num) 0 12)
      (hB (79272474121035482168459912448 : ℝ) (by norm_num) 1 11))
      (hB (397782862048098056944104687616 : ℝ) (by norm_num) 2 10))
      (hB (1202967822423450600429473546240 : ℝ) (by norm_num) 3 9))
      (hB (2440907961282422395178015129600 : ℝ) (by norm_num) 4 8))
      (hB (3499203212518166608667306098688 : ℝ) (by norm_num) 5 7))
      (hB (3632226807439215886240755744768 : ℝ) (by norm_num) 6 6))
      (hB (2749151176479530336289294385152 : ℝ) (by norm_num) 7 5))
      (hB (1504895340062999968099178905600 : ℝ) (by norm_num) 8 4))
      (hB (580682663125342684102535413760 : ℝ) (by norm_num) 9 3))
      (hB (149832423019138045752645779456 : ℝ) (by norm_num) 10 2))
      (hB (23201133831160555887889743872 : ℝ) (by norm_num) 11 1))
      (hB (1630109587768903635115704320 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (1630109587768903635115704320 : ℝ) (by norm_num) 0 12)
      (hB (15921496275293131354887159808 : ℝ) (by norm_num) 1 11))
      (hB (69756409904596375889617354752 : ℝ) (by norm_num) 2 10))
      (hB (180709228875366333418276126720 : ℝ) (by norm_num) 3 9))
      (hB (307414825249462907831698063360 : ℝ) (by norm_num) 4 8))
      (hB (361507636739005205386979442688 : ℝ) (by norm_num) 5 7))
      (hB (303178170279564736925009969152 : ℝ) (by norm_num) 6 6))
      (hB (187206816239269705343049924608 : ℝ) (by norm_num) 7 5))
      (hB (89797328432400144564003143680 : ℝ) (by norm_num) 8 4))
      (hB (35918671928298304926007377920 : ℝ) (by norm_num) 9 3))
      (hB (12001774079100989040055437312 : ℝ) (by norm_num) 10 2))
      (hB (2842826599288623664962222848 : ℝ) (by norm_num) 11 1))
      (hB (328059123627432402004582016 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (328059123627432402004582016 : ℝ) (by norm_num) 0 12)
      (hB (5030592367769753983147745536 : ℝ) (by norm_num) 1 11))
      (hB (36067197532393422540096186880 : ℝ) (by norm_num) 2 10))
      (hB (156079015394505297111476689920 : ℝ) (by norm_num) 3 9))
      (hB (449277716029490069232004464640 : ℝ) (by norm_num) 4 8))
      (hB (903170781910840022192747749376 : ℝ) (by norm_num) 5 7))
      (hB (1299952788270297579741434036224 : ℝ) (by norm_num) 6 6))
      (hB (1351349375741936701760028770304 : ℝ) (by norm_num) 7 5))
      (hB (1008542972261237095791713484800 : ℝ) (by norm_num) 8 4))
      (hB (527860305062537215171080028160 : ℝ) (by norm_num) 9 3))
      (hB (184186729599999356686951383040 : ℝ) (by norm_num) 10 2))
      (hB (38521569040933605387988107264 : ℝ) (by norm_num) 11 1))
      (hB (3656176701477825405606952960 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (3656176701477825405606952960 : ℝ) (by norm_num) 0 12)
      (hB (49226671794534204346578763776 : ℝ) (by norm_num) 1 11))
      (hB (301942859889605945231448604672 : ℝ) (by norm_num) 2 10))
      (hB (1116000092533029447078801244160 : ℝ) (by norm_num) 3 9))
      (hB (2769117150807469526626287779840 : ℝ) (by norm_num) 4 8))
      (hB (4860972453556450896870600114176 : ℝ) (by norm_num) 5 7))
      (hB (6191949592544829486920402092032 : ℝ) (by norm_num) 6 6))
      (hB (5768395063055237647006408925184 : ℝ) (by norm_num) 7 5))
      (hB (3901572052058061538428959211520 : ℝ) (by norm_num) 8 4))
      (hB (1868947441524561851595090928640 : ℝ) (by norm_num) 9 3))
      (hB (601991979240878752113294213632 : ℝ) (by norm_num) 10 2))
      (hB (117090610474368384342025942784 : ℝ) (by norm_num) 11 1))
      (hB (10402521695859542706849064064 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (10402521695859542706849064064 : ℝ) (by norm_num) 0 12)
      (hB (132569910226260640622351594752 : ℝ) (by norm_num) 1 11))
      (hB (772264276511693571196876385280 : ℝ) (by norm_num) 2 10))
      (hB (2719396023644763799479438684160 : ℝ) (by norm_num) 3 9))
      (hB (6447440373015434496880623861760 : ℝ) (by norm_num) 4 8))
      (hB (10843712816779623403411991560192 : ℝ) (by norm_num) 5 7))
      (hB (13266795838409160961356276957184 : ℝ) (by norm_num) 6 6))
      (hB (11897664100615287264218470940672 : ℝ) (by norm_num) 7 5))
      (hB (7762728449872851627789411942400 : ℝ) (by norm_num) 8 4))
      (hB (3593868644106057516770782085120 : ℝ) (by norm_num) 9 3))
      (hB (1120720409740124512633088901120 : ℝ) (by norm_num) 10 2))
      (hB (211376280873645375046289457152 : ℝ) (by norm_num) 11 1))
      (hB (18235907000513473179539210240 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (18235907000513473179539210240 : ℝ) (by norm_num) 0 12)
      (hB (226285487138677981262651588608 : ℝ) (by norm_num) 1 11))
      (hB (1284721678655483181013072347136 : ℝ) (by norm_num) 2 10))
      (hB (4412954079398163021696325386240 : ℝ) (by norm_num) 3 9))
      (hB (10214459300041041120719798272000 : ℝ) (by norm_num) 4 8))
      (hB (16784563704763472511018255515648 : ℝ) (by norm_num) 5 7))
      (hB (20077592649493758012812370116608 : ℝ) (by norm_num) 6 6))
      (hB (17616031174143230931780846354432 : ℝ) (by norm_num) 7 5))
      (hB (11251943069018468811970353152000 : ℝ) (by norm_num) 8 4))
      (hB (5102557591553059764923679887360 : ℝ) (by norm_num) 9 3))
      (hB (1559417007889530911703254649856 : ℝ) (by norm_num) 10 2))
      (hB (288382607876255125004986989312 : ℝ) (by norm_num) 11 1))
      (hB (24405032774064010481699973760 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (24405032774064010481699973760 : ℝ) (by norm_num) 0 12)
      (hB (297338178701281126555812380928 : ℝ) (by norm_num) 1 11))
      (hB (1657928286964816928762333957632 : ℝ) (by norm_num) 2 10))
      (hB (5594466515814089415836229278720 : ℝ) (by norm_num) 3 9))
      (hB (12723785015109155158410918440960 : ℝ) (by norm_num) 4 8))
      (hB (20548073359712560767732195565568 : ℝ) (by norm_num) 5 7))
      (hB (24160768211218288974864811671552 : ℝ) (by norm_num) 6 6))
      (hB (20840724250014629470125387644928 : ℝ) (by norm_num) 7 5))
      (hB (13088663092345614437273435668480 : ℝ) (by norm_num) 8 4))
      (hB (5836682181778504787232911851520 : ℝ) (by norm_num) 9 3))
      (hB (1754236775415009343716816453632 : ℝ) (by norm_num) 10 2))
      (hB (319058649894921022394814169088 : ℝ) (by norm_num) 11 1))
      (hB (26556722089037922560676724736 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (26556722089037922560676724736 : ℝ) (by norm_num) 0 12)
      (hB (318302680241989119061427224576 : ℝ) (by norm_num) 1 11))
      (hB (1745921109232758407049560064000 : ℝ) (by norm_num) 2 10))
      (hB (5794981226345800867035335557120 : ℝ) (by norm_num) 3 9))
      (hB (12962824478918807255512940707840 : ℝ) (by norm_num) 4 8))
      (hB (20586848629213593266026170843136 : ℝ) (by norm_num) 5 7))
      (hB (23801271703832664698966817685504 : ℝ) (by norm_num) 6 6))
      (hB (20183550430966643350768046465024 : ℝ) (by norm_num) 7 5))
      (hB (12459173722288642447033678950400 : ℝ) (by norm_num) 8 4))
      (hB (5459740167700920048155185832960 : ℝ) (by norm_num) 9 3))
      (hB (1612120713715112205598874396160 : ℝ) (by norm_num) 10 2))
      (hB (287980546122080216376540702464 : ℝ) (by norm_num) 11 1))
      (hB (23535230514004116893500096640 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (23535230514004116893500096640 : ℝ) (by norm_num) 0 12)
      (hB (276864986214018589067461616896 : ℝ) (by norm_num) 1 11))
      (hB (1489849554726434305199004454912 : ℝ) (by norm_num) 2 10))
      (hB (4848959664390922193543517634560 : ℝ) (by norm_num) 3 9))
      (hB (10630283962158998767524763402240 : ℝ) (by norm_num) 4 8))
      (hB (16536128765563662323075017342976 : ℝ) (by norm_num) 5 7))
      (hB (18714225761699888011163270643712 : ℝ) (by norm_num) 6 6))
      (hB (15524001364515683170526706008064 : ℝ) (by norm_num) 7 5))
      (hB (9367267408293921082343287685120 : ℝ) (by norm_num) 8 4))
      (hB (4009329054346953280162145239040 : ℝ) (by norm_num) 9 3))
      (hB (1155330052552696742177230815232 : ℝ) (by norm_num) 10 2))
      (hB (201227146747393045057297711104 : ℝ) (by norm_num) 11 1))
      (hB (16019011832689762324430454784 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (16019011832689762324430454784 : ℝ) (by norm_num) 0 12)
      (hB (183229137237161250729033203712 : ℝ) (by norm_num) 1 11))
      (hB (957351947940147004566321233920 : ℝ) (by norm_num) 2 10))
      (hB (3020760537814493341774575042560 : ℝ) (by norm_num) 3 9))
      (hB (6409493897878273765182443356160 : ℝ) (by norm_num) 4 8))
      (hB (9632244854268712741592096571392 : ℝ) (by norm_num) 5 7))
      (hB (10510154667790940983201558953984 : ℝ) (by norm_num) 6 6))
      (hB (8387503416522757634021363023872 : ℝ) (by norm_num) 7 5))
      (hB (4857317243209028463359819776000 : ℝ) (by norm_num) 8 4))
      (hB (1990140080734391568156992798720 : ℝ) (by norm_num) 9 3))
      (hB (547433201467000378278923079680 : ℝ) (by norm_num) 10 2))
      (hB (90745532298554904548229700352 : ℝ) (by norm_num) 11 1))
      (hB (6853588757991270102135486080 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (6853588757991270102135486080 : ℝ) (by norm_num) 0 12)
      (hB (73740597893235577903021965568 : ℝ) (by norm_num) 1 11))
      (hB (360378923008487785181637997056 : ℝ) (by norm_num) 2 10))
      (hB (1056823056988172376569390218240 : ℝ) (by norm_num) 3 9))
      (hB (2069092383248433531989949030400 : ℝ) (by norm_num) 4 8))
      (hB (2846217203550528566763888222208 : ℝ) (by norm_num) 5 7))
      (hB (2817936042229699137740893339648 : ℝ) (by norm_num) 6 6))
      (hB (2021897924764918613000865677312 : ℝ) (by norm_num) 7 5))
      (hB (1043586507500207263488996966400 : ℝ) (by norm_num) 8 4))
      (hB (378583813062711856668113960960 : ℝ) (by norm_num) 9 3))
      (hB (92120094290348448092412051456 : ℝ) (by norm_num) 10 2))
      (hB (13658255542415991493068849152 : ℝ) (by norm_num) 11 1))
      (hB (953312766815731995666022400 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (953312766815731995666022400 : ℝ) (by norm_num) 0 12)
      (hB (9221250861161576402915688448 : ℝ) (by norm_num) 1 11))
      (hB (43313042796549882100727283712 : ℝ) (by norm_num) 2 10))
      (hB (136832323008427289077179678720 : ℝ) (by norm_num) 3 9))
      (hB (332034641825603134921131458560 : ℝ) (by norm_num) 4 8))
      (hB (639877131163877026086392987648 : ℝ) (by norm_num) 5 7))
      (hB (959702212309579038204380004352 : ℝ) (by norm_num) 6 6))
      (hB (1083553376543944336996748648448 : ℝ) (by norm_num) 7 5))
      (hB (891765040247033695991531233280 : ℝ) (by norm_num) 8 4))
      (hB (515683412832800715396423173120 : ℝ) (by norm_num) 9 3))
      (hB (198037218351471494119612221952 : ℝ) (by norm_num) 10 2))
      (hB (45313481406806178530537027328 : ℝ) (by norm_num) 11 1))
      (hB (4675507519964331350490979456 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (4675507519964331350490979456 : ℝ) (by norm_num) 0 12)
      (hB (66898699072337773881246479616 : ℝ) (by norm_num) 1 11))
      (hB (435474612672319042977416197120 : ℝ) (by norm_num) 2 10))
      (hB (1704988279836493067141799096320 : ℝ) (by norm_num) 3 9))
      (hB (4472387013654838395965795287040 : ℝ) (by norm_num) 4 8))
      (hB (8282886194937317242218426269696 : ℝ) (by norm_num) 5 7))
      (hB (11109743268052427113977239568384 : ℝ) (by norm_num) 6 6))
      (hB (10878404440329697466663823212544 : ℝ) (by norm_num) 7 5))
      (hB (7720848121446384411288272896000 : ℝ) (by norm_num) 8 4))
      (hB (3875133707404323253674322165760 : ℝ) (by norm_num) 9 3))
      (hB (1306046943916355505767925678080 : ℝ) (by norm_num) 10 2))
      (hB (265487411387479690416974987264 : ℝ) (by norm_num) 11 1))
      (hB (24623265705359878862793605120 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (24623265705359878862793605120 : ℝ) (by norm_num) 0 12)
      (hB (325470965541157402290071535616 : ℝ) (by norm_num) 1 11))
      (hB (1965866039606810336371987709952 : ℝ) (by norm_num) 2 10))
      (hB (7175522307110641768466439208960 : ℝ) (by norm_num) 3 9))
      (hB (17629772648089606126295465328640 : ℝ) (by norm_num) 4 8))
      (hB (30719491707039194619067997618176 : ℝ) (by norm_num) 5 7))
      (hB (38930501688343042861660482568192 : ℝ) (by norm_num) 6 6))
      (hB (36157424297916149633460827193344 : ℝ) (by norm_num) 7 5))
      (hB (24428565032710907775647370526720 : ℝ) (by norm_num) 8 4))
      (hB (11709569561761535079280544829440 : ℝ) (by norm_num) 9 3))
      (hB (3780326686238621987119572882432 : ℝ) (by norm_num) 10 2))
      (hB (738090893540212004537404922624 : ℝ) (by norm_num) 11 1))
      (hB (65914372214541727338954687104 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (65914372214541727338954687104 : ℝ) (by norm_num) 0 12)
      (hB (843854039608789451597507567872 : ℝ) (by norm_num) 1 11))
      (hB (4943721292992973904780701980160 : ℝ) (by norm_num) 2 10))
      (hB (17526262681757703781442079144960 : ℝ) (by norm_num) 3 9))
      (hB (41876964910045868565267306434560 : ℝ) (by norm_num) 4 8))
      (hB (71049149633900584716258211438592 : ℝ) (by norm_num) 5 7))
      (hB (87769310619802235146383160950784 : ℝ) (by norm_num) 6 6))
      (hB (79546040923994018854709260419072 : ℝ) (by norm_num) 7 5))
      (hB (52495084010717726951524624793600 : ℝ) (by norm_num) 8 4))
      (hB (24601672218474451311181840056320 : ℝ) (by norm_num) 9 3))
      (hB (7772009335572103299472620912640 : ℝ) (by norm_num) 10 2))
      (hB (1486095825486188511544392548352 : ℝ) (by norm_num) 11 1))
      (hB (130070781876287218159263416320 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (130070781876287218159263416320 : ℝ) (by norm_num) 0 12)
      (hB (1635602939544704724277929443328 : ℝ) (by norm_num) 1 11))
      (hB (9416587590215781639541526757376 : ℝ) (by norm_num) 2 10))
      (hB (32822008988271646098807830282240 : ℝ) (by norm_num) 3 9))
      (hB (77140767299582129838091361484800 : ℝ) (by norm_num) 4 8))
      (hB (128791403241935707127195212218368 : ℝ) (by norm_num) 5 7))
      (hB (156626856640017173258923193253888 : ℝ) (by norm_num) 6 6))
      (hB (139799082113588609901308461473792 : ℝ) (by norm_num) 7 5))
      (hB (90891635071297252308226533068800 : ℝ) (by norm_num) 8 4))
      (hB (41979550057705574816790509634560 : ℝ) (by norm_num) 9 3))
      (hB (13074167062508516365588424224256 : ℝ) (by norm_num) 10 2))
      (hB (2465281267593128918030902683392 : ℝ) (by norm_num) 11 1))
      (hB (212844163142231144073885530240 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (212844163142231144073885530240 : ℝ) (by norm_num) 0 12)
      (hB (2642978647820418539742350042368 : ℝ) (by norm_num) 1 11))
      (hB (15028838245008702204414345172992 : ℝ) (by norm_num) 2 10))
      (hB (51747639452303204098217917726720 : ℝ) (by norm_num) 3 9))
      (hB (120164304147670340676295577436160 : ℝ) (by norm_num) 4 8))
      (hB (198249628510725792582758645628928 : ℝ) (by norm_num) 5 7))
      (hB (238280697767700616440288800407552 : ℝ) (by norm_num) 6 6))
      (hB (210224129085421929107333650055168 : ℝ) (by norm_num) 7 5))
      (hB (135117519024714638575410431918080 : ℝ) (by norm_num) 8 4))
      (hB (61699889401551151784587396382720 : ℝ) (by norm_num) 9 3))
      (hB (19000471105811400936736551862272 : ℝ) (by norm_num) 10 2))
      (hB (3542917102244524829653826797568 : ℝ) (by norm_num) 11 1))
      (hB (302507746019091151267536306176 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (302507746019091151267536306176 : ℝ) (by norm_num) 0 12)
      (hB (3717268802213662800767044550656 : ℝ) (by norm_num) 1 11))
      (hB (20918339805471918618981947146240 : ℝ) (by norm_num) 2 10))
      (hB (71281403214481830657165644267520 : ℝ) (by norm_num) 3 9))
      (hB (163815082351275217961252804362240 : ℝ) (by norm_num) 4 8))
      (hB (267478378322346367537972621869056 : ℝ) (by norm_num) 5 7))
      (hB (318173888025685517330521589284864 : ℝ) (by norm_num) 6 6))
      (hB (277814769599687185277326788132864 : ℝ) (by norm_num) 7 5))
      (hB (176715820646190933999730481561600 : ℝ) (by norm_num) 8 4))
      (hB (79859975890303344005898157506560 : ℝ) (by norm_num) 9 3))
      (hB (24337515698526691941868323788800 : ℝ) (by norm_num) 10 2))
      (hB (4490782272622990522375065041664 : ℝ) (by norm_num) 11 1))
      (hB (379423828486009984075980918400 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (379423828486009984075980918400 : ℝ) (by norm_num) 0 12)
      (hB (4615389611041249095448476999936 : ℝ) (by norm_num) 1 11))
      (hB (25708196421127536245675855329792 : ℝ) (by norm_num) 2 10))
      (hB (86704176238550151882680425487360 : ℝ) (by norm_num) 3 9))
      (hB (197193202102386875776544947159040 : ℝ) (by norm_num) 4 8))
      (hB (318604012821357564343934049099776 : ℝ) (by norm_num) 5 7))
      (hB (374970377659681819656012590825472 : ℝ) (by norm_num) 6 6))
      (hB (323890278854561392448287917441024 : ℝ) (by norm_num) 7 5))
      (hB (203780765138098968373915889336320 : ℝ) (by norm_num) 8 4))
      (hB (91073417129133749196129734819840 : ℝ) (by norm_num) 9 3))
      (hB (27443356155133788040491470815232 : ℝ) (by norm_num) 10 2))
      (hB (5006098514840631848247505977344 : ℝ) (by norm_num) 11 1))
      (hB (418051864569740924204717441024 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (418051864569740924204717441024 : ℝ) (by norm_num) 0 12)
      (hB (5027146234833150332665712607232 : ℝ) (by norm_num) 1 11))
      (hB (27674881075051491369091743744000 : ℝ) (by norm_num) 2 10))
      (hB (92223314351347031599551062671360 : ℝ) (by norm_num) 3 9))
      (hB (207184092540487410146699652136960 : ℝ) (by norm_num) 4 8))
      (hB (330558102985176560461023745441792 : ℝ) (by norm_num) 5 7))
      (hB (384047159426853188789763715907584 : ℝ) (by norm_num) 6 6))
      (hB (327359915659486959707204218806272 : ℝ) (by norm_num) 7 5))
      (hB (203174480603490255620557685555200 : ℝ) (by norm_num) 8 4))
      (hB (89537137093582036550629048017920 : ℝ) (by norm_num) 9 3))
      (hB (26593152532338519820544028480000 : ℝ) (by norm_num) 10 2))
      (hB (4779209269303556669755375761152 : ℝ) (by norm_num) 11 1))
      (hB (393007550938688836160962040960 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (393007550938688836160962040960 : ℝ) (by norm_num) 0 12)
      (hB (4652971953224975398107713221888 : ℝ) (by norm_num) 1 11))
      (hB (25204542055474125832419740548096 : ℝ) (by norm_num) 2 10))
      (hB (82593163958498244157362046218240 : ℝ) (by norm_num) 3 9))
      (hB (182337036693667943724883307315200 : ℝ) (by norm_num) 4 8))
      (hB (285668892632873542008441123504128 : ℝ) (by norm_num) 5 7))
      (hB (325651244481763626947756860899328 : ℝ) (by norm_num) 6 6))
      (hB (272129654413185597746451811663872 : ℝ) (by norm_num) 7 5))
      (hB (165425112428001313755170550579200 : ℝ) (by norm_num) 8 4))
      (hB (71332170978153395578508316508160 : ℝ) (by norm_num) 9 3))
      (hB (20707902214523156911738643808256 : ℝ) (by norm_num) 10 2))
      (hB (3633325204520555923140910252032 : ℝ) (by norm_num) 11 1))
      (hB (291333716087454990075198177280 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (291333716087454990075198177280 : ℝ) (by norm_num) 0 12)
      (hB (3358683981578363838663846002688 : ℝ) (by norm_num) 1 11))
      (hB (17686848762159043982490937065472 : ℝ) (by norm_num) 2 10))
      (hB (56241668631708222097613096222720 : ℝ) (by norm_num) 3 9))
      (hB (120242194880918140304544770293760 : ℝ) (by norm_num) 4 8))
      (hB (182030270174901088581993950609408 : ℝ) (by norm_num) 5 7))
      (hB (200012029027877319132489910321152 : ℝ) (by norm_num) 6 6))
      (hB (160659358960819721399609364185088 : ℝ) (by norm_num) 7 5))
      (hB (93589705871006247369297710202880 : ℝ) (by norm_num) 8 4))
      (hB (38541518618186871040902312120320 : ℝ) (by norm_num) 9 3))
      (hB (10645161995159031778827891694592 : ℝ) (by norm_num) 10 2))
      (hB (1769589537889198465304497879808 : ℝ) (by norm_num) 11 1))
      (hB (133815651876228052553991264896 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (133815651876228052553991264896 : ℝ) (by norm_num) 0 12)
      (hB (1441986107140274795991292477696 : ℝ) (by norm_num) 1 11))
      (hB (7041524256920871416382632271360 : ℝ) (by norm_num) 2 10))
      (hB (20567570251531474663690614430720 : ℝ) (by norm_num) 3 9))
      (hB (39933302718252490847750213693440 : ℝ) (by norm_num) 4 8))
      (hB (54143890405197181414602892681216 : ℝ) (by norm_num) 5 7))
      (hB (52382514640582367045795489234944 : ℝ) (by norm_num) 6 6))
      (hB (36273018655944044485155103145984 : ℝ) (by norm_num) 7 5))
      (hB (17742773025820179865337889587200 : ℝ) (by norm_num) 8 4))
      (hB (5938731832809792382797537935360 : ℝ) (by norm_num) 9 3))
      (hB (1282587054869345641696648888320 : ℝ) (by norm_num) 10 2))
      (hB (160305137400878416685781745664 : ℝ) (by norm_num) 11 1))
      (hB (8985041702163475599699476480 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (8985041702163475599699476480 : ℝ) (by norm_num) 0 12)
      (hB (55335863451044997707005689856 : ℝ) (by norm_num) 1 11))
      (hB (127925041421178032930112274432 : ℝ) (by norm_num) 2 10))
      (hB (259552432191585835734534389760 : ℝ) (by norm_num) 3 9))
      (hB (1270018823701349204766956093440 : ℝ) (by norm_num) 4 8))
      (hB (5023309930133631764044515147776 : ℝ) (by norm_num) 5 7))
      (hB (11803819826599544813493364375552 : ℝ) (by norm_num) 6 6))
      (hB (17538954201145354805168478511104 : ℝ) (by norm_num) 7 5))
      (hB (17204590595465536934242924113920 : ℝ) (by norm_num) 8 4))
      (hB (11205315847172107143805121930240 : ℝ) (by norm_num) 9 3))
      (hB (4687350482768419737014750213632 : ℝ) (by norm_num) 10 2))
      (hB (1144649365380560725157604075264 : ℝ) (by norm_num) 11 1))
      (hB (124427827816093259762795196544 : ℝ) (by norm_num) 12 0))]
  · linarith [(add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hB (124427827816093259762795196544 : ℝ) (by norm_num) 0 12)
      (hB (1841618502205677509149480641792 : ℝ) (by norm_num) 1 11))
      (hB (12354010987844704360925392445440 : ℝ) (by norm_num) 2 10))
      (hB (49711810380797065244336531701760 : ℝ) (by norm_num) 3 9))
      (hB (133763226245801621121706345103360 : ℝ) (by norm_num) 4 8))
      (hB (253775695752909701565072898260992 : ℝ) (by norm_num) 5 7))
      (hB (348365788451220278511499040784384 : ℝ) (by norm_num) 6 6))
      (hB (348887544118831186533462124265472 : ℝ) (by norm_num) 7 5))
      (hB (253162539509117849419027107020800 : ℝ) (by norm_num) 8 4))
      (hB (129878120096383507142813438443520 : ℝ) (by norm_num) 9 3))
      (hB (44738473824250514264418953461760 : ℝ) (by norm_num) 10 2))
      (hB (9294842065836880617904906698752 : ℝ) (by norm_num) 11 1))
      (hB (881164070912957861593088000000 : ℝ) (by norm_num) 12 0))]
/-- **The `t = tan (πx/4)` dictionary** on `[0,1]`: the tangent
half-angle value lies in `[0,1]` and rationalizes the three sines and
cosines of the transfer bracket. -/
theorem tan_quarter_package {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.tan (π * x / 4) ∈ Set.Icc (0:ℝ) 1 ∧
    Real.sin (π * x / 2) =
      2 * Real.tan (π * x / 4) / (1 + Real.tan (π * x / 4) ^ 2) ∧
    Real.cos (π * x / 2) =
      (1 - Real.tan (π * x / 4) ^ 2) / (1 + Real.tan (π * x / 4) ^ 2) ∧
    Real.sin (π * x) =
      4 * Real.tan (π * x / 4) * (1 - Real.tan (π * x / 4) ^ 2) /
        (1 + Real.tan (π * x / 4) ^ 2) ^ 2 := by
  have hpi := Real.pi_pos
  have hθ0 : 0 ≤ π * x / 4 := by positivity
  have hθle : π * x / 4 ≤ π / 4 := by nlinarith
  have hc : 0 < Real.cos (π * x / 4) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have hs0 : 0 ≤ Real.sin (π * x / 4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by nlinarith)
  have hpyth := Real.sin_sq_add_cos_sq (π * x / 4)
  have hs2 : Real.sin (π * x / 4) ^ 2 = 1 - Real.cos (π * x / 4) ^ 2 := by
    linarith
  have ht_eq : Real.tan (π * x / 4) =
      Real.sin (π * x / 4) / Real.cos (π * x / 4) :=
    Real.tan_eq_sin_div_cos _
  have ht0 : 0 ≤ Real.tan (π * x / 4) := by
    rw [ht_eq]
    exact div_nonneg hs0 hc.le
  have hslec : Real.sin (π * x / 4) ≤ Real.cos (π * x / 4) := by
    rw [show Real.cos (π * x / 4) = Real.sin (π / 2 - π * x / 4) from
      (Real.sin_pi_div_two_sub _).symm]
    refine Real.strictMonoOn_sin.monotoneOn ⟨by nlinarith, by nlinarith⟩
      ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
  have ht1 : Real.tan (π * x / 4) ≤ 1 := by
    rw [ht_eq]
    exact (div_le_one hc).mpr hslec
  have hu : Real.sin (π * x / 2) =
      2 * Real.tan (π * x / 4) / (1 + Real.tan (π * x / 4) ^ 2) := by
    rw [show π * x / 2 = 2 * (π * x / 4) by ring, Real.sin_two_mul,
      ht_eq, div_pow, hs2]
    field_simp
    ring
  have hv : Real.cos (π * x / 2) =
      (1 - Real.tan (π * x / 4) ^ 2) / (1 + Real.tan (π * x / 4) ^ 2) := by
    rw [show π * x / 2 = 2 * (π * x / 4) by ring, Real.cos_two_mul,
      ht_eq, div_pow, hs2]
    field_simp
    ring
  refine ⟨⟨ht0, ht1⟩, hu, hv, ?_⟩
  rw [show π * x = 2 * (π * x / 2) by ring, Real.sin_two_mul, hu, hv]
  have h1t : (0:ℝ) < 1 + Real.tan (π * x / 4) ^ 2 := by positivity
  field_simp
  ring

/-- **The pointwise Collatz–Wielandt bracket** for the optimized test
function: `0.66126798·h ≤ 𝓛₁h ≤ 0.66134921·h` on `[0,1]`. -/
theorem perron_bracket_pointwise {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    66126798 / 10 ^ 8 * perronTest x ≤ rpfTransfer perronTest x ∧
      rpfTransfer perronTest x ≤ 66134921 / 10 ^ 8 * perronTest x := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨⟨ht0, ht1⟩, hu, hv, hw⟩ := tan_quarter_package hx0 hx1
  have h1t : (0:ℝ) < 1 + Real.tan (π * x / 4) ^ 2 := by positivity
  have hB : perronNumerB (Real.tan (π * x / 4)) =
      10 ^ 6 * (1 + Real.tan (π * x / 4) ^ 2) ^ 6 * perronTest x := by
    unfold perronTest perronTestCubic perronNumerB
    rw [hw]
    field_simp
    ring
  have hA : perronNumerA (Real.tan (π * x / 4)) =
      2 * 10 ^ 6 * (1 + Real.tan (π * x / 4) ^ 2) ^ 6 *
        rpfTransfer perronTest x := by
    unfold rpfTransfer perronTest perronTestCubic perronNumerA
    rw [show π * (x / 2) = π * x / 2 by ring,
      show π * ((x + 1) / 2) = π * x / 2 + π / 2 by ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two,
      hu, hv]
    field_simp
    ring
  have hclow := perronCert_low _ ⟨ht0, ht1⟩
  have hchigh := perronCert_high _ ⟨ht0, ht1⟩
  rw [hA, hB] at hclow hchigh
  constructor
  · have h2 : 0 ≤ (2 * 10 ^ 14 * (1 + Real.tan (π * x / 4) ^ 2) ^ 6) *
        (rpfTransfer perronTest x -
          66126798 / 10 ^ 8 * perronTest x) := by
      linarith
    have h3 := (mul_nonneg_iff_of_pos_left
      (show (0:ℝ) < 2 * 10 ^ 14 * (1 + Real.tan (π * x / 4) ^ 2) ^ 6
        by positivity)).mp h2
    linarith
  · have h2 : 0 ≤ (2 * 10 ^ 14 * (1 + Real.tan (π * x / 4) ^ 2) ^ 6) *
        (66134921 / 10 ^ 8 * perronTest x -
          rpfTransfer perronTest x) := by
      linarith
    have h3 := (mul_nonneg_iff_of_pos_left
      (show (0:ℝ) < 2 * 10 ^ 14 * (1 + Real.tan (π * x / 4) ^ 2) ^ 6
        by positivity)).mp h2
    linarith

/-- **The kernel-checked `ρ₁` enclosure**: any limit of
`(sup 𝓛₁ⁿ𝟙)^(1/n)` lies in `[0.66126798, 0.66134921]` — item 4 of the
comparative audit's feasibility list, with the Sturm step replaced by
subdivided Bernstein certificates. -/
theorem perron_root_enclosure {ρ : ℝ}
    (hlim : Filter.Tendsto (fun n : ℕ => transferSup n ^ ((1:ℝ) / n))
      Filter.atTop (nhds ρ)) :
    66126798 / 10 ^ 8 ≤ ρ ∧ ρ ≤ 66134921 / 10 ^ 8 :=
  perron_root_mem_of_two_sided perronTest_continuous
    (fun _ hx => perronTest_pos hx) (by norm_num) (by norm_num)
    (fun _ hx => (perron_bracket_pointwise hx).1)
    (fun _ hx => (perron_bracket_pointwise hx).2) hlim

/-- The Perron root exists and satisfies the kernel-checked enclosure
`0.66126798 ≤ ρ₁ ≤ 0.66134921`. -/
theorem exists_perron_root_enclosure :
    ∃ ρ : ℝ, Filter.Tendsto (fun n : ℕ => transferSup n ^ ((1:ℝ) / n))
      Filter.atTop (nhds ρ) ∧
      66126798 / 10 ^ 8 ≤ ρ ∧ ρ ≤ 66134921 / 10 ^ 8 := by
  obtain ⟨ρ, -, -, hlim⟩ := exists_perron_root
  exact ⟨ρ, hlim, perron_root_enclosure hlim⟩

end Fabius
