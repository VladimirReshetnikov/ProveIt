import GRHArticle.SingularModuli.Prime17DiagonalCertificate
import GRHArticle.SingularModuli.HeckeCofactorEnclosure
import GRHArticle.SingularModuli.QuarticClassPolynomialCertificates

/-!
# Identifying the discriminant -68 analytic quartic

The diagonal at level 17 has the printed quartic as a factor. Its other
factor has no zero in any of the four disjoint boxes around the actual
modular invariant values.
-/

namespace GRHArticle.SingularModuli

open Polynomial

private def diagonal17CofactorCoefficients : List ℤ := [
  76201465028144685685476802833910667356812202668782104343270862494034798813130874465313120673441385731231448733410844745263897136327841104848224256000000000000000000000000000000000000000000,
  883506966902718182040911285009842846349658555240284812887034606562502471941116374966129582576620219019940786613103494988151728960963391007452299264000000000000000000000000000000000000000,
  -5801474675058342372700669790757087207977330361508592258284711144160146055739597033408184578035939233897952351649629027979846211005581371013244911616000000000000000000000000000000000000,
  -40250169575061476445254364215804318105716799657755406957120793897371066256817086193375766767893213500346706040100977074593990141254448269352083914752000000000000000000000000000000000,
  274069161844777835675197168146507243633784451179077273937273529009977284312068003676449480573890159190056545345317755087091223969287285146865387962368000000000000000000000000000000,
  -468601140463432704161090783408454236324085787722511070061650664436085662181657380982953605336426185875593874669058146868930491531287111774217313452032000000000000000000000000000,
  393097614643348615488749811848783347020910202984990580739585979603157151044456860315490471177781701884773644241192812659941143641658102686624413384704000000000000000000000000,
  -197398156574181912556952679778170053608536197983884242655776807755407302562197327455101653512835291378399605368743118109427510401818928697249894498304000000000000000000000,
  64359630947071003499269102110392256124622953716328522967088863254502420437554538628763546370371452636801128843598494007304599126390296715309327843328000000000000000000,
  -13730327835878401896789459755118332554581816764137975303512631084979416804638298049598013100718914535034541548636315497492499996762231896170557341696000000000000000,
  1841270961213461527010195568807205702911470019268206281244777607097906577328329753946032772820411554288790118809900243106958119229655215220295991296000000000000,
  -131764591079719307529850057602370212438924280271359603827657930547897455782615634934471357311185874501858690672628895271792563971036320485659901952000000000,
  2642454157393375587164283145729254324238748492625146553431956337462102796331575344998103424728195188922209656739305778543066395833382756119740416000000,
  109625013999489375527958274766179235512948724563098515615286445004880799656893390931158919751068438655615998726517652666774099520320393812377600000,
  308265349461914528691422127687836262386909823526230704724529843194881235448227994605001282493742588846674702765374539552440248482713384779776,
  -4380729283850808772194914251333265017120022334638409171411451943355263326896629922521373148607576281710542671927932422442046684095578112,
  324594628444067720591021281946445444614717720064017183938611238544027655090227924233178364661167777280593208537854348568238751744,
  18053796199773220707377106072733487653879246226854935008092301322817357238906302598182749741634878279398912476620255670566912,
  12924816761347182173518968121075080272627808153753396447897300257365324314867358291998693745913354602079022059276468224,
  -487050579580062207317371586795194449378018501110443588784595938871654879178276810853993435001373948152425480192,
  3944073463437957601218311017196121858801468634364553034530691403936701180932377322898889768418515353600,
  9687980774990184033622173773123897924950554785149350254930065747244578349154430732634356187136,
  3890994027452744398105969930050490794153078076989146650719353101748794164481320812544,
  -1431128178022667865731452639727289469011836705520959148276441832857118310400,
  44331260746937279412759516631551613032281887369759710887810281472,
  6941999253132351426274749008915293272773396378748138496,
  65288857310815658093426025068100354426721344,
  -2520319037332674408838892198866944,
  -13509074910015583168080,
  178211014704,
  1
]

private def quartic68CoefficientList : List ℤ :=
  [-2089297506304000000000000, -318507038720000000000, -75843692160000000,
    -178211040000, 1]

private def coarseRootBox (x y : ℤ) : RationalComplexBox :=
  ⟨⟨(x : ℚ) - 1, (x : ℚ) + 1⟩, ⟨(y : ℚ) - 1, (y : ℚ) + 1⟩⟩

private def quartic68CoarseBoxes : Fin 4 → RationalComplexBox :=
  ![coarseRootBox (178211465583) (0), coarseRootBox (-421407) (0), coarseRootBox (-2088) (-4844), coarseRootBox (-2088) (4844)]

private theorem quartic68CoefficientList_eq :
    coefficientListPolynomial quartic68CoefficientList = quartic68Int := by
  ext n
  by_cases hn : n ≤ 4
  · let i : Fin 5 := ⟨n, Nat.lt_succ_of_le hn⟩
    have h (j : Fin 5) : quartic68CoefficientList.getD j 0 = quartic68PrintedCoefficient j := by
      fin_cases j <;> decide +kernel
    rw [coeff_coefficientListPolynomial, h i, ← quartic68_printed_coeff]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (natDegree_coefficientListPolynomial_le (n := 4) (by decide)) (lt_of_not_ge hn)),
      coeff_eq_zero_of_natDegree_lt (quartic68Int_natDegree.trans_lt (lt_of_not_ge hn))]

private theorem diagonal17_factor :
    coefficientListPolynomial Prime17Data.diagonal =
      quartic68Int * coefficientListPolynomial diagonal17CofactorCoefficients := by
  have hcompute : Prime17Data.diagonal =
      multiplyPackedIntegerPolynomial 35 quartic68CoefficientList diagonal17CofactorCoefficients := by
    decide +kernel
  have hH : (coefficientListPolynomial quartic68CoefficientList).natDegree ≤ 4 :=
    natDegree_coefficientListPolynomial_le (by decide)
  have hR : (coefficientListPolynomial diagonal17CofactorCoefficients).natDegree ≤ 30 :=
    natDegree_coefficientListPolynomial_le (by decide)
  have hd : (coefficientListPolynomial quartic68CoefficientList *
      coefficientListPolynomial diagonal17CofactorCoefficients).natDegree < 35 :=
    Polynomial.natDegree_mul_le.trans_lt (by omega)
  rw [hcompute, coefficientListPolynomial_multiplyPackedIntegerPolynomial _ _ _ hd,
    quartic68CoefficientList_eq]

private noncomputable def root68 (i : Fin 4) : ℂ :=
  modularInvariant (quadraticPoint 68 (quartic68Form i).a (quartic68Form i).b)

private theorem coarse_root68_contains (i : Fin 4)
    (hbound :
      let A := modularInvariantBox (quartic68QBox i)
      let B := quartic68CoarseBoxes i
      B.re.lo ≤ A.re.lo ∧ A.re.hi ≤ B.re.hi ∧ B.im.lo ≤ A.im.lo ∧ A.im.hi ≤ B.im.hi) :
    (quartic68CoarseBoxes i).Contains (root68 i) := by
  have h := quartic68_modularInvariant_box_contains i
  refine ⟨⟨(Rat.cast_le.mpr hbound.1).trans h.1.1,
       h.1.2.trans (Rat.cast_le.mpr hbound.2.1)⟩,
    ⟨(Rat.cast_le.mpr hbound.2.2.1).trans h.2.1,
       h.2.2.trans (Rat.cast_le.mpr hbound.2.2.2)⟩⟩

private theorem quartic68Cofactor_excludesZero (i : Fin 4) :
    ((quartic68CoarseBoxes i).evaluateIntegerCoefficients
      diagonal17CofactorCoefficients).ExcludesZero := by
  fin_cases i <;> decide +kernel

private theorem quartic68Coarse_pairwiseSeparated
    (i j : Fin 4) (hij : i < j) :
    (quartic68CoarseBoxes i).Separated (quartic68CoarseBoxes j) := by
  fin_cases i <;> fin_cases j <;> first
  | decide +kernel
  | exact ((by decide : ¬(_ : Fin 4) < _) hij).elim

private theorem quartic68_root_from_diagonal
    (hdiag : ∀ z : UpperHalfPlane, aeval (modularInvariant z)
      (coefficientListPolynomial Prime17Data.diagonal) = -analyticPrimeHeckeDiagonal 17 z)
    (hbox : ∀ i : Fin 4, (quartic68CoarseBoxes i).Contains (root68 i)) (i : Fin 4) :
    aeval (root68 i) quartic68Int = 0 := by
  letI : Fact (Nat.Prime ((17 : ℕ+) : ℕ)) := ⟨by decide⟩
  let f := quartic68Form i
  let z := quadraticPoint 68 f.a f.b
  let P := coefficientListPolynomial Prime17Data.diagonal
  let R := coefficientListPolynomial diagonal17CofactorCoefficients
  have hP : aeval (modularInvariant z) P = -analyticPrimeHeckeDiagonal 17 z :=
    hdiag z
  have hz : analyticPrimeHeckeDiagonal 17 z = 0 := quartic68_analyticPrimeHeckePolynomial_diagonal i
  have hn : aeval (modularInvariant z) R ≠ 0 :=
    RationalComplexBox.ne_zero_of_contains_of_excludesZero
      (RationalComplexBox.contains_evaluateIntegerCoefficients (hbox i) _) (quartic68Cofactor_excludesZero i)
  change aeval (modularInvariant z) quartic68Int = 0
  exact aeval_factor_eq_zero_of_primeHeckeDiagonal_zero 17 P quartic68Int R 1 hP
    (by simpa only [pow_one] using diagonal17_factor) hz hn

private theorem quartic68_root68_injective
    (hbox : ∀ i : Fin 4, (quartic68CoarseBoxes i).Contains (root68 i)) :
    Function.Injective root68 := by
  intro i j he
  rcases lt_trichotomy i j with lt | eq | gt
  · exact (RationalComplexBox.ne_of_contains_of_separated (hbox i) (hbox j)
      (quartic68Coarse_pairwiseSeparated i j lt) he).elim
  · exact eq
  · exact (RationalComplexBox.ne_of_contains_of_separated (hbox j) (hbox i)
      (quartic68Coarse_pairwiseSeparated j i gt) he.symm).elim

set_option maxHeartbeats 1000000 in
private theorem quartic68_identification_from_certificates
    (hdiag : ∀ z : UpperHalfPlane, aeval (modularInvariant z)
      (coefficientListPolynomial Prime17Data.diagonal) = -analyticPrimeHeckeDiagonal 17 z)
    (hbox : ∀ i : Fin 4, (quartic68CoarseBoxes i).Contains (root68 i)) :
    analyticClassPolynomial 68 = quartic68Int.map (Int.castRingHom ℂ) := by
  classical
  let H := quartic68Int.map (Int.castRingHom ℂ)
  let Z := (Finset.univ : Finset (Fin 4)).val.map root68
  have hZ : Z.Nodup :=
    Finset.univ.nodup.map (quartic68_root68_injective hbox)
  have hH : H.Monic := quartic68Int_monic.map _
  have hZle : Z ≤ H.roots := by
    apply (Multiset.le_iff_subset hZ).mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    refine (Polynomial.mem_roots hH.ne_zero).mpr ?_
    rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map]
    exact quartic68_root_from_diagonal hdiag hbox i
  have hdiv : (Z.map fun x ↦ X - C x).prod ∣ H :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hH.ne_zero Z).mpr hZle
  have hclass : analyticClassPolynomial 68 = (Z.map fun x ↦ X - C x).prod := by
    have hrhs : (Z.map fun x ↦ X - C x).prod = ∏ i : Fin 4, (X - C (root68 i)) := by
      simp only [Z, Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]
    rw [hrhs, Fin.prod_univ_four, analyticClassPolynomial, reducedForms_sixtyEight]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    simp only [root68, quartic68Form, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_assoc]
  rw [← hclass] at hdiv
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le (analyticClassPolynomial_monic 68) hH hdiv ?_
  rw [analyticClassPolynomial_sixtyEight_natDegree, show H.natDegree = 4 by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, quartic68Int_natDegree]]

private theorem quartic68Coarse_bounds (i : Fin 4) :
    let A := modularInvariantBox (quartic68QBox i)
    let B := quartic68CoarseBoxes i
    B.re.lo ≤ A.re.lo ∧ A.re.hi ≤ B.re.hi ∧ B.im.lo ≤ A.im.lo ∧ A.im.hi ≤ B.im.hi := by
  dsimp only
  rw [quartic68_rootBoxes_eq]
  fin_cases i <;> decide +kernel

/-- A certified level-17 diagonal identifies the analytic class polynomial. -/
theorem analyticClassPolynomial_sixtyEight_eq_printed_of_diagonal
    (hdiag : ∀ z : UpperHalfPlane, aeval (modularInvariant z)
      (coefficientListPolynomial Prime17Data.diagonal) = -analyticPrimeHeckeDiagonal 17 z) :
    analyticClassPolynomial 68 = quartic68Int.map (Int.castRingHom ℂ) :=
  quartic68_identification_from_certificates hdiag
    (fun i ↦ coarse_root68_contains i (quartic68Coarse_bounds i))

end GRHArticle.SingularModuli
