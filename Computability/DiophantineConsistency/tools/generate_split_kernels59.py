#!/usr/bin/env python3
"""Emit the literal three split116 kernels and checked sharp generic bounds."""
from pathlib import Path
import importlib.util, json, hashlib
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('certificate59',ROOT/'tools/generate_split_certificate59.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
raw=(ROOT/'data/split59/split_kernels.json').read_bytes()
g.require(hashlib.sha256(raw).hexdigest()==g.PINS['split_kernels.json'],'kernel pin')
doc=json.loads(raw)
header='''import DiophantineConsistency.SplitGeometry59
import DiophantineConsistency.SplitWordBounds
import Mathlib.Tactic.Linarith

/-!
# Literal report59 split116 kernels

Generated from SHA-pinned split_kernels.json by generate_split_kernels59.py.
All four native ports remain parameters. These are the actual89 polynomial
coefficient recipes, with degree ceilings and a sharp generic box bound.
-/
namespace DiophantineConsistency.SplitKernelData59

open Polynomial
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable def sparseKernel (e : Fin n → ℕ) (a : Fin n → R) : R[X] :=
  ∑ i, monomial (e i) (a i)

theorem coeff_sparseKernel (e : Fin n → ℕ) (he : Function.Injective e)
    (a : Fin n → R) (i : Fin n) : (sparseKernel e a).coeff (e i) = a i := by
  classical
  simp only [sparseKernel, finsetSum_coeff, coeff_monomial, he.eq_iff]
  simp

theorem sparseKernel_degree (e : Fin n → ℕ) (a : Fin n → R) {d : ℕ}
    (hd : ∀ i, e i ≤ d) : (sparseKernel e a).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp only [sparseKernel, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  have hne : e i ≠ j := by have hi := hd i; omega
  exact if_neg hne

theorem sparseKernel_height (e : Fin n → ℕ) (he : Function.Injective e)
    (a : Fin n → ℤ) {H : ℤ} (hH : 0 ≤ H) (ha : ∀ i, |a i| ≤ H) (j : ℕ) :
    |(sparseKernel e a).coeff j| ≤ H := by
  classical
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [coeff_sparseKernel e he]
    exact ha i
  · have hz : (sparseKernel e a).coeff j = 0 := by
      simp only [sparseKernel, finsetSum_coeff, coeff_monomial]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi => hj ⟨i,hi⟩)
    simpa only [hz,abs_zero] using hH
'''
out=[header]
coeffs=[]
for ch,degree in zip(doc['kernels'],[1719,2027,1929]):
 k=ch['degree'];terms=ch['terms'];n=len(terms)
 cs=[g.coefficient({tuple(v['powers']):v['coefficient'] for v in t['coefficient']}) for t in terms]
 coeffs.append(cs)
 out.append(f'def positions{k} : Fin {n} → ℕ := '+g.vec([str(t['exponent']) for t in terms])+'\n')
 out.append(f'def coefficients{k} (ports : Fin 4 → R) : Fin {n} → R := '+g.vec(cs)+'\n')
 out.append(f'theorem positions{k}_injective : Function.Injective positions{k} := by decide +kernel\n')
 out.append(f'theorem positions{k}_le : ∀ i, positions{k} i ≤ {degree} := by decide +kernel\n')
 out.append(f'noncomputable def D{k} (ports : Fin 4 → R) : R[X] := sparseKernel positions{k} (coefficients{k} ports)\n')
 out.append(f'theorem degree_D{k} (ports : Fin 4 → R) : (D{k} ports).natDegree ≤ {degree} :=\n  sparseKernel_degree _ _ positions{k}_le\n')
out.append('''theorem leading_D2 (ports : Fin 4 → R) : (D2 ports).coeff 1929 = 1 := by
  change (sparseKernel positions2 (coefficients2 ports)).coeff (positions2 42) = 1
  rw [coeff_sparseKernel _ positions2_injective]
  rfl

theorem kernelBounds_of_records (ports : Fin 4 → ℤ) (H : ℤ) (hH : 0 ≤ H)
    (h0 : ∀ i, |coefficients0 ports i| ≤ H)
    (h1 : ∀ i, |coefficients1 ports i| ≤ H)
    (h2 : ∀ i, |coefficients2 ports i| ≤ H) :
    SplitWordBounds.KernelBounds (D0 ports) (D1 ports) (D2 ports) H :=
  ⟨degree_D0 ports,degree_D1 ports,degree_D2 ports,
    sparseKernel_height _ positions0_injective _ hH h0,
    sparseKernel_height _ positions1_injective _ hH h1,
    sparseKernel_height _ positions2_injective _ hH h2,leading_D2 ports⟩

private theorem box_facts (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ports 0 ^ 2 ≤ B ^ 2 ∧ ports 3 * ports 0 ≤ 2*B^2 ∧
      ports 0 * (ports 1+1) < B*K ∧ 16*B^2 ≤ B*K := by
  have hsq : ports 0 ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hb.1 (by omega)).mpr hb.2.le
  have hp : ports 3 * ports 0 ≤ 2*B^2 := by
    calc
      _ ≤ (2*B)*B := mul_le_mul hf.2.le hb.2.le hb.1 (by omega)
      _ = _ := by ring
  have hl : ports 0 * (ports 1+1) < B*K := by
    calc
      _ ≤ ports 0*K := mul_le_mul_of_nonneg_left (by omega) hb.1
      _ < B*K := mul_lt_mul_of_pos_right hb.2 (by omega)
  refine ⟨hsq,hp,hl,?_⟩
  nlinarith [mul_nonneg (by omega : 0 ≤ B) (sub_nonneg.mpr hK)]

/-- Arithmetic facts shared by the two kernel coefficient bounds. -/
theorem port_box_facts (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ports 0 ^ 2 ≤ B ^ 2 ∧ ports 3 * ports 0 ≤ 2*B^2 ∧
      ports 0 * (ports 1+1) < B*K ∧ 16*B^2 ≤ B*K :=
  box_facts ports B K hB hK hb hk hm hf
''')
for k in range(len(coeffs)):
 out.append(f'''theorem records{k}_lt (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ∀ i, |coefficients{k} ports i| < 2*B*K := by
  obtain ⟨hsq,hp,hl,hBK⟩ := box_facts ports B K hB hK hb hk hm hf
  intro i
  fin_cases i <;> dsimp [coefficients{k}] <;> rw [abs_lt] <;> constructor <;>
    nlinarith only [hB,hK,hb.1,hb.2,hk.1,hk.2,hm.1,hm.2,hf.1,hf.2,hsq,hp,hl,hBK,sq_nonneg B]
''')
out.append('''theorem kernelBounds_box (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    SplitWordBounds.KernelBounds (D0 ports) (D1 ports) (D2 ports) (2*B*K) := by
  apply kernelBounds_of_records ports (2*B*K) (by have hBK := hK; nlinarith)
  · exact fun i => (records0_lt ports B K hB hK hb hk hm hf i).le
  · exact fun i => (records1_lt ports B K hB hK hb hk hm hf i).le
  · exact fun i => (records2_lt ports B K hB hK hb hk hm hf i).le

end DiophantineConsistency.SplitKernelData59
''')
(ROOT/'Lean/DiophantineConsistency/SplitKernelData59.lean').write_text('\n'.join(out))
print('Generated89 literal recipes in SplitKernelData59.lean')
