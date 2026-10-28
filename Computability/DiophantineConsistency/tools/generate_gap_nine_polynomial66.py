#!/usr/bin/env python3
"""Supply the H2082 scalar/MvPolynomial recipe and checked finite coefficient maps.
Only inert checked Lean expression tables and the frozen split116 proof template
are read. Lean checks each generated finite-case proof against its table.
"""
from pathlib import Path
import argparse,hashlib,re,json
ROOT=Path(__file__).resolve().parents[1]

def render():
 source=(ROOT/'Lean/DiophantineConsistency/GapKernelData66.lean').read_text()
 text=(ROOT/'Lean/DiophantineConsistency/SplitNinePolynomial59.lean').read_text()
 text=text.replace('SplitKernelData59','GapKernelData66').replace('SplitNinePolynomial59','GapNinePolynomial66')
 text=text.replace('SplitNineSource59','GapNineSource66').replace('SplitSourceWords','GapSourceWords66').replace('SplitSourceExistence','GapSourceExistence66').replace('SplitNineRatio','GapNineRatio66')
 text=text.replace('SplitCertificate59','GapCertificate66').replace('GapCertificate66.sourceRows','GapSource66.rows')
 text=text.replace('^2279','^2200').replace('^(8*a+85)','^(15*a+79)').replace('((2:ℤ)^a)','((2:ℤ)^(2*a))')
 text=text.replace('def threshold (scale base b : A) : A := scale*b*base^1201','def threshold (scale base : A) : A := scale*base^1162')
 text=text.replace('(threshold scale base (x 0))','(threshold scale base)')
 text=text.replace('threshold ((2:ℤ)^(15*a+79)) (GapNineRatio66.base a b:ℤ) b','threshold ((2:ℤ)^(15*a+79)) (GapNineRatio66.base a b:ℤ)')
 text=text.replace('(threshold ((2:ℤ)^(15*a+79)) (sourceBase ((2:ℤ)^(2*a)) b) b)','(threshold ((2:ℤ)^(15*a+79)) (sourceBase ((2:ℤ)^(2*a)) b))')
 text=text.replace('simp only [kernel0,D0,sparseKernel,','simp only [kernel0,D0,sparseKernel,SplitKernelData59.sparseKernel,').replace('simp only [kernel1,D1,sparseKernel,','simp only [kernel1,D1,sparseKernel,SplitKernelData59.sparseKernel,').replace('simp only [kernel2,D2,sparseKernel,','simp only [kernel2,D2,sparseKernel,SplitKernelData59.sparseKernel,')
 text=text.replace('    GapNineSource66.parameters,','    GapNineSource66.parameters,GapSourceWords66.literalParameters,')
 text=text.replace('    SplitWordBounds.powerSum,', '    SplitWordBounds.powerSum,')
 text=text.replace('# Literal nine-variable polynomial for the split116 free-carrier recipe','# Literal nine-variable polynomial for the H2082 free-carrier recipe').replace('7+39+43','6+36+43')
 # Regenerate finite-case maps for the actual85 checked coefficient recipes.
 blocks=[f'-- H2082 kernel table SHA256 {hashlib.sha256(source.encode()).hexdigest()}.']
 for layer,count in enumerate((6,36,43)):
  found=re.search(rf'def coefficients{layer} .*? := !\[(.*?)\]\n',source,re.S)
  if found is None:raise ValueError('coefficient layer missing')
  exprs=[p.strip()for p in found.group(1).split(',')]
  if len(exprs)!=count:raise ValueError('coefficient count')
  blocks.extend(['set_option linter.unusedSimpArgs false in',
    f'theorem map_coefficients{layer} (f : A →+* B) (ports : Fin 4 → A) (i : Fin {count}) :',
    f'    f (coefficients{layer} ports i)=coefficients{layer} (fun j => f (ports j)) i := by',
    f'  fin_cases i <;> dsimp only [coefficients{layer}, Fin.reduceFinMk, Matrix.cons_val]',
    '  all_goals simp only [map_neg, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one, map_zero]'])
  blocks.append('')
 start='-- BEGIN GENERATED COEFFICIENT MAPS\n';end='-- END GENERATED COEFFICIENT MAPS\n'
 before,rest=text.split(start,1);_,after=rest.split(end,1)
 text=before+start+'\n'.join(blocks)+end+after
 # The H2082 parameter a is half the coefficient-height exponent.
 start=text.index('theorem exists_natural_zero_iff_source_portBounds')
 end=text.index('theorem no_natural_zero_iff_source')
 text=text[:start]+'''theorem exists_natural_zero_iff_source_portBounds (ports : Fin 4 → ℤ) (p q a : ℕ)
    (hp : 1≤p) (hpq : p+4≤q) (ha : p+q+1=2*a)
    (hb : 0≤ports 0 ∧ ports 0<2^p)
    (hk : 0≤ports 1 ∧ ports 1<2^q)
    (hm : 0≤ports 2 ∧ ports 2<2^p)
    (hf : 0≤ports 3 ∧ ports 3<2*2^p) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports a)=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        GapSource66.rows ports (fun i => (z i:ℤ)+1) j=0 :=
  exists_natural_zero_iff_source ports a
    (GapSourceWords66.literal_valid_pow ports p q a hp hpq ha hb hk hm hf)

theorem exists_natural_zero_iff_source_compact54 (ports : Fin 4 → ℤ)
    (hb : 0≤ports 0 ∧ ports 0<2^429959)
    (hk : 0≤ports 1 ∧ ports 1<2^434054)
    (hm : 0≤ports 2 ∧ ports 2<2^429959)
    (hf : 0≤ports 3 ∧ ports 3<2*2^429959) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports 432007)=0) ↔
      ∃ z : Fin 31 → ℕ, ∀ j,
        GapSource66.rows ports (fun i => (z i:ℤ)+1) j=0 :=
  exists_natural_zero_iff_source_portBounds ports 429959 434054 432007
    (by decide) (by decide) (by decide) hb hk hm hf

'''+text[end:]
 extra='''/-- The complete compact54 H2082 polynomial and earlier split116 polynomial
have the same natural root existence, through the proved positive affine
source change. This is not a native consistency calibration. -/
theorem compact54_zero_iff_split59 (ports : Fin 4 → ℤ) (hβ : 0<ports 0)
    (hb : 0≤ports 0 ∧ ports 0<2^429959)
    (hk : 0≤ports 1 ∧ ports 1<2^434054)
    (hm : 0≤ports 2 ∧ ports 2<2^429959)
    (hf : 0≤ports 3 ∧ ports 3<2*2^429959) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ)) (polynomial ports 432007)=0) ↔
      ∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i:ℤ))
        (SplitNinePolynomial59.polynomial ports 864014)=0 :=
  (exists_natural_zero_iff_source_compact54 ports hb hk hm hf).trans
    ((GapNineSource66.source_successor_zero_iff_old ports hβ).trans
      (SplitNinePolynomial59.exists_natural_zero_iff_source_compact54 ports hb hk hm hf).symm)

'''
 text=text.replace('import DiophantineConsistency.FreeCarrierRatio',
   'import DiophantineConsistency.FreeCarrierRatio\nimport DiophantineConsistency.SplitNinePolynomial59')
 text=text.replace('end DiophantineConsistency.GapNinePolynomial66',extra+'end DiophantineConsistency.GapNinePolynomial66')
 return text

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 p=ROOT/'Lean/DiophantineConsistency/GapNinePolynomial66.lean';s=render()
 if a.check:
  if p.read_text()!=s:raise ValueError('generated polynomial differs')
 else:p.write_text(s)
 print(json.dumps({'status':'PASS'if a.check else'GENERATED','coefficient_records':85,'variables':9,'height_exponent':'2*a','threshold_scale_exponent':'15*a+79','threshold_base_power':1162},sort_keys=True))
