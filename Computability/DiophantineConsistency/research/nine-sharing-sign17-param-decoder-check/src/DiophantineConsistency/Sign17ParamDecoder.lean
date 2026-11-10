import DiophantineConsistency.Sign17KByteBinding

/-! SOURCE ONLY. The displayed decoder with its decimal seed as a parameter. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ParamDecoder

def maskAt (A : ℕ) : ℕ := A % 2 ^ 636
def payloadAt (A : ℕ) : ℕ := A / 2 ^ 636
def discoveryAt (A j : ℕ) : ℕ := DecimalMachine215.digit 2 (maskAt A) j

def sigmaAt (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => sigmaAt A j + discoveryAt A j

def radixAt (A j : ℕ) : ℕ := (sigmaAt A j + 2) ^ (1 - discoveryAt A j)

def prefixAt (A : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => prefixAt A j * radixAt A j

def markAt (A q : ℕ) : ℕ := DecimalMachine215.digit 2 (maskAt A) (430 + q)
def tallyAt (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => tallyAt A q + markAt A q

def flagsAt (A q : ℕ) : ℕ :=
  (14 + (markAt A q : ℤ) * ((DecimalMachine215.digit 16 (payloadAt A / prefixAt A 430) (tallyAt A q) : ℤ) - 14)).toNat

def rawTargetAt (A j : ℕ) : ℤ :=
  (sigmaAt A (j + 1) : ℤ) - ((payloadAt A / prefixAt A j % radixAt A j : ℕ) : ℤ)

def actionAt (A j : ℕ) : Bool × Bool × ℕ :=
  (decide (DecimalMachine215.digit 2 (flagsAt A (j / 2)) (2 * (j % 2)) = 1),
   decide (DecimalMachine215.digit 2 (flagsAt A (j / 2)) (2 * (j % 2) + 1) = 1),
   (rawTargetAt A j % 216).toNat)

theorem sigma_seed (j : ℕ) : sigmaAt DecimalMachine215.seed j = DecimalMachine215.sigma j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [sigmaAt, DecimalMachine215.sigma, ih, discoveryAt, DecimalMachine215.discovery, maskAt, DecimalMachine215.mask]

theorem radix_seed (j : ℕ) : radixAt DecimalMachine215.seed j = DecimalMachine215.radix j := by
  simp only [radixAt, DecimalMachine215.radix, sigma_seed, discoveryAt, DecimalMachine215.discovery, maskAt, DecimalMachine215.mask]

theorem prefix_seed (j : ℕ) : prefixAt DecimalMachine215.seed j = DecimalMachine215.prefixProduct j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [prefixAt, DecimalMachine215.prefixProduct, ih, radix_seed]

theorem mark_seed (q : ℕ) : markAt DecimalMachine215.seed q = DecimalMachine215.mark q := by
  rfl

theorem tally_seed (q : ℕ) : tallyAt DecimalMachine215.seed q = DecimalMachine215.tally q := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [tallyAt, DecimalMachine215.tally, ih, mark_seed]

theorem flags_seed (q : ℕ) : flagsAt DecimalMachine215.seed q = DecimalMachine215.flags q := by
  simp only [flagsAt, DecimalMachine215.flags, mark_seed, payloadAt, DecimalMachine215.payload, prefix_seed, tally_seed]

theorem rawTarget_seed (j : ℕ) : rawTargetAt DecimalMachine215.seed j = DecimalMachine215.rawTarget j := by
  simp only [rawTargetAt, DecimalMachine215.rawTarget, sigma_seed, payloadAt, DecimalMachine215.payload, prefix_seed, radix_seed]

theorem action_seed (j : ℕ) : actionAt DecimalMachine215.seed j = DecimalMachine215.action j := by
  simp only [actionAt, DecimalMachine215.action, flags_seed, rawTarget_seed, DecimalMachine215.target]

end DiophantineConsistency.Sign17ParamDecoder
#print axioms DiophantineConsistency.Sign17ParamDecoder.action_seed
