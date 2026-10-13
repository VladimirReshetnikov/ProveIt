"""Assemble the consolidated final route (Notes L.16-final) from the used declarations.

usage: python -X utf8 assemble_final.py USED_NAMES
Writes Proofs18FinalClasses / Proofs18FinalStep / Proofs18FinalEnvelopes /
Proofs18Final into the GowersSzemeredi source directory.
"""
import importlib.util
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('fe', HERE / 'final_extract.py')
fe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fe)
GS = fe.GS

# declarations replaced by the generic statements of `Proofs18Final`
EXCLUDE = {'theorem_18_2_L0_thirteen_le_of_profiles_poly',
           'corollary_18_7_L0_thirteen_le_of_profiles_poly'}

GROUPS = {
    'Proofs18FinalClasses': ['Proofs18FejerEnvelopeBaseQ', 'Proofs18TightClassesFejerQ',
                             'Proofs18TightClassesFejerS', 'Proofs18TightClassesFejerT',
                             'Proofs18FejerEnvelopeBaseW', 'Proofs18TightClassesFejerX',
                             'Proofs18TightClassesFejerZ', 'Proofs18TightClassesFejerM',
                             'Proofs16SplitTwoTrack', 'Proofs16SplitTwoTrackClasses',
                             'Proofs16UniformCoverTwoTight', 'Proofs16SplitTwoTrackClassesT3'],
    'Proofs18FinalStep': None,  # every chain module up to the JT3 exponents
    'Proofs18FinalEnvelopes': ['Proofs18CoverFejerHeadlineZ', 'Proofs18CoverFejerHeadlineY',
                               'Proofs18CoverFejerHeadlineJ', 'Proofs18CoverFejerHeadlineK',
                               'Proofs18CoverFejerHeadlineK3', 'Proofs16PolynomialFejerQ',
                               'Proofs16PolynomialFejerS', 'Proofs16PolynomialFejerX',
                               'Proofs16PolynomialFejerJ', 'Proofs16PolynomialFejerT3'],
    'Proofs18Final': ['Proofs18CoverFejerLowDegrees5', 'Proofs18CoverFejerLowDegrees4',
                      'Proofs18CoverFejerShortLengths3'],
}
BASE = ['Proofs16PolynomialFejer', 'Proofs16UniformCoverTwoSplit', 'Proofs16WeylBudgetGrowth',
        'Proofs18CoverFejerLowDegrees', 'Proofs18CoverFejerShortLengths', 'Proofs18EtaStepSmall',
        'Proofs18JointSliceInverseFejer']


def imports_of(m):
    return [d.split('.', 1)[1] for d in
            re.findall(r'^import\s+(GowersSzemeredi\.\S+)', (GS / f'{m}.lean').read_text(encoding='utf8'), re.M)]


def topo(mods):
    pos, out, seen = set(mods), [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in imports_of(m):
            if d in pos:
                visit(d)
        out.append(m)
    for m in mods:
        visit(m)
    return out


def extract(used_path):
    used = {}
    for l in open(used_path, encoding='utf8'):
        if l.strip():
            mod, name = l.split()
            used.setdefault(mod.split('.', 1)[1], set()).add(name.replace(fe.ROOT_NS + '.', ''))
    chunks = {}
    for mod in fe.SOURCES:
        keep = used.get(mod, set()) - EXCLUDE
        chunk, names = [], []
        for it in fe.parse((GS / f'{mod}.lean').read_text(encoding='utf8')):
            if it[0] == 'ctx':
                chunk.append(('ctx', it[1]))
            elif it[0] == 'decl' and it[1] not in EXCLUDE and (
                    it[1] in keep or any(u.startswith(it[1] + '.') for u in keep)):
                chunk.append(('decl', it[2]))
                names.append(it[1])
        missing = sorted(n for n in keep if n not in names and not any(n.startswith(x + '.') for x in names))
        if missing:
            print(f'WARNING {mod}: not found {missing}')
        if names:
            chunks[mod] = '\n\n'.join(t for _, t in fe.prune(chunk))
    return chunks


# ---------------------------------------------------------------- generated code

def ren181(t):
    def r(m):
        tok = m.group(0)
        tok = re.sub(r'JT(?=$|_)', 'JT3', tok)
        for a, b in (('tDegT2', 'tDegT3'), ('uDegT2', 'uDegT3'), ('classT2', 'classT3')):
            tok = tok.replace(a, b)
        return tok
    return re.sub(r"[A-Za-z_][A-Za-z0-9_']*", r, t)


def step181():
    s = (GS / 'Proofs18CoverFejerHeadlineJT.lean').read_text(encoding='utf8')
    a = s.index('/-- The envelope after one step (no threshold). -/')
    b = s.index('/-! The envelopes in dimensions `2, …, 14`, kernel-evaluated. -/')
    body = ren181(s[a:b]).rstrip() + '\n'
    assert 'JT ' not in body and 'T2' not in body.replace('.T2', ''), 'rename left a T2/JT token'
    return body


def fits(fn, lhs, ranges):
    """Kernel-evaluated ranges and the fits `lhs ≤ C·2^k` from `k0` on."""
    out = []
    for C, k0 in ranges:
        out.append(f'''theorem {fn}_small{C} {{k : Nat}} (h1 : {k0} ≤ k) (h2 : k ≤ 14) :
    {lhs} ≤ {C} * 2 ^ k := by
  interval_cases k <;> decide +kernel

theorem {fn}_fit{C} {{k : Nat}} (hk : {k0} ≤ k) : {lhs} ≤ {C} * 2 ^ k := by
  rcases Nat.lt_or_ge k 15 with h | h
  · exact {fn}_small{C} hk (by omega)
  · have := {fn}_le16 k h
    have h16 : 16 * 2 ^ k ≤ {C} * 2 ^ k := Nat.mul_le_mul_right _ (by norm_num)
    omega
''')
    return '\n'.join(out)


PRE = 'set_option autoImplicit false\nnoncomputable section\nopen scoped BigOperators\n'


def module(name, imports, doc, chunks, extra=''):
    parts = [f'import GowersSzemeredi.{i}' for i in imports]
    text = '\n'.join(parts) + '\n\n' + doc.strip() + '\n' + PRE
    for c in chunks:
        if 'open BaseCase' in c:
            body = c
        else:
            body = c
        text += '\nnamespace LeanProofs.GowersSzemeredi\n\n' + body.strip() + '\n\nend LeanProofs.GowersSzemeredi\n'
    if extra:
        text += '\nnamespace LeanProofs.GowersSzemeredi\n\n' + extra.strip() + '\n\nend LeanProofs.GowersSzemeredi\n'
    (GS / f'{name}.lean').write_text(text, encoding='utf8', newline='\n')
    print(f'{name}: {text.count(chr(10))} lines')


DOC_CLASSES = '''/-! **The final route, part 1: the class table** (Notes L.16-final).

The classes `tDegT3` of the two-track split (Notes L.16x/y) and their
polynomial covers (`polyCoverAt_classT3`), with the base envelope bounds of
the Fejér route (`Proofs18FejerEnvelopeBase`, Notes L.16): the declarations of
the class modules that the final route uses, in their original order
(extracted by `assemble_final.py`). -/'''

DOC_STEP = '''/-! **The final route, part 2: the joint-slice step at `tDegT3`** (Notes L.16-final).

The parameters `GenParamsJT3` of one single-piece inverse step over the classes
`tDegT3`, and the bounds on their density, exponents and thresholds
(Notes L.16q/y), extracted from the step modules (`assemble_final.py`). -/'''

DOC_ENV = '''/-! **The final route, part 3: the envelopes and their fits** (Notes L.16-final).

One step for each theorem over the single class table `tDegT3`:
* Theorem 18.1: `envStepJT3` and the envelope `polyGenMuJT3` (joint slices);
* Theorem 18.2: `envStepKTx3` and the envelope `genMuXK3` (joint slices,
  sharp partition constant).
Beyond dimension `14` the closed forms bound both envelopes by `16·2^k - 4k - 128`;
`decide +kernel` evaluates them below. Fits:
* `polyGenMuJT3 k + 1 ≤ 16·2^k, 32·2^k, 64·2^k` from `k = 9, 6, 2`;
* `genMuXK3 k + 2k + 22 ≤ 16·2^k, 32·2^k, 64·2^k, 128·2^k` from `k = 9, 7, 4, 2`.
With them, Theorem 16.2 and Corollary 16.11 with polynomial controls at
`tDegT3`. -/'''

DOC_FINAL = '''/-! **The final route** (Notes L.16-final).

All the final bounds from one structure of inputs, `FinalInputs`: recurrence
profiles with polynomial family constants, and a progression phase partition
(the corpus supplies both; see `Proofs18CoverFejerAllDegrees`). Over the class
table `tDegT3`:
* Theorem 18.1 with `d + 4` in every degree, `d + 3` for `d ≥ 8`, and
  `d + 2` for `d ≥ 11` (degrees `0, …, 3` from the corpus exponents and the
  polynomial base envelope);
* Theorem 18.2 with `L + 3` in every length, `L + 2` for `L ≥ 8`, `L + 1` for
  `L ≥ 11`, and `L + 0` for `L ≥ 13` (lengths `L ≤ 5` from the corpus's
  explicit thresholds). -/'''


FINAL = '''/-- **The inputs of the final route**: recurrence profiles with family constants
`Kc`, `pc` at most `2^(2^(4k+16))`, and a progression phase partition. -/
structure FinalInputs where
  Kc : Nat → Nat
  pc : Nat → Nat
  two_le_Kc : ∀ k, 2 ≤ Kc k
  pc_pos : ∀ k, 0 < pc k
  profile : ∀ k, 1 ≤ k →
    Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k))
  const : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))
  phase : ∃ (K : Real) (p : Nat), ProgressionPhasePartition K p ∧ 0 < p ∧ K ≤ 2 ^ p ∧
    (p : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)

namespace FinalInputs

variable (I : FinalInputs)
include I

/-- Theorem 18.1 at `d + c` for `d ≥ 4`, once the envelope fits `2^(c+2)·2^(d-2)`. -/
theorem theorem_18_1_of_fit {c d : Nat} (hd : 4 ≤ d)
    (hfit : polyGenMuJT3 (d - 2) + 1 ≤ 2 ^ (c + 2) * 2 ^ (d - 2)) : Theorem181AtSharp c d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
  have henv := polyEnvBound_allJT3 I.Kc I.pc I.two_le_Kc I.pc_pos I.profile I.const hpp hp hK hpB
    (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  rwa [show d + c = (c + 2) + (d - 2) by omega, pow_add]

/-- Theorem 18.2 at `L + c` for `L ≥ 6`, once the envelope fits `2^(c+4)·2^(L-4)`. -/
theorem theorem_18_2_of_fit {c L : Nat} (hL : 6 ≤ L)
    (hfit : genMuXK3 (L - 4) + 2 * (L - 4) + 22 ≤ 2 ^ (c + 4) * 2 ^ (L - 4)) :
    Theorem182AtSharp c L := by
  have henv := envBound_allXK3 I.Kc I.pc I.two_le_Kc I.pc_pos I.profile I.const (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXK3_ge (k := L - 4) (by omega)
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXK3 (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXK3 (L - 4))
    omega
  refine theorem182AtSharp_of_envBound (by omega) henv (by omega) hLμ ?_
  rw [show L + c = (c + 4) + (L - 4) by omega, pow_add]
  omega

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 2`.** -/
theorem theorem_18_1_d2 {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 2 d :=
  I.theorem_18_1_of_fit (by omega) (polyGenMuJT3_fit16 (by omega))

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 3`.** -/
theorem theorem_18_1_d3 {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 3 d :=
  I.theorem_18_1_of_fit (by omega) (polyGenMuJT3_fit32 (by omega))

/-- **Theorem 18.1 at every degree with `d + 4`.** -/
theorem theorem_18_1_d4 (d : Nat) : Theorem181AtSharp 4 d := by
  match d with
  | 0 => exact theorem_18_1_d4_degree_zero
  | 1 => exact theorem_18_1_d4_degree_one
  | 2 => exact theorem_18_1_d4_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
    exact theorem_18_1_d4_three_of_phase_partition hpp hp hK hpB
  | d + 4 => exact I.theorem_18_1_of_fit (by omega) (polyGenMuJT3_fit64 (by omega))

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 0`.** -/
theorem theorem_18_2_L0 {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 0 L :=
  I.theorem_18_2_of_fit (by omega) (genMuXK3_fit16 (by omega))

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 1`.** -/
theorem theorem_18_2_L1 {L : Nat} (hL : 11 ≤ L) : Theorem182AtSharp 1 L :=
  I.theorem_18_2_of_fit (by omega) (genMuXK3_fit32 (by omega))

/-- **Theorem 18.2 at every length `L ≥ 8` with `L + 2`.** -/
theorem theorem_18_2_L2 {L : Nat} (hL : 8 ≤ L) : Theorem182AtSharp 2 L :=
  I.theorem_18_2_of_fit (by omega) (genMuXK3_fit64 (by omega))

/-- **Theorem 18.2 at every length with `L + 3`.** -/
theorem theorem_18_2_L3 (L : Nat) : Theorem182AtSharp 3 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L3_le_five (by omega)
  · exact I.theorem_18_2_of_fit h (genMuXK3_fit128 (by omega))

end FinalInputs
'''


def main():
    chunks = extract(sys.argv[1])
    order = topo(fe.SOURCES)
    pos = {m: i for i, m in enumerate(order)}
    named = set(m for g in GROUPS.values() if g for m in g)
    GROUPS['Proofs18FinalStep'] = [m for m in order if m not in named]
    # every group's sources must come after the sources of the earlier groups
    seen = set()
    for g, mods in GROUPS.items():
        for m in mods:
            anc = [d for d in fe_ancestors(m) if d in pos]
            late = [d for d in anc if d not in seen and d not in mods]
            if late and m in chunks:
                print(f'ORDER {g}: {m} needs {late}')
        seen |= set(mods)

    def pick(g):
        return [chunks[m] for m in sorted(GROUPS[g], key=pos.get) if m in chunks]
    module('Proofs18FinalClasses', BASE, DOC_CLASSES, pick('Proofs18FinalClasses'))
    module('Proofs18FinalStep', ['Proofs18FinalClasses'], DOC_STEP, pick('Proofs18FinalStep'))
    env_extra = step181() + '\n' + fits('polyGenMuJT3', 'polyGenMuJT3 k + 1', [(16, 9), (32, 6), (64, 2)]) \
        + '\n' + fits('genMuXK3', 'genMuXK3 k + 2 * k + 22', [(32, 7), (64, 4), (128, 2)])
    module('Proofs18FinalEnvelopes', ['Proofs18FinalStep'], DOC_ENV, pick('Proofs18FinalEnvelopes'), env_extra)
    module('Proofs18Final', ['Proofs18FinalEnvelopes', 'Proofs18CoverHeadlineFrom'], DOC_FINAL,
           pick('Proofs18Final'), FINAL)


_anc = {}


def fe_ancestors(m):
    if m in _anc:
        return _anc[m]
    s = set()
    if (GS / f'{m}.lean').exists():
        for d in imports_of(m):
            s |= {d} | fe_ancestors(d)
    _anc[m] = s
    return s


if __name__ == '__main__':
    main()
