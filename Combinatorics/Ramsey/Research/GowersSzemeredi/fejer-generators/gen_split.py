"""Split-class step at any (P, T): the printed and the Fejér split bounds as instances.

`Proofs16SplitStepFejer` copied the printed chain of `Proofs16SplitStepBounds` (basics, remainder
count, samples, count, width exponent) with the Fejér inputs, and generalized the width exponent to
two tracks. Here the Fejér proofs, with their inputs as hypotheses and the degrees `sw… P T`, are
stated once in `Proofs16SplitStepBounds`; the printed chain is the instance at `(stepP k, stepT k)`
(the width exponent on the diagonal `ac = ae`, `Dc = De`) and the Fejér chain at
`(fejerStepP k, fejerStepT k)`. Statements unchanged.
"""
import re

from foldlib import Fold

SB, SF = 'Proofs16SplitStepBounds', 'Proofs16SplitStepFejer'
F = Fold()


def sub1(t, a, b):
    assert t.count(a) == 1, (t.count(a), a[:100])
    return t.replace(a, b)


B = r"(?<![\w'.])"
E = r"(?![\w'])"
TERMS = [('classPiecesFejer gamma theta k', 'm'), ('classBudgetW (fejerThetaOne theta gamma k) k', 'tS'),
         ('section16Delta (fejerThetaOne theta gamma k)', 'gS'),
         ('tightZeta (fejerThetaOne theta gamma k / 4)', 'zeta'), ('fejerStepP k', 'P'), ('fejerStepT k', 'T')]
P_ONLY = ['StepY', 'QrW', 'SW', 'PbW', 'CountW', 'EbW', 'ErW', 'BqW', 'LW', 'PbW2', 'LW2']
P_T = ['ZW', 'ExpW', 'ExpW2']
NAMES = [('split_step_basics_fejer', 'split_step_basics_W'), ('split_Qr_le_fejer', 'split_Qr_le_W'),
         ('split_samples_le_fejer', 'split_samples_le_W'), ('split_count_le_fejer', 'split_count_le_W'),
         ('split_exp_inv_le_fejer2', 'split_exp_inv_le_W2')]
U = '(2 / (gamma * theta))'
H_BASIC = (f'(hm0 : (m : Real) ≤ {U} ^ P)\n    (hgd0 : 2 / (gamma * tS) ≤ {U} ^ (P + 1))\n'
           f'    (hdd0 : 2 / (gS * tS) ≤ {U} ^ (P + 1))')


def generalize(t):
    for a, b in TERMS:
        t = re.sub(B + re.escape(a) + E, b, t)
    for x in P_ONLY:
        t = re.sub(B + 'fs' + x + r' k' + E, f'sw{x} P k', t)
    for x in P_T:
        t = re.sub(B + 'fs' + x + r' k' + E, f'sw{x} P T k', t)
    for x in P_ONLY + P_T:
        t = re.sub(B + 'fs' + x + E, 'sw' + x, t)
    for a, b in NAMES:
        t = re.sub(B + re.escape(a) + E, b, t)
    t = t.replace('split_step_basics_W (k := k) hV hVV hg hg1 ht ht1 hr hr1 n',
                  'split_step_basics_W hV hVV hg hg1 ht ht1 hr hr1 n hm0 hgd0 hdd0')
    t = re.sub(r'(split_Qr_le_W \(k := k\) \S+ \S+ hV hVV hg hg1 ht ht1 hr hr1 n)',
               r'\1 hm0 hgd0 hdd0 hb hPk', t)
    t = re.sub(r'(split_samples_le_W \(k := k\) \S+ \S+ hV hVV hg hg1 ht ht1 hr hr1 n)',
               r'\1 hm0 hgd0 hdd0 hb hb1 hPk', t)
    drop = [r'  have hm := classPiecesFejer_le_gen k hg hg1 ht ht1\n',
            r'  have hgd := twoDiv_gamma_le_fejer k hg hg1 ht ht1\n',
            r'  have hdd := twoDiv_delta_le_fejer k hg hg1 ht ht1\n',
            r'  obtain ⟨hb, -⟩ := classBudgetW_pos_le k \(fejerThetaOne_bounds[^\n]*\n',
            r'  obtain ⟨hb, hb1⟩ := classBudgetW_pos_le k \(fejerThetaOne_bounds[^\n]*\n',
            r'  obtain ⟨-, -, hd\', hd1\'⟩ := section16_theta_delta_bounds_with[^\n]*\n',
            r'  have hd : 0 < gS := hd\'\n', r'  have hd1 : gS ≤ 1 := hd1\'\n',
            r'  have hPk := fejerStepP_ge k\n', r'  set tS := tS\n', r'  set P := P with hPdef\n',
            r'\s*rw \[← hPdef\]\n']
    for d in drop:
        t = re.sub(d, lambda mm: '\n' if mm.group(0).startswith('\n') else '', t)
    t = t.replace('  obtain ⟨hz0, hz1, hzi⟩ := tightZeta_fejer_inv_le_gen k hg hg1 ht ht1\n',
                  '  obtain ⟨hz0, hz1, hzi⟩ := hz\n')
    t = t.replace(', ← hPdef', '').replace('← hPdef, ', '')
    assert 'Fejer' not in re.sub(r'/-.*?-/', '', t, flags=re.S).replace('fejerThetaOne', ''), 'Fejér left'
    assert 'hPdef' not in t and 'fejer' not in re.sub(r'/-.*?-/', '', t, flags=re.S)
    return t


DEGS = '''/-! ### The split degrees at any `(P, T)`

The printed split degrees `s…W` are these at `(stepP k, stepT k)`, the Fejér ones
`fs…W` (`Proofs16SplitStepFejer`) at `(fejerStepP k, fejerStepT k)`, both by `rfl`;
the two-track degrees `sw…2` reduce to the one-track ones on the diagonal. -/

def swStepY (P k a D : Nat) : Nat := a * (P + 1) + D * (P + k + 6)
def swQrW (P k a D : Nat) : Nat := swStepY P k a D * 2 ^ k
def swSW (P k a D : Nat) : Nat := swQrW P k a D + P + 8
def swPbW (P k a D : Nat) : Nat := a * (P + swSW P k a D + 1) + D * (P + 5)
def swCountW (P k a D : Nat) : Nat := P + 1 + 2 * swSW P k a D + 2 * swPbW P k a D
def swEbW (P k a D : Nat) : Nat := a * (P + 1) + D * (P + 6)
def swErW (P k a D : Nat) : Nat := (swStepY P k a D + 4) * 2 ^ k
def swBqW (P k a D : Nat) : Nat := 4 + (swEbW P k a D + 1) * 2 ^ (k + 2)
def swLW (P k a D : Nat) : Nat := swBqW P k a D + (swErW P k a D + swEbW P k a D)
def swZW (P T k a D : Nat) : Nat := T + a + swEbW P k a D + 7
def swPbW2 (P k ac Dc ae De : Nat) : Nat := ae * (P + swSW P k ac Dc + 1) + De * (P + 5)
def swLW2 (P k ac Dc ae De : Nat) : Nat := swBqW P k ac Dc + (swErW P k ae De + swEbW P k ae De)
def swExpW2 (P T k ac Dc ae De : Nat) : Nat :=
  swZW P T k ac Dc + swLW2 P k ac Dc ae De + swPbW2 P k ac Dc ae De + 6

'''

# --- the generic chain, from the Fejér proofs
gen = {}
for old, new in NAMES:
    blk = F.take(SF, old)
    gen[new] = generalize(blk)

g = gen['split_step_basics_W']
g = sub1(g, 'theorem split_step_basics_W {k : Nat} {V V\' : Real}', 'theorem split_step_basics_W {P m : Nat} {tS gS V V\' : Real}')
g = sub1(g, '    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :\n',
         f'    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)\n    (hm : (m : Real) ≤ {U} ^ P) (hgd : 2 / (gamma * tS) ≤ {U} ^ (P + 1))\n'
         f'    (hdd : 2 / (gS * tS) ≤ {U} ^ (P + 1)) :\n')
gen['split_step_basics_W'] = g

for nm, extra in (('split_Qr_le_W', ' (hb : 0 < tS) (hPk : k + 8 ≤ P)'),
                  ('split_samples_le_W', ' (hb : 0 < tS) (hb1 : tS ≤ 1) (hPk : k + 8 ≤ P)'),
                  ('split_count_le_W', ' (hb : 0 < tS) (hb1 : tS ≤ 1) (hPk : k + 8 ≤ P)')):
    g = gen[nm]
    g = sub1(g, f'theorem {nm} {{k a D : Nat}}', f'theorem {nm} {{k a D P m : Nat}} {{tS gS : Real}}')
    g = sub1(g, '(ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :\n',
             f'(ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)\n    {H_BASIC}{extra} :\n')
    gen[nm] = g

g = gen['split_exp_inv_le_W2']
g = sub1(g, 'theorem split_exp_inv_le_W2 {k ac Dc ae De : Nat}', 'theorem split_exp_inv_le_W2 {k ac Dc ae De P T m : Nat}\n    {tS gS zeta : Real}')
g = sub1(g, '    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :\n'
            '    let M := n * m\n    let tS := tS\n    let gS := gS\n',
         f'    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat)\n    {H_BASIC}\n'
         '    (hb : 0 < tS) (hb1 : tS ≤ 1) (hd : 0 < gS) (hd1 : gS ≤ 1)\n'
         f'    (hz : 0 < zeta ∧ zeta ≤ 1 ∧ zeta⁻¹ ≤ Real.exp ({U} ^ T)) (hPk : k + 8 ≤ P) :\n'
         '    let M := n * m\n')
g = sub1(g, '  intro M tS gS e\n', '  intro M e\n')
gen['split_exp_inv_le_W2'] = g

# --- place the generic chain in front of the printed one, with the degrees
s = F.get(SB)
for nm, anchor in (('split_step_basics_W', 'split_step_basics'), ('split_Qr_le_W', 'split_Qr_le'),
                   ('split_samples_le_W', 'split_samples_le'), ('split_count_le_W', 'split_count_le')):
    F.insert(SB, gen[nm], anchor)
n2 = ''.join(F.take(SF, x) for x in ('sPbN2', 'sLN2', 'sExpN2'))
F.insert(SB, n2 + '\n' + gen['split_exp_inv_le_W2'], 'split_exp_inv_le')
s = F.get(SB)
F.text[SB] = sub1(s, '/-! ### Shared facts of the step -/\n', DEGS + '/-! ### Shared facts of the step -/\n')

# --- printed instances
PIN = 'classPieces_le_stepP k hg hg1 ht ht1) (twoDiv_gamma_le k hg hg1 ht ht1)\n    (twoDiv_delta_le k hg hg1 ht ht1)'
F.reprove(SB, 'split_step_basics', f'\n  split_step_basics_W hV hVV hg hg1 ht ht1 hr hr1 n ({PIN}')
F.reprove(SB, 'split_Qr_le', f'\n  split_Qr_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := stepP k) ({PIN}\n'
          '    (classBudget_pos_le k ht ht1 hg hg1).1 (stepP_ge k)')
for nm in ('split_samples_le', 'split_count_le'):
    F.reprove(SB, nm, f'\n  have hb := classBudget_pos_le k ht ht1 hg hg1\n'
              f'  {nm}_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := stepP k) ({PIN} hb.1 hb.2\n'
              '    (stepP_ge k)')
F.reprove(SB, 'split_exp_inv_le', f'''
  have hb := classBudget_pos_le k ht ht1 hg hg1
  have hd := section16_theta_delta_bounds k ht ht1 hg hg1
  split_exp_inv_le_W2 ha hD ha hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n (P := stepP k)
    (T := stepT k) ({PIN} hb.1 hb.2 hd.2.2.1 hd.2.2.2
    (section16Zeta_inv_le_gen k hg ht) (stepP_ge k)''')

# --- Fejér instances: re-add the five theorems in front of `split_exp_inv_le_fejer`
FIN = ('classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)\n'
       '    (twoDiv_delta_le_fejer k hg hg1 ht ht1)')
HF = '  have hf := fejerThetaOne_bounds k ht ht1 hg hg1\n  have hb := classBudgetW_pos_le k hf.1 hf.2\n'
orig = {}
src = (F.get(SF))
import foldlib
tmp = foldlib.Fold()
fs_head = tmp.get(SF)
blocks = foldlib.blocks(fs_head)
for old, _ in NAMES:
    st, en = blocks[old]
    orig[old] = fs_head[st:en]
inst = {}
inst['split_step_basics_fejer'] = f'\n  split_step_basics_W hV hVV hg hg1 ht ht1 hr hr1 n ({FIN}'
inst['split_Qr_le_fejer'] = (f' by\n{HF}  exact split_Qr_le_W ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k) ({FIN}\n'
                             '    hb.1 (by have := fejerStepP_ge k; omega)')
for nm in ('split_samples_le_fejer', 'split_count_le_fejer'):
    inst[nm] = (f' by\n{HF}  exact {nm.replace("_fejer", "_W")} ha hD hV hVV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k)\n'
                f'    ({FIN} hb.1 hb.2 (by have := fejerStepP_ge k; omega)')
inst['split_exp_inv_le_fejer2'] = (f' by\n{HF}  have hd := section16_theta_delta_bounds_with hf.1 hf.2\n'
                                   '  exact split_exp_inv_le_W2 hac hDc hae hDe hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n\n'
                                   f'    (P := fejerStepP k) (T := fejerStepT k) ({FIN} hb.1 hb.2 hd.2.2.1 hd.2.2.2\n'
                                   '    (tightZeta_fejer_inv_le_gen k hg hg1 ht ht1) (by have := fejerStepP_ge k; omega)')
add = ''
for old, _ in NAMES:
    o = orig[old]
    j = o.index(':= by')
    add += o[:j] + ':=' + inst[old].lstrip(' ') if inst[old].startswith('\n') else o[:j] + ':=' + inst[old]
    add += '\n\n'
F.insert(SF, add, 'split_exp_inv_le_fejer')
F.commit()
