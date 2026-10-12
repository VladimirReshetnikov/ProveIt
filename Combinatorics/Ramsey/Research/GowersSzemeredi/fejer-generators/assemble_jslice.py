"""Proofs16JointSliceCell: the line-cell lemma with the two anchor slices covered jointly (Notes L.16q)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16SinglePieceSections.lean').read_text(encoding='utf-8')
a = s.index('theorem single_piece_on_line_cell_of_slices')
b = s.index('/-- **One multilinear piece on a line-covered cell**, from the dimension-`k`')
body = s[a:b]


def sub(t, pairs):
    for x, y in pairs:
        assert t.count(x) == 1, ('count', t.count(x), x[:100])
        t = t.replace(x, y)
    return t


body = sub(body, [
    ('theorem single_piece_on_line_cell_of_slices {k q : Nat} (hk : 0 < k)\n    {c : Real → Real} {w : Real → Nat → Nat}\n'
     '    (hc : ∀ t, 0 < t → t ≤ 1 → 0 < c t ∧ c t ≤ 1) (hw : ∀ t, Monotone (w t))\n',
     'theorem single_piece_on_line_cell_of_joint_slices {k q : Nat} (hk : 0 < k)\n    {Qb Eb : Real → Real}\n'
     '    (hQ : ∀ t, 0 < t → t ≤ 1 → 1 ≤ Qb t) (hE : ∀ t, 0 < t → t ≤ 1 → 0 ≤ Eb t)\n'),
    ('    (hsl : ∀ x ∈ J.carrier, LocalPieceFor c w (Dom x) (fun h => phi (h, x)))\n',
     '    (hsl : ∀ x ∈ J.carrier, MultiplyLinearWith Qb Eb (partialGraph (Dom x) (fun h => phi (h, x))))\n'),
    ('    (hwidth : 2 ≤ w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width)) :\n',
     '    (hwidth : 2 ≤ jointSliceWidth Eb theta q T.width) :\n'),
    ('      Nat.sqrt (w (c (singlePieceTheta theta q)) (w (singlePieceTheta theta q) T.width) - 1) - 1\n        ≤ S.width ∧\n',
     '      Nat.sqrt (jointSliceWidth Eb theta q T.width - 1) - 1 ≤ S.width ∧\n'),
    ('      singlePieceDensity c theta q * S.carrier.card ≤\n        (D.filter fun p =>',
     '      jointSliceDensity Qb theta q * S.carrier.card ≤\n        (D.filter fun p =>'),
])
# step 3: the two anchor slices, jointly
i = body.index('  -- 3. the cross-section at `a`, then at `b`')
j = body.index('  -- 4. reconstruction on the doubly agreeing fibres')
STEP3 = '''  -- 3. the cross-sections at `a` and `b`, covered jointly at `θ₁/4`
  have hab : a ≠ b := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by
      have : (0 : Real) < W.card := lt_of_lt_of_le (by positivity) hWc
      exact_mod_cast this : 0 < W.card)
    exact (Finset.mem_filter.mp hp).2.1
  have hρ0 : 0 < θ1 / 4 := by positivity
  have hρ1 : θ1 / 4 ≤ 1 := by linarith
  have hcovs : ∀ e ∈ ({a, b} : Finset (ZMod N)),
      MultiplyLinearWith ((fun _ => Qb) e) ((fun _ => Eb) e)
        (partialGraph (Dom e) ((fun x h => phi (h, x)) e)) := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hsl _ ha
    · rw [Finset.mem_singleton.mp he]; exact hsl _ hb
  have hJC := joint_cover_on (ι := ZMod N) Dom (fun x h => phi (h, x)) (fun _ => Qb) (fun _ => Eb)
    (fun _ => θ1 / 4) {a, b} hcovs
    (fun _ _ => ⟨hρ0, hρ1⟩) (fun _ _ => (zero_le_one.trans (hQ _ hρ0 hρ1)))
    (fun _ _ => hE _ hρ0 hρ1) T hT
  rw [Finset.sum_pair hab, Finset.prod_pair hab, Finset.prod_pair hab] at hJC
  obtain ⟨R2, nu, hR2, hR2T, hR2w, hnu, hR2c⟩ := hJC.piece (theta := θ1) (by linarith) H1
    (Finset.filter_subset _ _)
    (fun e he h hh => by
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hDom _ (hslice h hh).1
      · rw [Finset.mem_singleton.mp he]; exact hDom _ (hslice h hh).2)
    hH1 hTne
  set mua := nu a with hmuadef
  set mub := nu b with hmubdef
  have hmua : IsMultilinear mua := hnu a (Finset.mem_insert_self _ _)
  have hmub : IsMultilinear mub := hnu b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  set H3 := H1.filter fun x => x ∈ R2.carrier ∧ ∀ e ∈ ({a, b} : Finset (ZMod N)), phi (x, e) = nu e x
    with hH3def
  set dR := (θ1 - (θ1 / 4 + θ1 / 4)) / (Qb (θ1 / 4) * Qb (θ1 / 4)) with hdRdef
  have hQ1 := hQ _ hρ0 hρ1
  have hdR0 : 0 < dR := by rw [hdRdef]; apply div_pos (by linarith); nlinarith
  have hR2width : jointSliceWidth Eb theta q T.width ≤ R2.width := by
    unfold jointSliceWidth
    rw [← hθ1def]
    exact Nat.ceil_le.mpr hR2w
  have hR2two : 2 ≤ R2.width := hwidth.trans hR2width
'''
body = body[:i] + STEP3 + body[j:]
body = sub(body, [
    ('''    obtain ⟨hpW, hpH3⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpH2, -, hb'⟩ := Finset.mem_filter.mp hpH3
    obtain ⟨-, -, ha'⟩ := Finset.mem_filter.mp hpH2
    have hne : a ≠ b := (Finset.mem_filter.mp hpW).2.1
''', '''    obtain ⟨hpW, hpH3⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, hall⟩ := Finset.mem_filter.mp hpH3
    have ha' := hall a (Finset.mem_insert_self _ _)
    have hb' := hall b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hne : a ≠ b := (Finset.mem_filter.mp hpW).2.1
'''),
    ('''  have hGcard : c (c θ1) * R2.carrier.card * (θ1 * J.carrier.card) ≤ G.card := by
    have h := fibre_sum_ge W H3 (s := θ1 * J.carrier.card) fun h hh =>
      (Finset.mem_filter.mp (Finset.filter_subset _ _ (Finset.filter_subset _ _ hh))).2''',
     '''  have hR2c' : dR * R2.carrier.card ≤ H3.card := by
    rw [hH3def]; convert hR2c using 3 <;> (ext x; simp only [Finset.mem_filter])
  have hGcard : dR * R2.carrier.card * (θ1 * J.carrier.card) ≤ G.card := by
    have h := fibre_sum_ge W H3 (s := θ1 * J.carrier.card) fun h hh =>
      (Finset.mem_filter.mp (Finset.filter_subset _ _ hh)).2'''),
    ('    exact (mul_le_mul_of_nonneg_right hR2c (by positivity)).trans h\n',
     '    exact (mul_le_mul_of_nonneg_right hR2c\' (by positivity)).trans h\n'),
    ('    R2.axis_carrier_subset_of_carrier_subset T hR2ne (hR2R1.trans hR1T) i\n',
     '    R2.axis_carrier_subset_of_carrier_subset T hR2ne hR2T i\n'),
    ('''    have hc2pos := (hc (c θ1) hcpos hcle).1
    have hGpos : 0 < G.card := by
      have : (0 : Real) < G.card :=
        lt_of_lt_of_le (mul_pos (mul_pos hc2pos hRpos) (mul_pos hθ1pos hJpos)) hGcard''',
     '''    have hGpos : 0 < G.card := by
      have : (0 : Real) < G.card :=
        lt_of_lt_of_le (mul_pos (mul_pos hdR0 hRpos) (mul_pos hθ1pos hJpos)) hGcard'''),
    ('''  have hle : ∑ j, singlePieceDensity c theta q * (S j).carrier.card ≤ ∑ j, ((Gj j).card : Real) := by
    rw [← Finset.mul_sum, hSsum, hGsum]
    calc singlePieceDensity c theta q * (R2.carrier.card * J.carrier.card) =
        c (c θ1) * R2.carrier.card * (θ1 * J.carrier.card) := by
          rw [singlePieceDensity, ← hθ1def]; ring''',
     '''  have hle : ∑ j, jointSliceDensity Qb theta q * (S j).carrier.card ≤ ∑ j, ((Gj j).card : Real) := by
    rw [← Finset.mul_sum, hSsum, hGsum]
    calc jointSliceDensity Qb theta q * (R2.carrier.card * J.carrier.card) =
        dR * R2.carrier.card * (θ1 * J.carrier.card) := by
          rw [jointSliceDensity, ← hθ1def, hdRdef]; ring'''),
    ('  refine ⟨S j, R2, I j, mu, (hSprop j).1, hSprod j, hR2R1.trans hR1T, ?_, ?_, hmu, ?_⟩\n',
     '  refine ⟨S j, R2, I j, mu, (hSprop j).1, hSprod j, hR2T, ?_, ?_, hmu, ?_⟩\n'),
    ('    exact ⟨hR1T (hR2R1 hx\'.1), hx\'.2⟩\n', '    exact ⟨hR2T hx\'.1, hx\'.2⟩\n'),
    ('''have hsq : Nat.sqrt (w (c θ1) (w θ1 T.width) - 1) ≤ v :=''',
     '''have hsq : Nat.sqrt (jointSliceWidth Eb theta q T.width - 1) ≤ v :='''),
])
HEAD = '''import GowersSzemeredi.Proofs16SinglePieceSections
import GowersSzemeredi.Proofs16JointCovers

/-! **Joint slices: the line-cell lemma with the two anchor sections covered
together** (Notes L.16q).

`single_piece_on_line_cell_of_slices` applies the dimension-`k` provider to
the cross-section `φ(·, a)`, and then to `φ(·, b)` inside the first agreement
set. The second application works at the density `c(θ₁)` that the first one
left, so the density is `θ₁·c(c(θ₁))` and the `t`-degrees of the slice
control multiply. Here the two cross-sections are given by covers
(`MultiplyLinearWith Qb Eb`). `joint_cover_on` composes them at the common
precision `θ₁/4`, and one pigeonhole (`JointCoverOn.piece`) gives one box
carrying both maps:
* density `jointSliceDensity Qb θ q = θ₁·(θ₁/2)/Qb(θ₁/4)²`: the degrees add;
* width `jointSliceWidth Eb θ q L = ⌈L^(Eb(θ₁/4)²)⌉`.

Steps 1, 2, 4 and 5 are those of `single_piece_on_line_cell_of_slices`
verbatim (generated by `assemble_jslice.py`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The density of the joint-slice step: `θ₁·(θ₁/2)/Qb(θ₁/4)²`, `θ₁ = θ³/(4q²)`. -/
def jointSliceDensity (Qb : Real → Real) (theta : Real) (q : Nat) : Real :=
  singlePieceTheta theta q *
    ((singlePieceTheta theta q - (singlePieceTheta theta q / 4 + singlePieceTheta theta q / 4)) /
      (Qb (singlePieceTheta theta q / 4) * Qb (singlePieceTheta theta q / 4)))

/-- The width of the joint-slice step: `⌈L^(Eb(θ₁/4)²)⌉`. -/
def jointSliceWidth (Eb : Real → Real) (theta : Real) (q L : Nat) : Nat :=
  ⌈(L : Real) ^ (Eb (singlePieceTheta theta q / 4) * Eb (singlePieceTheta theta q / 4))⌉₊

/-- **One multilinear piece on a line-covered cell, from jointly covered
anchor slices.** -/
'''
out = HEAD + body + 'end LeanProofs.GowersSzemeredi\n'
(GS / 'Proofs16JointSliceCell.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
