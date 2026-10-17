"""Family Lemmas 16.6 / 16.9 and the family piece cover: the abstract versions replace the concrete.

`Proofs16AbstractFamily` restated the family results of `Proofs16FamilyLemma6` …
`Proofs16FamilyPieceCover` over abstract members (frequency map `K`, linearity domains `A`,
functions `f`); the proofs never used Gowers's frame. The final route uses the abstract versions.
- the abstract Lemma 16.6 moves into `Proofs16FamilyLemma6`, and the concrete one is its instance
  (`K = section16LargeSpectrum`, `A` = the induced domain, `f = φ′`; the Bohr linearity is the
  induced selection);
- the concrete Lemma 16.9 and the concrete piece cover have no users: deleted, and with them
  `Proofs16FamilyLemma9`.
"""
from foldlib import Fold

F = Fold()
L6, L9, PC, AF = ('Proofs16FamilyLemma6', 'Proofs16FamilyLemma9', 'Proofs16FamilyPieceCover',
                  'Proofs16AbstractFamily')


def sub1(m, a, b):
    s = F.get(m)
    assert s.count(a) == 1, (m, s.count(a), a[:80])
    F.text[m] = s.replace(a, b)


moved = F.take(AF, 'AbstractFamilyLemma166At') + '\n' + F.take(AF, 'abstractFamilyLemma166At_of')
F.insert(L6, moved, 'allScaleFamilyLemma166At_of')
F.reprove(L6, 'allScaleFamilyLemma166At_of', ''' by
  unfold AllScaleFamilyLemma166At
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1 Gamma hML
    ι B phi H H1 Y phiPrime hfreq hH1 hselection P Q I hP hproduct hmP
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  obtain ⟨G, M, S, T, J, hGQ, hGm, hSP, hSpr, hSpd, hSw, hlin⟩ :=
    abstractFamilyLemma166At_of k hC hp hrec N m hk _ sigma hz hzHalf hs hs1 Qb Eb hQ ha ha1 Gamma
      hML ι H1 (fun c x => section16LargeSpectrum (B c) x (section16Delta (section16ThetaOne theta gamma k)))
      (fun c x => Finset.univ.filter fun y => (x, y) ∈ section16InducedDomain (B c) (H c) (Y c))
      phiPrime hfreq (fun c x hx v hv J hJ hd => by
        simpa only [Finset.inter_filter, Finset.inter_univ] using
          (hselection c).2 x (hH1 c hx) v hv J.step hd J rfl hJ)
      P Q I hP hproduct hmP
  refine ⟨G, M, S, T, J, hGQ, hGm, hSP, hSpr, hSpd, hSw, fun c u h hhG hhH hhT => ?_⟩
  simpa only [Finset.inter_filter, Finset.inter_univ] using hlin c u h hhG hhH hhT''')
sub1(L6, '''* `AllScaleFamilyLemma166At`, `allScaleFamilyLemma166At_of`.''',
     '''* `AbstractFamilyLemma166At`, `abstractFamilyLemma166At_of`: the same for
  abstract members (frequencies `K`, linearity domains `A`, functions `f`); the
  proof never uses Gowers's frame.
* `AllScaleFamilyLemma166At`, `allScaleFamilyLemma166At_of`: its instance at
  Gowers's data.''')

F.delete_decl(L9, 'AllScaleFamilyLemma169At')
F.delete_decl(L9, 'allScaleFamilyLemma169At_of')
F.delete_module(L9, ['Proofs16FamilyLemma6', 'Proofs16FamilyAffineLift'])

F.delete_decl(PC, 'section16_family_piece_large_box_profile')
F.delete_decl(PC, 'section16_family_piece_cover_with')
sub1(PC, '''* `card_biUnion_partialGraph_fiber_le`.
* `section16_family_piece_large_box_profile`,
  `section16_family_piece_cover_with`. -/''', '''* `card_biUnion_partialGraph_fiber_le`.

The assembly itself is stated for abstract members in
`Proofs16AbstractFamily` (`abstract_family_piece_large_box_profile`,
`abstract_family_piece_cover_with`). -/''')
sub1(AF, '''* `AbstractFamilyLemma166At`, `abstractFamilyLemma166At_of`.
''', '''* `AbstractFamilyLemma166At`, `abstractFamilyLemma166At_of`
  (`Proofs16FamilyLemma6`).
''')
F.commit()
