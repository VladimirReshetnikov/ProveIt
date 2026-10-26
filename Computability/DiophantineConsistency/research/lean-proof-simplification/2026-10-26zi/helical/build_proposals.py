from pathlib import Path
import difflib, json, hashlib
root=Path(__file__).resolve().parent.parent
src=root/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'
out=root/'helical/proposed'
prefix='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'

q=(src/'WangTiles942HelicalQuotient.lean').read_text()
a=q.index('  induction t using Int.induction_on')
b=q.index('\n/-- A generic integer periodic function',a)
qnew=q[:a]+'''  have hp : Function.Periodic (fun p : ℤ × ℤ => T p.1 p.2) (w, -1) := by
    rintro ⟨a,b⟩
    change T (a+w) (b+(-1)) = T a b
    simpa only [sub_eq_add_neg] using hhelix a b
  have h := hp.zsmul t (x,t)
  change T (x+t • w) (t+t • (-1 : ℤ)) = T x t at h
  simpa only [zsmul_eq_mul, mul_neg, mul_one, add_neg_cancel, mul_comm] using h.symm
''' + q[b:]
(out/'WangTiles942HelicalQuotient.lean').write_text(qnew)

c=(src/'WangTiles942CycleBand.lean').read_text()
a=c.index('/-- A halting actual blank run')
helper='''/-- The concrete quotient of the extended band has matching and retains every
canonical-band tile. Both the existential and uniquely marked endpoints use this
same descent proof; marker uniqueness is deliberately not a premise. -/
theorem band_quotient_properties (T L R H : ℕ) [NeZero H]
    [NeZero ((L+R)*H)]
    (hh : (DecimalMachine215.machine.run T).state = none)
    (hL : T+2 ≤ L) (hR : T+2 ≤ R) (hTH : T+2 ≤ H) (hH : 3 ≤ H)
    (hw : 0 < L+R) :
    let a := quotientWord (extend (band L H) (L+R) (L : ℤ))
      (extend_allowed (band L H) (L+R) hw (L : ℤ)
        (fun x _ t => band_allowed T L H hh hTH x t)) (L+R) H
    MarkedWord ((L+R)*H) (L+R : ℕ) a ∧
      ∀ x, -(L : ℤ) ≤ x → x < (R : ℤ) → ∀ t,
        tile (a (address ((L+R)*H) (L+R : ℕ) x t)) = band L H x t := by
  have hleft : ((L+R : ℕ) : ℤ)-(L : ℤ)-1 = (R : ℤ)-1 := by push_cast; ring
  rcases extension_properties (band L H) (L+R) H hw (L : ℤ) (by omega) (by omega)
      (fun x _ t => band_allowed T L H hh hTH x t)
      (fun x _ t => band_temporal L H hH x t)
      (fun x hx _ t => band_horizontal T L H hh hL x t hx)
      (by simpa only [hleft] using band_twisted T L R H hh hL hR)
      (fun x _ t => band_period L H x t) (band_start L H (by omega)) with
    ⟨_,hhoriz,htime,hs,hhel,hvert⟩
  refine ⟨quotientWord_marked _ _ _ _ hhoriz htime hs hhel hvert,?_⟩
  intro x hx0 hxR t
  apply (quotientWord_binding _ _ _ _ hhel hvert x t).trans
  apply extend_on_band (band L H) (L+R) hw (L : ℤ) x t
  unfold InBand
  push_cast
  omega

'''
cnew=c[:a]+helper+c[a:]
a=cnew.index('  have hw : 0 < L+R := by omega',cnew.index('theorem marked_word_of_halt'))
b=cnew.index('\nend DiophantineConsistency.WangTiles942CycleBand',a)
cnew=cnew[:a]+'''  have hp := band_quotient_properties T L R H hh hL hR hTH hH (by omega)
  exact ⟨_,hp.1,hp.2⟩
''' + cnew[b:]
(out/'WangTiles942CycleBand.lean').write_text(cnew)

m=(src/'WangTiles942BandMarker.lean').read_text()
a=m.index('  have hL0 :',m.index('theorem canonicalWord_properties'))
b=m.index('\n/-- An actual halting time',a)
mnew=m[:a]+'''  have hp := band_quotient_properties T L R H hh hL hR hTH hH hw
  exact ⟨hp.1,canonicalWord_marker_iff T L R H hh hTH (by omega) (by omega) hw,hp.2⟩
''' + m[b:]
(out/'WangTiles942BandMarker.lean').write_text(mnew)

for pid,files in [('H1',[('WangTiles942HelicalQuotient.lean',q,qnew)]),('H2',[('WangTiles942CycleBand.lean',c,cnew),('WangTiles942BandMarker.lean',m,mnew)])]:
    patch=''.join(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+prefix+name,tofile='b/'+prefix+name)) for name,a,b in files)
    (root/f'helical/patches/{pid}.patch').write_text(patch)

metrics=[]
for name,a,b in [('WangTiles942HelicalQuotient.lean',q,qnew),('WangTiles942CycleBand.lean',c,cnew),('WangTiles942BandMarker.lean',m,mnew)]:
    metrics.append(dict(file=name,original_lines=len(a.splitlines()),proposed_lines=len(b.splitlines()),delta_lines=len(b.splitlines())-len(a.splitlines()),original_sha256=hashlib.sha256(a.encode()).hexdigest(),proposed_sha256=hashlib.sha256(b.encode()).hexdigest()))
(root/'helical/metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
