#!/usr/bin/env python3
"""Create isolated scheduler overlays without changing the pinned checkout."""
from pathlib import Path
import argparse, difflib, hashlib, json, re, subprocess

ap = argparse.ArgumentParser()
ap.add_argument('--repo', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
args = ap.parse_args()
PIN='57541fe0cfe3af62b4cb58747d8d1d7c16b338d5'
assert subprocess.check_output(['git','-C',str(args.repo),'rev-parse','HEAD'],text=True).strip()==PIN,'unexpected repository revision'
prefix = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
dest = args.output / 'BusyBeaver/ZFC'
dest.mkdir(parents=True, exist_ok=True)

binding = '''private abbrev scheduler : CofinalScheduler.Dynamics St :=
  ⟨enumStep, run, fun _ => rfl, fun n s => by cases h : enumStep s <;> simp only [run, h]⟩

'''

def replace_theorem(text, name, new):
    pattern = re.compile(r'^theorem '+re.escape(name)+r'\b.*?(?=\n(?:theorem |/-- |/-! |def |end )|\Z)',re.M|re.S)
    out, n = pattern.subn(new.rstrip()+'\n',text,count=1)
    assert n == 1, name
    return out

metrics=[]
patches=[]
for name in ['EnumPerm','Enum222','EnumDom','Enum254']:
    path=args.repo/prefix/(name+'.lean')
    old=path.read_text()
    s=old.replace('\n\n/-!','\nimport BusyBeaver.ZFC.CofinalScheduler\n\n/-!',1)
    s=s.replace('/-! ## Soundness -/',binding+'/-! ## Soundness -/',1)
    assert 'private abbrev scheduler' in s
    inv='Inv (toW s)' if name=='EnumPerm' else 'Inv s'
    inv2="Inv (toW s')" if name=='EnumPerm' else "Inv s'"
    proof = '(fun s t hi ht => by change enumStep s = some t at ht; simpa only [ht] using step_sound hi)' if name=='EnumPerm' else '(fun _ _ hi ht => step_inv hi ht)'
    invariant='(fun s => Inv (toW s))' if name=='EnumPerm' else 'Inv'
    s=replace_theorem(s,'run_inv',f'''theorem run_inv : ∀ (n : Nat) {{s s' : St}}, {inv} → run n s = some s' → {inv2} :=
  fun n s s' => scheduler.run_invariant {invariant} {proof} n s s'
''')
    s=replace_theorem(s,'run_add','''theorem run_add : ∀ (n m : Nat) (s s1 : St), run n s = some s1 → run (n + m) s = run m s1 :=
  scheduler.run_add
''')
    if name=='EnumPerm':
        laws='''private theorem scheduler_laws : scheduler.Laws St.pl St.np where
  advance := by
    intro s t hs hp
    rw [(step_eq hs).2]
    simp only [fetch, hp, if_true]
  descend := by
    intro s t hs hp
    obtain ⟨h1, h2⟩ := step_eq hs
    have hd := decode_le (fetch s).1
    simp only [fetch, hp, if_false] at h1 h2 hd
    exact ⟨by omega, h2⟩

'''
        drain='''theorem drain : ∀ (m : Nat) (s : St), s.pl ≤ m →
    (∃ n s', run n s = some s' ∧ s'.pl = 0 ∧ s'.np = s.np) ∨ HaltsFrom s :=
  fun _ s _ => (scheduler.reach_or_halt scheduler_laws s.np s (Nat.le_refl _)).symm
'''
        reach='''theorem reach (sd : St) (hpl : sd.pl = 0) : ∀ k : Nat,
    (∃ n s, run n sd = some s ∧ s.pl = 0 ∧ s.np = sd.np + k) ∨ HaltsFrom sd := by
  intro k
  have _ := hpl
  exact (scheduler.reach_or_halt scheduler_laws (sd.np + k) sd (by omega)).symm
'''
    else:
        laws='''private theorem scheduler_laws : scheduler.Laws St.pl St.np where
  advance := fun _ _ hs hp => step_start hp hs
  descend := fun _ _ hs hp => step_pl hp hs

'''
        drain='''theorem drain : ∀ (m : Nat) (s : St), s.pl ≤ m →
    (∃ n s', run n s = some s' ∧ s'.pl = 0 ∧ s'.np = s.np) ∨
    (∃ n s', run n s = some s' ∧ enumStep s' = none) :=
  fun _ s _ => (scheduler.reach_or_halt scheduler_laws s.np s (Nat.le_refl _)).symm
'''
        reach='''theorem reach : ∀ N : Nat, (∃ n s, run n s0 = some s ∧ s.pl = 0 ∧ s.np = N) ∨ Halts :=
  fun N => (scheduler.reach_or_halt scheduler_laws N s0 (Nat.zero_le _)).symm
'''
    s=s.replace('/-- A candidate in progress finishes or the enumerator halts. -/',laws+'/-- A candidate in progress finishes or the enumerator halts. -/',1)
    s=replace_theorem(s,'drain',drain)
    s=replace_theorem(s,'reach',reach)
    if name=='EnumPerm':
        s=s.replace('/-- Completeness: between candidates, a derivation of code 1 is eventually run. -/',
          '/-- Completeness from every starting state, including an active candidate. -/')
        s=replace_theorem(s,'complete','''theorem complete_any {sd : St} (h : C222 F) : HaltsFrom sd := by
  obtain ⟨p, hp⟩ := build (cdom_of_c222 h)
  let cs := p ++ [.drop, .nip, .nip]
  apply scheduler.complete_at scheduler_laws sd (encL (.ax 0 1 sd.np) cs) (encL_ge sd.np cs)
  intro _ s _ hpl hnp
  have hf : (fetch s).1 = encL (.ax 0 1 sd.np) cs := by simp only [fetch, hpl, if_true, hnp]
  exact exec_list cs (.ax 0 1 sd.np) s hf (program_none sd.np p hp _)

theorem complete {sd : St} (hpl : sd.pl = 0) (h : C222 F) : HaltsFrom sd := by
  have _ := hpl
  exact complete_any h
''')
        s=s.replace('\nend SetTheory.BusyBeaver.ZFC.EnumPerm','''
/-- From any invariant state, including an active candidate, halting is refutability. -/
theorem halts_iff_any {s : St} (hs : Inv (toW s)) : HaltsFrom s ↔ C222 F :=
  ⟨sound hs, complete_any⟩

#print axioms complete_any
#print axioms halts_iff_any

end SetTheory.BusyBeaver.ZFC.EnumPerm''')
    (dest/(name+'.lean')).write_text(s)
    metrics.append({'module':name,'before_lines':len(old.splitlines()),'after_lines':len(s.splitlines()),
      'before_bytes':len(old.encode()),'after_bytes':len(s.encode()),'source_sha256':hashlib.sha256(old.encode()).hexdigest(),
      'overlay_sha256':hashlib.sha256(s.encode()).hexdigest()})
    patches.extend(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+str(prefix/(name+'.lean')),tofile='b/'+str(prefix/(name+'.lean'))))
(args.output.parent/'scheduler-clients.patch').write_text(''.join(patches))
core=dest/'CofinalScheduler.lean'
if core.exists():
    full=patches+list(difflib.unified_diff([],core.read_text().splitlines(True),fromfile='/dev/null',tofile='b/'+str(prefix/'CofinalScheduler.lean')))
    (args.output.parent/'scheduler-production.patch').write_text(''.join(full))
(args.output.parent/'source-metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
