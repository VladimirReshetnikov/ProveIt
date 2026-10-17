"""Write UsedRanges3.lean: the stub check's environment, rooted at the 25 final theorems AND at every
corpus name that the real-only bridge modules mention (they cannot be loaded locally; text is an
over-approximation, which is the safe direction for detaching).

usage: python -X utf8 gen_used3.py      (then build UsedRanges3.lean like the stub check)
Output of the Lean run: used_ranges3.txt, lines `Module Name startLine endLine`.
"""
import re
from pathlib import Path

SCR = Path(__file__).parent
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
stub = (SCR / 'StubFinal.lean').read_text(encoding='utf8')
cut = stub.rindex('open Lean Elab Command in\nrun_cmd do')
prelude = stub[:cut]
finals = re.findall(r'``(LeanProofs\.GowersSzemeredi\.[\w\'.]+)', stub[cut:].split('let final')[1].split(']')[0])
assert len(finals) == 25, len(finals)

REAL_ONLY = ['Proofs05ExplicitPartitionBounds', 'Proofs05ExplicitSchmidtRecurrence', 'Proofs05SchmidtRecurrence',
             'Proofs05SimultaneousMultiaffinePartition', 'Proofs05SimultaneousMultiaffineStep',
             'Proofs16ExplicitPhasePartition', 'Proofs16ExplicitRecurrenceProfiles',
             'Proofs16PolynomialRecurrenceProfile', 'Proofs16SimultaneousRecurrence', 'Proofs18CoverFejerAllDegrees']
toks = set()
for m in REAL_ONLY:
    t = (GS / f'{m}.lean').read_text(encoding='utf8')
    t = re.sub(r'--[^\n]*', ' ', re.sub(r'/-.*?-/', ' ', t, flags=re.S))
    toks |= set(re.findall(r"[A-Za-z_][\w'.₀-₉?!]*", t))
extra = sorted(x for x in toks if len(x) > 2)
names = ', '.join(f'"{x}"' for x in extra)
roots = ', '.join(f'`{x}' for x in finals)
cmd = f'''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let extraStr : List String := [{names}]
  let mut roots : List Name := [{roots}]
  for s in extraStr do
    let n := s.toName
    for c in [n, `LeanProofs.GowersSzemeredi ++ n, `LeanProofs.GowersSzemeredi.BaseCase ++ n] do
      if env.contains c then roots := c :: roots
  let mut seen : NameSet := {{}}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in ci.getUsedConstantsAsSet.toList do
        if !seen.contains m then stack := m :: stack
  let mut out : Array String := #[]
  for n in seen.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mn := env.header.moduleNames[idx.toNat]!
      if (`GowersSzemeredi).isPrefixOf mn then
        let r ← liftCoreM (findDeclarationRanges? n)
        match r with
        | some dr => out := out.push s!"{{mn}} {{n}} {{dr.range.pos.line}} {{dr.range.endPos.line}}"
        | none => out := out.push s!"{{mn}} {{n}} 0 0"
  IO.FS.writeFile "{(SCR / 'used_ranges3.txt').as_posix()}" (String.intercalate "\\n" out.toList)
  logInfo m!"{{roots.length}} roots, {{out.size}} project declarations used"

open Lean in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let isGS (i : Nat) : Bool := (mods[i]!).toString.startsWith "GowersSzemeredi"
  let lines : Array String := env.constants.map₁.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | none => acc
    | some i =>
      let mi := i.toNat
      if !isGS mi then acc else
        let used := ci.getUsedConstantsAsSet.toList
        let ms := used.filterMap fun u => match env.getModuleIdxFor? u with
          | some j => if j.toNat != mi && isGS j.toNat then some s!"{{mods[j.toNat]!}}:{{u}}" else none
          | none => none
        let same := used.filterMap fun u => match env.getModuleIdxFor? u with
          | some j => if j.toNat == mi then some u.toString else none
          | none => none
        acc.push s!"{{mods[mi]!}} {{n}} | {{" ".intercalate ms.eraseDups}} | {{" ".intercalate same}}"
  IO.FS.writeFile "{(SCR / 'decl_needs3.txt').as_posix()}" ("\\n".intercalate lines.toList ++ "\\n")
  logInfo m!"{{lines.size}} declarations"
'''
(SCR / 'UsedRanges3.lean').write_text(prelude + stub[cut:].rstrip('\n') + '\n' + cmd, encoding='utf8')
print(len(finals), 'final roots;', len(extra), 'candidate extra names')
