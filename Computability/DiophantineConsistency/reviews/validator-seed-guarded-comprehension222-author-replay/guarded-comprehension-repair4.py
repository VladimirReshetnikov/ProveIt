from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedGuardedComprehension222.lean')
s=p.read_text();a='    fin_cases i <;> rfl';b='    exact Fin.cases rfl (Fin.cases rfl Fin.elim0) i'
assert a in s;s=s.replace(a,b,1);p.write_text(s)
