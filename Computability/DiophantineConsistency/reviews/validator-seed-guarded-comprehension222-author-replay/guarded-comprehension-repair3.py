from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedGuardedComprehension222.lean')
s=p.read_text()
a="  have h' : Source V ⊢! ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0)"
b="""  have hv : (fun i : Fin 2 => (⌜(![#0,#0] i : SyntacticSemiterm ℒₛₑₜ 1)⌝ :
      Semiterm V ℒₛₑₜ 1)) = ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0] := by
    funext i
    fin_cases i <;> rfl
  have h' : Source V ⊢! ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0)"""
assert a in s;s=s.replace(a,b,1)
a='memTerm,FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail] using h'
b='memTerm,FirstOrder.Semiformula.quote_def,hv] using h'
assert a in s;s=s.replace(a,b,1)
a="""  have h : Γ ⊢[Source V] memTerm z c.shift 🡘
      (eqTerm z B.shift ⋎ (eqTerm z t.shift ⋎ (memTerm z B.shift ⋏ θ.shift.subst ![z]))) := by
    unfold twoProperty at hc'
    cl_prover 96 [hc',hb,ht',hs]"""
b="""  have hback : Γ ⊢[Source V]
      (eqTerm z B.shift ⋎ (eqTerm z t.shift ⋎ (memTerm z B.shift ⋏ θ.shift.subst ![z]))) 🡒
        memTerm z c.shift :=
    left_A!_intro hb (left_A!_intro ht' (CK!_iff_CC!.mpr hs))
  have h : Γ ⊢[Source V] memTerm z c.shift 🡘
      (eqTerm z B.shift ⋎ (eqTerm z t.shift ⋎ (memTerm z B.shift ⋏ θ.shift.subst ![z]))) := by
    apply E!_intro
    · simpa only [twoProperty] using hc'
    · exact hback"""
assert a in s;s=s.replace(a,b,1)
p.write_text(s)
