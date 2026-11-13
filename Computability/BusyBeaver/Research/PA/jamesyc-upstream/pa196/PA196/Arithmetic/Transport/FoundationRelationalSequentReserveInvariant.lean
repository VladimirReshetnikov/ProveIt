module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentAllocator
public import PA196.Arithmetic.Transport.CertificateInterface
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Exact paired certificate relation and explicit full-PA invariant for
changing only the source translator reserve, under both coverage guards. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateEquivalence

attribute [local irreducible] parametersGraph translateGraph biGraph
noncomputable def reserveGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “forward backward p b f lo z other. ∃ param target a aa,
    !parametersGraph param b f lo z ∧ !parametersGraph target b f lo other ∧
    !translateGraph a param p ∧ !translateGraph aa target p ∧ !biGraph forward backward a aa”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reserve_graph (forward backward p b f lo z other : V) :
    reserveGraph.val.Evalb ![forward,backward,p,b,f,lo,z,other] ↔
      BiCertificates forward backward (translate (parameters b f lo z) p)
        (translate (parameters b f lo other) p) := by
  simp [reserveGraph,parameters_graph,translate_graph,bi_graph,Matrix.comp_vecCons'']

attribute [local irreducible] reserveGraph coverageGraph
noncomputable def reserveInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, ∀ b f lo z other, !coverageGraph b f lo z p → !coverageGraph b f lo other p →
    ∃ forward backward, !reserveGraph forward backward p b f lo z other”

theorem reserve_invariant (n : V) : reserveInvariant.Evalb ![n] ↔
    ∀ p<n, ∀ b f lo z other : V, FormulaCovered b f lo z p → FormulaCovered b f lo other p →
      ∃ forward backward, BiCertificates forward backward (translate (parameters b f lo z) p)
        (translate (parameters b f lo other) p) := by
  simp [reserveInvariant,coverage_graph,reserve_graph,Matrix.comp_vecCons'']

theorem reserve_atom_certificates (b f lo z other k r ts : V)
    (hat : ∃ out, AtomTranslation out k r ts b f lo z)
    (henv' : EnvironmentsValid b f lo other) [V↓[ℒₒᵣ] ⊧* theory] :
    ∃ forward backward, BiCertificates forward backward
      (totalAtom (parameters b f lo z) k r ts) (totalAtom (parameters b f lo other) k r ts) := by
  obtain ⟨out,hat⟩ := hat
  have hout := totalAtom_agrees hat
  obtain ⟨hk,hlen,henv,a,d,ha,hd,hhead⟩ := hat
  have hnew : totalAtom (parameters b f lo other) k r ts=totalHead r a d other := by
    simp only [totalAtom,parameters_bound,parameters_free,parameters_reserve]
    rw [←totalLabel_agrees ha,←totalLabel_agrees hd]
  rw [←hout,hnew]
  rcases hhead with ⟨rfl,he⟩ | ⟨rfl,he⟩
  · rw [he]
    simp only [totalHead,ite_true]
    let h : BiWitness (ActualArithmeticGraph.eval neighborhoodExpr a d z 0)
      (ActualArithmeticGraph.eval neighborhoodExpr a d other 0) :=
      ⟨neighborhoodBinderChange a d z other (Ne.symm (label_reserved ha henv))
        (Ne.symm (label_reserved hd henv)) (Ne.symm (label_reserved ha henv'))
        (Ne.symm (label_reserved hd henv')),
       neighborhoodBinderChange a d other z (Ne.symm (label_reserved ha henv'))
        (Ne.symm (label_reserved hd henv')) (Ne.symm (label_reserved ha henv))
        (Ne.symm (label_reserved hd henv))⟩
    exact ⟨_,_,h.accepted⟩
  · rw [he]
    simp only [totalHead,Arithmetic.one_ne_zero,ite_false,ite_true]
    have heq : ActualArithmeticGraph.eval membershipExpr a d z 0=
        ActualArithmeticGraph.eval membershipExpr a d other 0 := rfl
    rw [heq]
    exact ⟨_,_,(BiWitness.refl _).accepted⟩

#print axioms reserve_graph
#print axioms reserve_invariant
#print axioms reserve_atom_certificates
end PA196.Arithmetic.Transport.RelationalSource.Numeric

