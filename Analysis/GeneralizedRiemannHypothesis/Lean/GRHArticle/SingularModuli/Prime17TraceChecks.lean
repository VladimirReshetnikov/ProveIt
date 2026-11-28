import GRHArticle.SingularModuli.Prime17TraceChecks0_2
import GRHArticle.SingularModuli.Prime17TraceChecks3_5
import GRHArticle.SingularModuli.Prime17TraceChecks6_8
import GRHArticle.SingularModuli.Prime17TraceChecks9_11
import GRHArticle.SingularModuli.Prime17TraceChecks12_14
import GRHArticle.SingularModuli.Prime17TraceChecks15_17

namespace GRHArticle.SingularModuli.Prime17Data

theorem trace_checks : ∀ k ≤ 17, TraceCheck k := by
  have h : ∀ i : Fin 18, TraceCheck (i : ℕ) := by
    intro i
    fin_cases i
    · exact traceCheck0
    · exact traceCheck1
    · exact traceCheck2
    · exact traceCheck3
    · exact traceCheck4
    · exact traceCheck5
    · exact traceCheck6
    · exact traceCheck7
    · exact traceCheck8
    · exact traceCheck9
    · exact traceCheck10
    · exact traceCheck11
    · exact traceCheck12
    · exact traceCheck13
    · exact traceCheck14
    · exact traceCheck15
    · exact traceCheck16
    · exact traceCheck17
  exact fun k hk ↦ h ⟨k, Nat.lt_succ_of_le hk⟩

end GRHArticle.SingularModuli.Prime17Data
