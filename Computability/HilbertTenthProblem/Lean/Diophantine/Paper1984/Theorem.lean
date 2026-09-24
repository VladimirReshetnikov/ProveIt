import Diophantine.Paper1984.Completeness
import Diophantine.Paper1984.Soundness

/-!
# Jones–Matijasevič 1984, §3: the main theorem

For a (normalised) register machine program `P` and an input `x`, the
conditions (24)–(39) on the unknowns `s, Q, I, R_1, …, R_r, L_0, …, L_l` have a
solution if and only if `P` accepts `x`.  Together with §2 (each condition is
exponential Diophantine: `≼` via binomial coefficients and Lucas' theorem,
`Q pow 2` via (12), `rem` via (6), …) this is the register-machine proof of the
Davis–Putnam–Robinson theorem: every recursively enumerable set is exponential
Diophantine.
-/

namespace JM1984
namespace RM

/-- **Jones–Matijasevič 1984, §3.**  A well-formed register machine program `P`
accepts `x` iff the system (24)–(39) is solvable. -/
theorem accepts_iff {r : ℕ} (P : Program r) (hP : WF P) (x : ℕ) :
    Accepts P x ↔ ∃ s Q I R L, Sys P x s Q I R L :=
  ⟨fun h => let ⟨s, Q, I, R, L, H, _⟩ := sys_of_accepts hP h; ⟨s, Q, I, R, L, H⟩,
    fun ⟨_, _, _, _, _, H⟩ => accepts_of_sys hP H⟩

end RM
end JM1984
