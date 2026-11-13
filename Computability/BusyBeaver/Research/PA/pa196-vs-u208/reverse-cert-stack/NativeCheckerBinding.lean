import NativeChecker
import UpstreamCommandAudit

/-! Exact upstream command-word binding to the direct Nat checker.
The direct checker's full equality to the imported Foundation/model-valued
`Checker.verifyValue` and all iPRA-internal facts remain unproved here. -/
namespace PA196CertificateStack.NativeChecker

theorem upstream_command_halt_yields_numeric_certificate
    (cs : List PA196.Commands.Command)
    (halt : PA196.Commands.run cs (⟨0,0,0,0⟩ : PA196.Commands.Store) = none) :
    ∃ proof, verify proof = 2 := by
  exact PA196UpstreamCommandAudit.upstream_halt_has_checker_certificate
    cert checker_interfaces cs halt

end PA196CertificateStack.NativeChecker

#print axioms PA196CertificateStack.NativeChecker.upstream_command_halt_yields_numeric_certificate
