import IPRADerivations.Analysis.Stirling.Binet.Bose.LiteralTails.GaussianBinetBoseLiteralUniform

/-!
# Literal Bose observations at an independent later clock

Choose the geometric cutoff at the requested comparison precision.
The existing literal prefix can then be evaluated at any later
observation, keeping the same actual exponential row clock schedule.
-/

set_option autoImplicit false
namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralLate

alias finite_uniform_late := GaussianBinetBoseLiteralUniform.finite_uniform_late

end LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralLate
