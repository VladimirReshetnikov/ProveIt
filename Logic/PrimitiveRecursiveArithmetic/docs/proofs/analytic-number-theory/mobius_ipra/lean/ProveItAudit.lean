/- Replay in the pinned ProveIt checkout. Build the imported modules first.
   These declarations have conclusions in the embedded calculus. -/
import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.AnalyticNumberTheory.SummatoryPhi
import IPRADerivations.AnalyticNumberTheory.MuLambda
import IPRADerivations.AnalyticNumberTheory.PsiModulus
import IPRADerivations.AnalyticNumberTheory.FinalPNT

open LeanProofs.IPRA.AnalyticNumberTheory

#check Mobius.muP
#check Mobius.muN
#check Mobius.swap
#check Mobius.kill
#check Mobius.mobius_one
#check Mobius.mobius_cancel
#check MobiusBounds.mu_bound
#check MobiusBounds.cancel_gen
#check MobiusInversion.mobius_inversion
#check MobiusInversion.phi_mobius
#check SummatoryPhi.summatory_phi
#check MuLambda.mu_lambda
#check PsiModulus.psi_modulus
#check FinalPNT.arith_pnt

#print axioms LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds.cancel_gen
#print axioms LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion.mobius_inversion
#print axioms LeanProofs.IPRA.AnalyticNumberTheory.PsiModulus.psi_modulus
