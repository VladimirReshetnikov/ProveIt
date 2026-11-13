import DiophantineConsistency.Current14Carrier65DegreeDirect
import DiophantineConsistency.Sign17ExactDegree

/-! Candidate specialization of the direct exact-degree theorem to current ports. -/
namespace DiophantineConsistency.Current14Carrier65DegreeCurrent

theorem current_exact :
    (Carrier65.polynomial CurrentWindowCarry2011.ports).totalDegree = 150 :=
  Current14Carrier65DegreeDirect.polynomial_exact CurrentWindowCarry2011.ports
    Sign17ExactDegree.current_port_nonzero

end DiophantineConsistency.Current14Carrier65DegreeCurrent

#print axioms DiophantineConsistency.Current14Carrier65DegreeCurrent.current_exact
