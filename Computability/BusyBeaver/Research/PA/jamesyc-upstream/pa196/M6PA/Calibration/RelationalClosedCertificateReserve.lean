module

public import Std

@[expose] public section

namespace M6.PA.RelationalClosedCertificate

def certificateReserve (budget code : Nat) : Nat :=
  max 20 budget + code

-- Establish the inequalities with a symbolic code before instantiating them.
theorem certificateReserve_code (budget code : Nat) : code ≤ certificateReserve budget code :=
  Nat.le_add_left _ _

theorem certificateReserve_room (budget code : Nat) : 20 ≤ certificateReserve budget code :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)

theorem certificateReserve_budget (budget code : Nat) : budget ≤ certificateReserve budget code :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)

theorem certificateReserve_budget_left (a b code : Nat) : a ≤ certificateReserve (max a b) code :=
  Nat.le_trans (Nat.le_max_left _ _) (certificateReserve_budget _ _)

theorem certificateReserve_budget_right (a b code : Nat) : b ≤ certificateReserve (max a b) code :=
  Nat.le_trans (Nat.le_max_right _ _) (certificateReserve_budget _ _)

end M6.PA.RelationalClosedCertificate
