module
public import PA196.Program
@[expose] public section
namespace PA196.Arithmetic.Scheduler.AXGateRows
open M6.Source
theorem row3769 : resolveAt Program.sites 3658 = some (.dec 3 (some 3662) (some 3659)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3770 : resolveAt Program.sites 3659 = some (.inc 7 (some 3660)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3771 : resolveAt Program.sites 3660 = some (.inc 6 (some 3661)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3772 : resolveAt Program.sites 3661 = some (.jump (some 3658)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3785 : resolveAt Program.sites 3674 = some (.dec 7 (some 3677) (some 3675)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3786 : resolveAt Program.sites 3675 = some (.inc 6 (some 3676)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3787 : resolveAt Program.sites 3676 = some (.jump (some 3674)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3788 : resolveAt Program.sites 3677 = some (.dec 4 (some 3680) (some 3678)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3789 : resolveAt Program.sites 3678 = some (.inc 5 (some 3679)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3790 : resolveAt Program.sites 3679 = some (.jump (some 3677)) := by
  rw [Program.resolve_tree]; decide +kernel
theorem row3803 : resolveAt Program.sites 3692 = some (.jump (some 3799)) := by
  rw [Program.resolve_tree]; decide +kernel
end PA196.Arithmetic.Scheduler.AXGateRows
