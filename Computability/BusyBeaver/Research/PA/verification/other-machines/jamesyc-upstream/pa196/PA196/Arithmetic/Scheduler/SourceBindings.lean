module
public import PA196.Program
public import PA196.Source.Readers
public import M6.Source.UnpairPartial
@[expose] public section
namespace PA196.Arithmetic.Scheduler.SourceBindings
open M6.Source

theorem stack_partial : UnpairPartial.Bound Program.sites 11 := by
  unfold UnpairPartial.Bound
  simp only [Program.resolve_tree]
  decide +kernel

theorem stack_last11 : resolveAt Program.sites 22 = some (.dec 6 (some 25) (some 23)) := by
  rw [Program.resolve_tree]; decide +kernel
 theorem stack_last12 : resolveAt Program.sites 23 = some (.inc 5 (some 24)) := by
  rw [Program.resolve_tree]; decide +kernel
 theorem stack_last13 : resolveAt Program.sites 24 = some (.jump (some 22)) := by
  rw [Program.resolve_tree]; decide +kernel
end PA196.Arithmetic.Scheduler.SourceBindings
