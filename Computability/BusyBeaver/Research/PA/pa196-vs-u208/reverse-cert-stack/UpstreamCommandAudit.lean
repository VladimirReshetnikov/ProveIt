import CertificateStack
import PA196.Commands.Store

/-!
Binds the standalone certificate extractor to the actual imported PA196
Cantor and command sources. The checker equations remain explicit hypotheses;
this is not an iPRA theorem or a proof of literal machine halting behavior.
-/

namespace PA196UpstreamCommandAudit
open PA196CertificateStack
open PA196CertificateStack.Cantor
open PA196CertificateStack.Native

theorem triangle_eq (n : Nat) : Cantor.triangle n = M6.Source.Cantor.triangle n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Cantor.triangle, M6.Source.Cantor.triangle, ih]

theorem pair_eq (a b : Nat) : Cantor.pair a b = M6.Source.Cantor.pair a b := by
  simp [Cantor.pair, M6.Source.Cantor.pair, triangle_eq]

theorem heads_eq (D H A d h : Nat) : Native.heads D H A d h = PA196.Commands.Code.heads D H A d h := by
  simp [Native.heads, PA196.Commands.Code.heads,
    Native.head1, PA196.Commands.Code.head1, Native.head2, PA196.Commands.Code.head2,
    Native.head3, PA196.Commands.Code.head3, Native.head4, PA196.Commands.Code.head4,
    Native.head5, PA196.Commands.Code.head5, Native.head6, PA196.Commands.Code.head6,
    Native.rho8, PA196.Commands.Code.rho8, Native.ex, PA196.Commands.Code.ex,
    Native.N, PA196.Commands.Code.N, Native.I, PA196.Commands.Code.I,
    Native.U, PA196.Commands.Code.U, Native.M, PA196.Commands.Code.M,
    Native.E, PA196.Commands.Code.E, pair_eq]

theorem gate_eq (a b c : Nat) : Native.gate a b c = PA196.Commands.Code.gate a b c := by
  simp [Native.gate, PA196.Commands.Code.gate, Native.bundle, PA196.Commands.Code.bundle,
    Native.eqVac, PA196.Commands.Code.eqVac, Native.memVac, PA196.Commands.Code.memVac,
    Native.separationTail, PA196.Commands.Code.separationTail,
    Native.separation, PA196.Commands.Code.separation, Native.point, PA196.Commands.Code.point,
    Native.conj, PA196.Commands.Code.conj, Native.N, PA196.Commands.Code.N,
    Native.I, PA196.Commands.Code.I, Native.U, PA196.Commands.Code.U,
    Native.M, PA196.Commands.Code.M, Native.E, PA196.Commands.Code.E, pair_eq]

theorem old_order_wrong : PA196.Commands.Code.head4 1 0 0 ≠ PA196.Commands.Code.head4 0 1 0 := by
  intro h
  change 4 * M6.Source.Cantor.pair (PA196.Commands.Code.E 0 1)
      (PA196.Commands.Code.I (PA196.Commands.Code.M 0 0) (PA196.Commands.Code.M 0 1)) =
      4 * M6.Source.Cantor.pair (PA196.Commands.Code.E 0 0)
      (PA196.Commands.Code.I (PA196.Commands.Code.M 1 0) (PA196.Commands.Code.M 1 0)) at h
  have hp : M6.Source.Cantor.pair (PA196.Commands.Code.E 0 1)
      (PA196.Commands.Code.I (PA196.Commands.Code.M 0 0) (PA196.Commands.Code.M 0 1)) =
      M6.Source.Cantor.pair (PA196.Commands.Code.E 0 0)
      (PA196.Commands.Code.I (PA196.Commands.Code.M 1 0) (PA196.Commands.Code.M 1 0)) := by omega
  have he := (M6.Source.Cantor.pair_injective hp).1
  have hn : PA196.Commands.Code.E 0 1 ≠ PA196.Commands.Code.E 0 0 := by decide
  exact hn he
end PA196UpstreamCommandAudit
namespace PA196UpstreamCommandAudit

theorem advance_eq (p : Nat × Nat) :
    PA196CertificateStack.Cantor.advance p = M6.Source.Cantor.advance p := by
  rcases p with ⟨a,b⟩
  cases a <;> rfl

theorem decode_eq (n : Nat) :
    PA196CertificateStack.Cantor.decode n = M6.Source.Cantor.decode n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [PA196CertificateStack.Cantor.decode, M6.Source.Cantor.decode, ih, advance_eq]

def toStore (s : PA196CertificateStack.Commands.Store) : PA196.Commands.Store := ⟨s.t,s.w,s.d,s.h⟩
def toCommand : PA196CertificateStack.Commands.Command → PA196.Commands.Command
  | .shift => .shift
  | .mp x => .mp x
  | .ax a x y => .ax a x y

theorem step_eq (c : PA196CertificateStack.Commands.Command) (s : PA196CertificateStack.Commands.Store) :
    (PA196CertificateStack.Commands.step PA196CertificateStack.Cantor.pair
      PA196CertificateStack.Cantor.decode PA196CertificateStack.Native.heads
      PA196CertificateStack.Native.gate c s).map toStore =
      PA196.Commands.step (toCommand c) (toStore s) := by
  have hp : PA196CertificateStack.Cantor.pair = M6.Source.Cantor.pair := by
    funext a b; exact pair_eq a b
  have hd : PA196CertificateStack.Cantor.decode = M6.Source.Cantor.decode := by
    funext n; exact decode_eq n
  cases c <;>
    simp [PA196CertificateStack.Commands.step, PA196.Commands.step, toCommand, toStore,
      PA196CertificateStack.Commands.stackOf, PA196CertificateStack.Commands.implication,
      PA196.Commands.Code.I, hp, hd, heads_eq, gate_eq] <;>
      split <;> simp [toStore]
end PA196UpstreamCommandAudit
namespace PA196UpstreamCommandAudit

def fromCommand : PA196.Commands.Command → PA196CertificateStack.Commands.Command
  | .shift => .shift
  | .mp x => .mp x
  | .ax a x y => .ax a x y

@[simp] theorem command_roundtrip (c : PA196.Commands.Command) : toCommand (fromCommand c) = c := by
  cases c <;> rfl

theorem run_eq (cs : List PA196CertificateStack.Commands.Command) (s : PA196CertificateStack.Commands.Store) :
    (PA196CertificateStack.Commands.run PA196CertificateStack.Cantor.pair
      PA196CertificateStack.Cantor.decode PA196CertificateStack.Native.heads
      PA196CertificateStack.Native.gate cs s).map toStore =
      PA196.Commands.run (cs.map toCommand) (toStore s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    cases hs : PA196CertificateStack.Commands.step PA196CertificateStack.Cantor.pair
        PA196CertificateStack.Cantor.decode PA196CertificateStack.Native.heads
        PA196CertificateStack.Native.gate c s with
    | none =>
      have he : PA196.Commands.step (toCommand c) (toStore s) = none := by
        rw [← step_eq, hs]; rfl
      simp [PA196CertificateStack.Commands.run, PA196.Commands.run, hs, he]
    | some next =>
      have he : PA196.Commands.step (toCommand c) (toStore s) = some (toStore next) := by
        rw [← step_eq, hs]; rfl
      simpa [PA196CertificateStack.Commands.run, PA196.Commands.run, hs, he] using ih next

theorem upstream_halt_has_checker_certificate
    (cert : Nat → Nat → Prop) (hcert : PA196CertificateStack.Native.CheckerInterfaces cert)
    (cs : List PA196.Commands.Command)
    (halt : PA196.Commands.run cs (⟨0,0,0,0⟩ : PA196.Commands.Store) = none) :
    ∃ proof, cert proof 1 := by
  have hmap : (cs.map fromCommand).map toCommand = cs := by
    simp [List.map_map, Function.comp_def]
  have hrun := run_eq (cs.map fromCommand) ⟨0,0,0,0⟩
  rw [hmap] at hrun
  have hlocal : PA196CertificateStack.Commands.run PA196CertificateStack.Cantor.pair
      PA196CertificateStack.Cantor.decode PA196CertificateStack.Native.heads
      PA196CertificateStack.Native.gate (cs.map fromCommand) ⟨0,0,0,0⟩ = none := by
    cases he : PA196CertificateStack.Commands.run PA196CertificateStack.Cantor.pair
        PA196CertificateStack.Cantor.decode PA196CertificateStack.Native.heads
        PA196CertificateStack.Native.gate (cs.map fromCommand) ⟨0,0,0,0⟩ with
    | none => rfl
    | some s => simp [he, toStore, halt] at hrun
  obtain ⟨proof, _, hp⟩ := PA196CertificateStack.Native.native_halt_extractor cert hcert _ hlocal
  exact ⟨proof, hp⟩
end PA196UpstreamCommandAudit
namespace PA196UpstreamCommandAudit
theorem upstream_head4_order_counterexample : (PA196.Commands.Code.heads 1 0 0 0 0)[2]! ≠ PA196.Commands.Code.head4 0 1 0 := by
  change PA196.Commands.Code.head4 1 0 0 ≠ PA196.Commands.Code.head4 0 1 0
  exact old_order_wrong
#print axioms upstream_halt_has_checker_certificate
#print axioms old_order_wrong
end PA196UpstreamCommandAudit
namespace PA196UpstreamCommandAudit
set_option maxRecDepth 5000 in
theorem upstream_head4_correct_value : PA196.Commands.Code.head4 1 0 0 = 144136 := by decide
set_option maxRecDepth 5000 in
theorem upstream_head4_permuted_value : PA196.Commands.Code.head4 0 1 0 = 119544 := by decide
end PA196UpstreamCommandAudit
