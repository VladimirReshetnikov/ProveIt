import PA194BRows

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194BRows

/-- Transport the delivered PA194B action to native labels. The current
control is supplied in the primary machine's dense numbering. -/
def reorder (q : Nat) : Nat :=
  (labels.idxOf (primaryLabels.getD q 254))

def nativeAction (ids : List Nat) (v : Action) : Action :=
  (v.1,v.2.1,ids.getD v.2.2 254)

def expectedNative (q b : Nat) : Action :=
  match primaryLabels.getD q 254,b with
  | 87,0 => (0,1,88)
  | 88,0 => (0,0,301)
  | 301,0 => (0,1,122)
  | 301,1 => (1,1,301)
  | _,_ => nativeAction primaryLabels (primary q b)

theorem counts : actions.length = 388 ∧ labels.length = 195 ∧
    primaryLabels.length = 195 ∧ targets.length = 195 := by decide +kernel

theorem labelTransport : ∀ q : Fin 195,
    labels.getD (reorder q.val) 254 = primaryLabels.getD q.val 254 ∧ reorder q.val < 195 := by
  decide +kernel

theorem nativeDelta : ∀ (q : Fin 194) (b : Fin 2),
    nativeAction labels (action (reorder q.val) b.val) = expectedNative q.val b.val := by
  decide +kernel

theorem rhoLabels : ∀ q : Fin 195,
    rho q.val = if primaryLabels.getD q.val 254 = 301 then labels.idxOf 88 else reorder q.val := by
  decide +kernel

theorem rhoHalt : rho 194 = 194 := by decide +kernel

theorem rhoStart : rho 0 = 0 := by decide +kernel

theorem rhoLive : ∀ q : Fin 194, rho q.val < 194 := by decide +kernel

theorem ordinary : ∀ (q : Fin 194) (b : Fin 2), q.val ≠ 39 → q.val ≠ 52 →
    let a := primary q.val b.val
    action (rho q.val) b.val = (a.1,a.2.1,rho a.2.2) := by decide +kernel

theorem incoming39 : ∀ (q : Fin 194) (b : Fin 2), (primary q.val b.val).2.2 = 39 →
    primary q.val b.val = (1,1,39) := by decide +kernel

theorem incoming52 : ∀ (q : Fin 194) (b : Fin 2), (primary q.val b.val).2.2 = 52 →
    primary q.val b.val = (0,1,52) := by decide +kernel

theorem oldTarget : ∀ (q : Fin 194) (b : Fin 2), (primary q.val b.val).2.2 ≤ 194 := by
  decide +kernel

theorem newTarget : ∀ (q : Fin 194) (b : Fin 2), (action q.val b.val).2.2 ≤ 194 := by
  decide +kernel

theorem exceptions :
    rho 39 = 39 ∧ rho 52 = 39 ∧ rho 53 = 72 ∧ rho 54 = 53 ∧ rho 73 = 106 ∧
    primary 39 0 = (0,1,53) ∧ primary 39 1 = (1,1,54) ∧
    primary 52 0 = (0,1,73) ∧ primary 52 1 = (1,1,54) ∧
    action 39 0 = (0,0,52) ∧ action 39 1 = (1,1,53) ∧
    action 52 0 = (0,1,72) ∧ action 52 1 = (1,1,52) ∧
    action 72 0 = (0,0,95) ∧ action 95 0 = (0,1,84) ∧ action 84 0 = (0,1,106) := by decide +kernel

#print axioms nativeDelta
#print axioms ordinary
#print axioms exceptions
end PA194BRows
