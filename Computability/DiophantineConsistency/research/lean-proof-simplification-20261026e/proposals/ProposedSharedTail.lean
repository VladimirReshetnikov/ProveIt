import DiophantineConsistency.NearSquareFinalizer

/-!
UNCOMPILED REFACTOR PROTOTYPE. Static-source evidence only.
Pinned upstream: 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
This is a common scalar constructor, NOT an equality of the distinct Gap/Split
circuits, source parameters, or full polynomial definitions. No existing code
or node count is changed by this standalone proposal.
-/
namespace DiophantineConsistency.ProposedSharedTail
variable {A B : Type*} [CommRing A] [CommRing B]

def ratioValue (R N b g t h s w C i j n : A) : A :=
  let U := N^2*w
  let Y := N^2*s
  let M := R*Y
  let P := 2*M^2*U
  let K := R+1+h*(P-1)
  let a := M*(U+1)
  let B1 := 2*R+1
  let W := b*w
  let J := 4*a-5
  let Q := 3*W*C-2*(W^2-1)
  let D := (a^2-1)*C^2+1
  let E := i*J*D*C^2
  let F := (a^2-1)*E^2+1
  let G := a+F*(C*D+1-a)
  let H := C+F*(B1+j*C)
  let I := (G^2-1)*H^2+1
  let k := i*J*C
  let V0 := P*K
  let V1 := k*(8*D^2-4*D-1)*G*H
  let m := K^2*(4*t-g)-16*t*(C-K*Y)^2
  let omega := J*m
  let theta := J*(n+W^2)+Q-omega*(V0+V1)
  NearSquareFinalizer.norm theta omega ((P^2-1)*K^2+1) 8 (D*F*I)


theorem map_ratioValue (f : A →+* B) (R N b g t h s w C i j n : A) :
    f (ratioValue R N b g t h s w C i j n)=
      ratioValue (f R) (f N) (f b) (f g) (f t) (f h) (f s) (f w) (f C) (f i) (f j) (f n) := by
  simp only [ratioValue,NearSquareFinalizer.norm,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]


/-- The sole coordinate left unshifted is the internal CRT index 7. -/
def successorShift (x : Fin 9 → A) : Fin 9 → A :=
  fun i => if i = 7 then x i else x i + 1

theorem map_successorShift (f : A →+* B) (x : Fin 9 → A) :
    (fun i => f (successorShift x i)) = successorShift (fun i => f (x i)) := by
  funext i
  by_cases hi : i = 7 <;>
    simp only [successorShift, hi, if_true, if_false, map_add, map_one]

end DiophantineConsistency.ProposedSharedTail
