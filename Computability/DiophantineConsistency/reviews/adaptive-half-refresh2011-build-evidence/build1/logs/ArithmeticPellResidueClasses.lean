import DiophantineConsistency.ArithmeticPellPeriodicity
import DiophantineConsistency.ArithmeticModularCancellation

/-! Complete first-coordinate residue classes at arbitrary internal indices.
All arithmetic is in the IΣ1 model. The local positive target excludes the
base2/index0 exception; no carrier index or fundamental-unit premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellResidueClasses
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellPeriodicity
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mod_add_congr (a b c m : V) (hm : 0<m) (h : a%m=b%m) :
    (a+c)%m=(b+c)%m := by
  rw [mod_add (a:=a) (b:=c) hm,mod_add (a:=b) (b:=c) hm,h]

theorem mod_add_cancel (a b c m : V) (hm : 0<m)
    (h : (a+c)%m=(b+c)%m) : a%m=b%m := by
  exact ArithmeticModularCancellation.add_cancel hm h

theorem mod_reduce (a m n : V) (hm : 0<m) (hdiv : m∣n) :
    (a%n)%m=a%m := ArithmeticModularCancellation.mod_mod_of_dvd hm hdiv a

theorem mod_scale (a m c : V) (hm : 0<m) (hc : 0<c) :
    (c*a)%(c*m)=c*(a%m) := ArithmeticModularCancellation.mul_mod_mul hc hm

theorem x_strictMono (b : V) : StrictMono (fun t : V => xcoord t b) := by
  intro i j hij
  have hd : 1≤j-i := by simpa using lt_iff_succ_le.mp (tsub_pos_iff_lt.mpr hij)
  have hx : 1<xcoord (j-i) b := lt_of_le_of_lt
    (le_trans hd (time_le_y (j-i) b)) (y_lt_x (j-i) b)
  have hp : 0<xcoord i b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x i b)
  calc
    xcoord i b<xcoord i b*xcoord (j-i) b := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hx hp
    _≤xcoord (i+(j-i)) b := by rw [(addition i (j-i) b).1]; simp
    _=xcoord j b := by rw [add_tsub_cancel_of_le (le_of_lt hij)]

theorem x_reflection_add (l r b : V) :
    xcoord (l+2*r) b+xcoord l b=2*xcoord (l+r) b*xcoord r b := by
  rw [(addition l (2*r) b).1,double_y]
  calc
    xcoord l b*xcoord (2*r) b+delta b*ycoord l b*(2*xcoord r b*ycoord r b)+xcoord l b=
      xcoord l b*(xcoord (2*r) b+1)+2*delta b*ycoord l b*xcoord r b*ycoord r b := by ring
    _=2*xcoord (l+r) b*xcoord r b := by
      rw [double_x_add_one,(addition l r b).1]
      ring

theorem x_reflection (n m b : V) (hm : m≤n) :
    xcoord (n+m) b+xcoord (n-m) b=2*xcoord n b*xcoord m b := by
  simpa only [two_mul, ← add_assoc, tsub_add_cancel_of_le hm] using
    x_reflection_add (n-m) m b

theorem x_antiperiod (n t b : V) :
    (xcoord (2*n+t) b+xcoord t b)%xcoord n b=0 := by
  have h := x_reflection_add t n b
  rw [add_comm t (2*n),add_comm t n] at h
  rw [h]
  exact mod_mul_self_left _ _

theorem x_antireflection (n j b : V) (hj : j≤2*n) :
    (xcoord (2*n-j) b+xcoord j b)%xcoord n b=0 := by
  have key (u : V) (hu : u≤n) :
      (xcoord (2*n-u) b+xcoord u b)%xcoord n b=0 := by
    have h := x_reflection n (n-u) b (tsub_le_self)
    rw [tsub_tsub_cancel_of_le hu,
      show n+(n-u)=2*n-u by rw [two_mul,add_tsub_assoc_of_le hu]] at h
    rw [h,show 2*xcoord n b*xcoord (n-u) b=xcoord n b*(2*xcoord (n-u) b) by ring]
    exact mod_mul_self_right _ _
  rcases le_total j n with h|h
  · exact key j h
  · have hsub : 2*n-j≤n := by
      apply (tsub_le_iff_right).mpr
      simpa only [two_mul] using (_root_.add_le_add le_rfl h : n+n≤n+j)
    have hh := key (2*n-j) hsub
    rwa [tsub_tsub_cancel_of_le hj,add_comm] at hh

theorem x_four_reflection (n j b : V) (hj : j≤2*n) :
    xcoord (4*n-j) b%xcoord n b=xcoord j b%xcoord n b := by
  have hp : 0<xcoord n b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x n b)
  apply mod_add_cancel _ _ (xcoord (2*n-j) b) _ hp
  have h1 := x_antiperiod n (2*n-j) b
  have he : 2*n+(2*n-j)=4*n-j := by
    rw [←add_tsub_assoc_of_le hj]
    congr 1
    ring
  rw [he] at h1
  exact h1.trans (by simpa only [add_comm] using (x_antireflection n j b hj).symm)

theorem x_gap (n b : V) (hn : 2≤n) : 2*xcoord (n-1) b<xcoord n b := by
  have h1 : 1≤n := le_trans (by simp) hn
  have hpred : 1≤n-1 := (le_tsub_iff_right h1).mpr (by
    simpa only [show (1:V)+1=2 by ring] using hn)
  have hy : 0<ycoord (n-1) b := lt_of_lt_of_le (by simp : (0:V)<1)
    (le_trans hpred (time_le_y (n-1) b))
  have hd : 0<delta b := by unfold delta; exact mul_pos (by simp) (by simp)
  calc
    2*xcoord (n-1) b≤(b+2)*xcoord (n-1) b :=
      mul_le_mul_of_nonneg_right (by simp) (Arithmetic.zero_le _)
    _<(b+2)*xcoord (n-1) b+delta b*ycoord (n-1) b :=
      lt_add_of_pos_right _ (mul_pos hd hy)
    _=xcoord n b := by rw [←x_succ,tsub_add_cancel_of_le h1]

theorem x_local_residue (b i j n : V) (hi : 0<i) (hin : i≤n) (hj : j≤2*n)
    (h : xcoord j b%xcoord n b=xcoord i b%xcoord n b) : j=i := by
  have hp : 0<xcoord n b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x n b)
  have hxpos (r : V) : 0<xcoord r b :=
    lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x r b)
  rcases le_total j n with hle|hge
  · rcases lt_or_eq_of_le hin with hil|hie
    · rcases lt_or_eq_of_le hle with hjl|hje
      · rw [mod_eq_self_of_lt (x_strictMono b hjl),mod_eq_self_of_lt (x_strictMono b hil)] at h
        exact (x_strictMono b).injective h
      · rw [hje,mod_self,mod_eq_self_of_lt (x_strictMono b hil)] at h
        exact False.elim ((ne_of_gt (hxpos i)) h.symm)
    · rw [hie,mod_self] at h
      rcases lt_or_eq_of_le hle with hjl|hje
      · rw [mod_eq_self_of_lt (x_strictMono b hjl)] at h
        exact False.elim ((ne_of_gt (hxpos j)) h)
      · exact hje.trans hie.symm
  · rcases eq_or_lt_of_le hge with he|hlt
    · subst j
      rcases lt_or_eq_of_le hin with hil|hie
      · rw [mod_self,mod_eq_self_of_lt (x_strictMono b hil)] at h
        exact False.elim ((ne_of_gt (hxpos i)) h.symm)
      · exact hie.symm
    · let r := 2*n-j
      have hr : r<n := by
        apply (tsub_lt_iff_left hj).mpr
        simpa only [two_mul] using (_root_.add_lt_add_of_lt_of_le hlt le_rfl : n+n<j+n)
      have hxr : xcoord r b<xcoord n b := x_strictMono b hr
      have hneg : xcoord j b%xcoord n b=(xcoord n b-xcoord r b)%xcoord n b := by
        apply mod_add_cancel _ _ (xcoord r b) _ hp
        rw [tsub_add_cancel_of_le (le_of_lt hxr),mod_self]
        simpa only [r,add_comm] using x_antireflection n j b hj
      have hsmall : xcoord n b-xcoord r b<xcoord n b :=
        tsub_lt_self hp (hxpos r)
      rw [mod_eq_self_of_lt hsmall] at hneg
      rcases lt_or_eq_of_le hin with hil|hie
      · rw [mod_eq_self_of_lt (x_strictMono b hil)] at h
        have heq : xcoord i b+xcoord r b=xcoord n b := by
          calc
            xcoord i b+xcoord r b=(xcoord n b-xcoord r b)+xcoord r b :=
              congrArg (fun v : V => v+xcoord r b) (h.symm.trans hneg)
            _=xcoord n b := tsub_add_cancel_of_le (le_of_lt hxr)
        have hi1 : 1≤i := by simpa using lt_iff_succ_le.mp hi
        have hn2 : 2≤n := by
          calc
            2=(1:V)+1 := by ring
            _≤i+1 := _root_.add_le_add hi1 le_rfl
            _≤n := lt_iff_succ_le.mp hil
        have h1 : 1≤n := le_trans (by simp) hn2
        have hil' : i≤n-1 := (le_tsub_iff_right h1).mpr (lt_iff_succ_le.mp hil)
        have hrl' : r≤n-1 := (le_tsub_iff_right h1).mpr (lt_iff_succ_le.mp hr)
        have hsumle : xcoord i b+xcoord r b≤2*xcoord (n-1) b := by
          rw [two_mul]
          exact _root_.add_le_add ((x_strictMono b).monotone hil') ((x_strictMono b).monotone hrl')
        have hsum := lt_of_le_of_lt hsumle (x_gap n b hn2)
        exact False.elim ((ne_of_lt hsum) heq)
      · rw [hie,mod_self] at h
        have hz : xcoord n b-xcoord r b=0 := hneg.symm.trans h
        exact False.elim ((ne_of_gt (tsub_pos_iff_lt.mpr hxr)) hz)

theorem x_residue_classes (b i j n : V) (hi : 0<i) (hin : i≤n)
    (h : xcoord j b%xcoord n b=xcoord i b%xcoord n b) :
    j%(4*n)=i ∨ (j+i)%(4*n)=0 := by
  have hn : 0<n := lt_of_lt_of_le hi hin
  have h4 : 0<4*n := mul_pos (by simp) hn
  let j0 := j%(4*n)
  have hj0 : j0<4*n := mod_lt j h4
  have hp : xcoord j0 b%xcoord n b=xcoord i b%xcoord n b := by
    have hh := (period_mod (j/(4*n)) n j0 b).1
    rw [show 4*n*(j/(4*n))+j0=j from div_add_mod j (4*n)] at hh
    exact hh.symm.trans h
  rcases le_total j0 (2*n) with hlo|hhi
  · exact Or.inl (x_local_residue b i j0 n hi hin hlo hp)
  · have hr : 4*n-j0≤2*n := by
      apply tsub_le_iff_right.mpr
      calc
        4*n=2*n+2*n := by ring
        _≤2*n+j0 := _root_.add_le_add le_rfl hhi
    have he : xcoord (4*n-j0) b%xcoord n b=xcoord j0 b%xcoord n b := by
      have hh := x_four_reflection n (4*n-j0) b hr
      rw [tsub_tsub_cancel_of_le (le_of_lt hj0)] at hh
      exact hh.symm
    have hridx := x_local_residue b i (4*n-j0) n hi hin hr (he.trans hp)
    right
    have hsum : j0+i=4*n := by rw [←hridx,add_tsub_cancel_of_le (le_of_lt hj0)]
    calc
      (j+i)%(4*n)=(j0+i)%(4*n) := by
        rw [mod_add (a:=j) (b:=i) h4,mod_add (a:=j0) (b:=i) h4,
          mod_eq_self_of_lt hj0]
      _=0 := by rw [hsum,mod_self]

theorem doubled_step_down (b m p t : V) (hp : 0<p) (hpm : 2*p≤m)
    (h : xcoord (2*t) b%xcoord m b=xcoord (2*p) b%xcoord m b ∨
      (xcoord (2*t) b+xcoord (2*p) b)%xcoord m b=0) :
    t%m=p%m ∨ (t+p)%m=0 := by
  have hm : 0<m := lt_of_lt_of_le (mul_pos (by simp) hp) hpm
  have h2 : 0<(2:V) := by simp
  have hxm : 0<xcoord m b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x m b)
  have key (j : V) (hj : xcoord j b%xcoord m b=xcoord (2*p) b%xcoord m b) :
      j%(2*m)=(2*p)%(2*m) ∨ (j+2*p)%(2*m)=0 := by
    have hd : 2*m∣4*m := ⟨2,by ring⟩
    rcases x_residue_classes b (2*p) j m (mul_pos h2 hp) hpm hj with he|he
    · left
      have hh := congrArg (fun x : V => x%(2*m)) he
      rwa [mod_reduce _ _ _ (mul_pos h2 hm) hd] at hh
    · right
      have hh := congrArg (fun x : V => x%(2*m)) he
      simpa only [mod_reduce _ _ _ (mul_pos h2 hm) hd,zero_mod] using hh
  have finish (he : (2*t)%(2*m)=(2*p)%(2*m) ∨ (2*t+2*p)%(2*m)=0) :
      t%m=p%m ∨ (t+p)%m=0 := by
    rcases he with he|he
    · left
      rw [mod_scale _ _ _ hm h2,mod_scale _ _ _ hm h2] at he
      exact mul_left_cancel₀ (ne_of_gt h2) he
    · right
      rw [show 2*t+2*p=2*(t+p) by ring,mod_scale _ _ _ hm h2] at he
      exact (mul_eq_zero.mp he).resolve_left (ne_of_gt h2)
  rcases h with he|he
  · exact finish (key (2*t) he)
  · have hj : xcoord (2*m+2*t) b%xcoord m b=xcoord (2*p) b%xcoord m b := by
      apply mod_add_cancel _ _ (xcoord (2*t) b) _ hxm
      exact (x_antiperiod m (2*t) b).trans (by simpa only [add_comm] using he.symm)
    have hh := key (2*m+2*t) hj
    apply finish
    simpa only [add_assoc,mod_add_remove_left (mul_pos h2 hm)] using hh

theorem odd_index_of_base_dvd (b j : V) (h : b+2∣xcoord j b) : j%2=1 := by
  have hx1 : xcoord 1 b=b+2 := by simpa using x_succ (0:V) b
  have he : xcoord j b%xcoord 1 b=xcoord 1 b%xcoord 1 b := by
    rw [hx1,mod_self]
    exact mod_eq_zero_iff_dvd.mpr h
  have h2 : 0<(2:V) := by simp
  have hd : (2:V)∣4 := ⟨2,by ring⟩
  rcases x_residue_classes b 1 j 1 (by simp) le_rfl he with hh|hh
  · have hmod := congrArg (fun x : V => x%2) hh
    simpa only [mul_one,mod_reduce _ _ _ h2 hd,mod_eq_self_of_lt (show (1:V)<2 by simp)] using hmod
  · have hmod := congrArg (fun x : V => x%2) hh
    have hz : (j+1)%2=0 := by simpa only [mul_one,mod_reduce _ _ _ h2 hd,zero_mod] using hmod
    rcases mod_two j with hj|hj
    · have hone : (j+1)%2=1 := by rw [mod_add h2,hj]; simp
      exact False.elim (_root_.one_ne_zero (hone.symm.trans hz))
    · exact hj

theorem odd_index_witness (b j : V) (h : b+2∣xcoord j b) :
    ∃ k : V, j=2*k+1 := by
  refine ⟨j/2,?_⟩
  have hh := div_add_mod j 2
  rw [odd_index_of_base_dvd b j h] at hh
  exact hh.symm

end DiophantineConsistency.ArithmeticPellResidueClasses
