import BusyBeaver.ZFC.L2Control222

/- Typed consumers of the public 222 contracts, independent of the sharing
certificate and native 254 proof names. Compile this same file against each
side of the change and compare the exact printed assumption profiles. -/
namespace MacroSharing18Api

open SetTheory.BusyBeaver.ZFC
open RMDag Dag222 Code254

-- Positional construction, named updates and the out-of-range convention are
-- observable parts of the state interface, including qualified `L2K.AS`.
theorem record_encoding (np tw ws ac p1 p2 s1 s2 pl : Nat) :
    L2K.enc (⟨np, tw, ws, ac, p1, p2, s1, s2, pl⟩ : L2K.AS) 0 = np ∧
    L2K.enc (⟨np, tw, ws, ac, p1, p2, s1, s2, pl⟩ : L2K.AS) 8 = pl ∧
    L2K.enc (⟨np, tw, ws, ac, p1, p2, s1, s2, pl⟩ : L2K.AS) 9 = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem named_update (st : L2K.AS) (v : Nat) :
    upd (L2K.enc st) 6 v = L2K.enc { st with s1 := v } :=
  L2K.upd_s1 st v

theorem indexed_update (st : L2K.AS) (r v : Nat) (hr : r < 9) :
    upd (L2K.enc st) r v = L2K.enc (L2K.updAS st r v) ∧
    L2K.enc (L2K.updAS st r v) r = v :=
  ⟨L2K.upd_enc_AS st r v hr, L2K.enc_updAS_self st r v hr⟩

theorem push_parameter (st : L2K.AS) (hc : L2K.Clean st) :
    Run dag222 (.node 166) (L2K.enc st) .normal
      (L2K.enc { st with tw := st.p1, ws := P st.tw st.ws }) :=
  L2K.par1 st hc

-- The constructor contract consumes the actual top of the paired stack;
-- the cleanliness fact is usable again at the returned state.
theorem implication_and_clean (st : L2K.AS) (hc : L2K.Clean st) :
    Run dag222 (.node 119) (L2K.enc st) .normal
      (L2K.enc { st with tw := wim (SetTheory.Cantor.ofNat st.ws).1 st.tw, ws := (SetTheory.Cantor.ofNat st.ws).2 }) ∧
    L2K.Clean { st with tw := wim (SetTheory.Cantor.ofNat st.ws).1 st.tw, ws := (SetTheory.Cantor.ofNat st.ws).2 } :=
  ⟨L2K.cons st hc, L2K.cons_clean hc⟩

theorem read_parameter (st : L2K.AS) (hc : L2K.Clean st) :
    Run dag222 (.node 175) (L2K.enc st) .normal
      (L2K.enc { st with pl := (SetTheory.Cantor.ofNat st.pl).2, p1 := st.p1 + (SetTheory.Cantor.ofNat st.pl).1 }) :=
  L2K.read_p1 st hc

-- The non-normal branch is part of the public contract as well.
theorem unequal_break (st : L2K.AS) (h : st.s1 ≠ st.p2) :
    Run dag222 (.node 123) (L2K.enc st) (.brk 1)
      (L2K.enc { st with s1 := 0, p2 := 0 }) :=
  L2K.ifeq_ne st h

theorem modus_ponens (st : L2K.AS) (hc : L2K.Clean st) :
    Run dag222 (.node 150) (L2K.enc st) .normal
      (L2K.enc (if wim st.tw st.p1 = st.p2
        then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 }
        else { st with tw := 0, p2 := 0 })) :=
  L2K.mp_branch st hc

-- Fetch crosses the rotated loop deliberately excluded from shared transport.
theorem fetch_cases (st : L2K.AS) :
    (∀ v, st.pl = v + 1 → Run dag222 (.node 133) (L2K.enc st) .normal
      (L2K.enc { st with pl := v })) ∧
    (st.pl = 0 → st.s1 = 0 → Run dag222 (.node 133) (L2K.enc st) .normal
      (L2K.enc { st with pl := st.np, np := st.np + 1 })) :=
  ⟨fun v hv => L2K.fetch_pos st v hv, fun hp hs => L2K.fetch_zero st hp hs⟩

theorem halt_branch (st : L2K.AS) (hc : L2K.Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag222 (.node 152) (L2K.enc st) .halt R' :=
  L2K.nip_halt st hc hh

#print axioms record_encoding
#print axioms named_update
#print axioms indexed_update
#print axioms push_parameter
#print axioms implication_and_clean
#print axioms read_parameter
#print axioms unequal_break
#print axioms modus_ponens
#print axioms fetch_cases
#print axioms halt_branch

end MacroSharing18Api
