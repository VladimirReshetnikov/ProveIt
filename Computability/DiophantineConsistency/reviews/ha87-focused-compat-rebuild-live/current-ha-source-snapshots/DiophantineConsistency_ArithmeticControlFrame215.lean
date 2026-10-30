import DiophantineConsistency.ArithmeticSite215
import BusyBeaver.ZFC.ArithmeticControl215Table

/-! Canonical entries of the actual 215 control table. Finite consumed-path
rebasing preserves the complete internal register/spare suffix. All source
execution comes from the accepted actual sites. The catalogue and prefix
arguments follow the generic ControlCatalogue/Rotation240 proofs; no old
machine execution theorem is used. Global iteration and boot are separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticControlFrame215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath RegisterPathClean RMBisim SiteCoverage ControlCatalogue
open ArithmeticCantor ArithmeticControlFile ArithmeticControlTable ArithmeticControl215Table
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215
open ArithmeticSite215 (pathValue)

def entries : List (List Bool × Edge) := leafEntries KSource215.t215
theorem entries_length : entries.length=4751 := by
  have h:=congrArg List.length table215_eq_catalogue
  simpa only [table215_length,List.length_map,entries] using h.symm
abbrev Control := Fin 4751
def source (i : Control) : List Bool × Edge := entries[i.val]'(by rw [entries_length]; exact i.isLt)
def number (i : Control) : Nat := i.val+1
def sourcePC (i : Control) : Nat := bitsNat (source i).1
theorem source_leaf (i : Control) : LeafAt KSource215.t215 (source i).1 (source i).2 :=
  leafEntries_sound _ _ _ (List.getElem_mem _)
theorem source_length (i : Control) : (source i).1.length≤48 := ArithmeticSite215.source_length (source_leaf i)
theorem source_not_node (i : Control) (r : Nat) : (source i).2≠.node r := by
  intro h
  exact ArithmeticSite215.source_not_node (h ▸ source_leaf i)

private theorem leaf_walk {t : Tree} {P : List Bool} {e : Edge} (h : LeafAt t P e) :
    ∀ n, twalk t P n=some (e,n+P.length) := by
  induction h with
  | here e => intro n; simp [twalk]
  | left h ih => intro n; simpa only [twalk,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (n+1)
  | right h ih => intro n; simpa only [twalk,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (n+1)
theorem source_walk (i : Control) :
    walk KSource215.p215 (KSource215.p215.nnodes+1) KSource215.p215.root (source i).1 0=
      some ((source i).2,(source i).1.length) := by
  rw [walk_root,KSource215.t215_eq]
  simpa only [Nat.zero_add] using leaf_walk (source_leaf i) 0
theorem source_follow (i : Control) :
    follow KSource215.p215 (.node KSource215.p215.root) (source i).1=some (source i).2 := by
  simpa only [consume,List.take_append_length] using
    walk_follow_consume KSource215.p215 _ _ _ (source_walk i)

theorem table_row_at (i : Control) : table215[i.val]?=some (rowOf KSource215.t215 (source i)) := by
  rw [table215_eq_catalogue]
  have hi : i.val<(leafEntries KSource215.t215).length := by
    change i.val<entries.length
    rw [entries_length]
    exact i.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,source,entries]
theorem rows_at (i : Control) : rows215 (number i)=some (rowOf KSource215.t215 (source i)) := by
  have hi : i.val<count := i.isLt
  have h:=table_row_at i
  simp only [table215,PackedTables.table,List.getElem?_ofFn,dif_pos hi,Option.some.injEq] at h
  unfold rows215 PackedTables.rowsOf
  rw [if_neg (show ¬(number i=0 ∨ count<number i) by unfold number; change ¬(i.val+1=0 ∨ 4751<i.val+1); omega)]
  simpa only [number,Nat.add_sub_cancel] using congrArg some h

theorem actual_walk_exists (P : List Bool) :
    ∃ e d, walk KSource215.p215 (KSource215.p215.nnodes+1) KSource215.p215.root P 0=some (e,d) :=
  allSites_walk_total _ _ _ rfl KSites215.all_sites P
private theorem rank_lt (P : List Bool) : crank (annotate KSource215.t215) P<4751 := by
  obtain ⟨e,d,hw⟩:=actual_walk_exists P
  rw [walk_root,KSource215.t215_eq] at hw
  obtain ⟨hr,_⟩:=entry_at_crank KSource215.t215 P 0 e d hw
  change crank (annotate KSource215.t215) P<entries.length at hr
  rwa [entries_length] at hr
def resolveControl (P : List Bool) : Control := ⟨crank (annotate KSource215.t215) P,rank_lt P⟩
theorem resolve_source (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk KSource215.p215 (KSource215.p215.nnodes+1) KSource215.p215.root P 0=some (e,d)) :
    source (resolveControl P)=(consume P d,e) := by
  rw [walk_root,KSource215.t215_eq] at hw
  obtain ⟨_,he⟩:=entry_at_crank KSource215.t215 P 0 e d hw
  simpa only [source,entries,resolveControl,Nat.sub_zero] using he
def nextControl (i : Control) (positive : Bool) : Nat :=
  successorOf KSource215.t215 (source i).1 (source i).2 positive
theorem next_number (i : Control) (positive : Bool) (hn : (source i).2≠.halt) :
    nextControl i positive=number (resolveControl (outgoingPathOf (source i).1 (source i).2 positive)) := by
  cases he : (source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | halt => exact False.elim (hn he)
  | inc r | decnz r | brk r | cont r => simp only [nextControl,successorOf,he,number,resolveControl]

def physical (i : Control) : Fin 9 := ⟨registerOf (source i).2,registerOf_lt _⟩
theorem physical_map : ∀ r : Fin 9, Permutation252Frame.physOf r.val=KSim.physOf r.val := by decide +kernel
theorem physical_inc (i : Control) (r : Nat) (he : (source i).2=.inc r) :
    KSim.physOf r=(physical i).val := by
  have hl : LeafAt KSource215.t215 (source i).1 (.inc r) := he ▸ source_leaf i
  have hr:=(ArithmeticSite215.source_inc_bounds hl).1
  simpa only [physical,he,registerOf] using (physical_map ⟨r,hr⟩).symm
theorem physical_decnz (i : Control) (r : Nat) (he : (source i).2=.decnz r) :
    KSim.physOf r=(physical i).val := by
  have hl : LeafAt KSource215.t215 (source i).1 (.decnz r) := he ▸ source_leaf i
  have hr:=(ArithmeticSite215.source_decnz_bounds hl).1
  simpa only [physical,he,registerOf] using (physical_map ⟨r,hr⟩).symm

def pcRows : List (Nat × Nat) := List.ofFn fun i : Control => (sourcePC i,sourcePC i)
def pcDef : 𝚺₀.Semisentence 2 := .mkSigma “out q. !(lookupDef (compactRows 0 pcRows)) out q 0”
def blockDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out value suffix. ∃ bits, !(bitPrefixDef true) bits (value+1) suffix ∧ out=2*bits”
def blocksDef : List (Fin 9) → 𝚺₁.Semisentence 3
  | [] => .mkSigma “out file suffix. out=suffix”
  | p::ps => .mkSigma
      “out file suffix. ∃ tail, !(blocksDef ps) tail file suffix ∧
        ∃ value, !(projectionDef 8 p) value file ∧ !blockDef out value tail”
def spareDef : 𝚺₁.Semisentence 2 := .mkSigma “out k. !repeat3Def out k 6 0”
def entryDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out q file k gap. ∃ pc, !pcDef pc q ∧ ∃ spares, !spareDef spares k ∧
    ∃ blocks, !(blocksDef (List.finRange 9)) blocks file spares ∧
    ∃ gapBits, !(bitPrefixDef false) gapBits gap (2*blocks+1) ∧
    ∃ pcBits, !(bitPrefixDef false) pcBits 64 gapBits ∧
    ∃ tape, !ArithmeticCantor.pairDef tape 1 (pc+pcBits) ∧ !ArithmeticCantor.pairDef out 24 tape”

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def pcValue (q : V) : V := lookupValue (compactRows 0 pcRows) q 0
noncomputable def blocksValue : List (Fin 9) → V → V → V
  | [],_,suffix => suffix
  | p::ps,f,suffix => block (regValue f p) (blocksValue ps f suffix)
noncomputable def spareValue (k : V) : V := repeat3 6 k 0
noncomputable def entryValue (q f k gap : V) : V :=
  frameSparse 84 1 (pcValue q+bitPrefix false 64
    (bitPrefix false gap (2*blocksValue (List.finRange 9) f (spareValue k)+1)))
instance pc_defined : 𝚺₀-Function₁[V] pcValue via pcDef :=
  .mk fun e => by simp [pcDef,pcValue]
instance block_defined : 𝚺₁-Function₂[V] block via blockDef :=
  .mk fun e => by simp [blockDef,block]
instance blocks_defined (ps : List (Fin 9)) : 𝚺₁-Function₂[V] (blocksValue ps) via blocksDef ps := by
  induction ps with
  | nil => exact .mk fun e => by simp [blocksDef,blocksValue]
  | cons p ps ih => exact .mk fun e => by simp [blocksDef,blocksValue,regValue,(projection_defined 8 p).iff,ih.iff]
instance spare_defined : 𝚺₁-Function₁[V] spareValue via spareDef :=
  .mk fun e => by simp [spareDef,spareValue,repeatValue,numeral_eq_natCast]
instance entry_defined : 𝚺₁-Function₄[V] entryValue via entryDef :=
  .mk fun e => by simp [entryDef,entryValue,frameSparse,sparseCode_dispatch,numeral_eq_natCast]
instance pc_delta : 𝚫₁-Function₁[V] pcValue := pc_defined.to_definable.of_zero
instance block_delta : 𝚫₁-Function₂[V] block := block_defined.graph_delta.to_definable
instance blocks_delta (ps : List (Fin 9)) : 𝚫₁-Function₂[V] (blocksValue ps) :=
  (blocks_defined ps).graph_delta.to_definable
instance spare_delta : 𝚫₁-Function₁[V] spareValue := spare_defined.graph_delta.to_definable
instance entry_delta : 𝚫₁-Function₄[V] entryValue := entry_defined.graph_delta.to_definable
instance entry_definable : 𝚺₁-Function₄[V] entryValue := entry_defined.to_definable

theorem blocks_list (ps : List (Fin 9)) (f suffix : V) :
    blocksValue ps f suffix=ArithmeticRegisterBoxes215.file (ps.map (regValue f)) suffix := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [blocksValue,List.map_cons,ArithmeticRegisterBoxes215.file,ih]
theorem blocks_plain (f k : V) : blocksValue (List.finRange 9) f (spareValue k)=plain (regValue f) k := by
  rw [blocks_list,plain,List.ofFn_eq_map]
  rfl
theorem pc_at (i : Control) : pcValue (V:=V) (number i : V)=binaryValue (source i).1 := by
  have h:=compact_lookup_at (V:=V) pcRows 0 i.val (by simpa only [pcRows,List.length_ofFn] using i.isLt) 0
  rw [binaryValue_cast]
  simpa only [pcValue,pcRows,number,sourcePC,Nat.zero_add,List.getElem_ofFn,ite_self] using h
theorem entry_format (i : Control) (f k gap : V) :
    entryValue (number i : V) f k gap=frameSparse 84 1
      (binaryValue (source i).1+bitPrefix false 64 (bitPrefix false gap (2*plain (regValue f) k+1))) := by
  rw [entryValue,pc_at,blocks_plain]
theorem entry_active (q f k gap : V) : first (entryValue q f k gap)=(24:V) := by
  simp only [entryValue,frameSparse,first_cantor,sparseCode_dispatch,Nat.cast_ofNat]

theorem path_append (P Q : List Bool) (z : V) : pathValue (P++Q) z=pathValue P (pathValue Q z) := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [List.cons_append,pathValue,ih]
theorem path_replicate (n : Nat) (z : V) : pathValue (List.replicate n false) z=bitPrefix false (n:V) z := by
  induction n with
  | zero => simp only [List.replicate_zero,pathValue,Nat.cast_zero,bitPrefix_zero]
  | succ n ih => simp only [List.replicate_succ,pathValue,ih,Nat.cast_succ,bitPrefix_succ]
theorem path_affine (P : List Bool) (z : V) :
    pathValue P z=binaryValue P+bitPrefix false (P.length:V) z := by
  induction P with
  | nil => simp [pathValue,binaryValue]
  | cons b P ih =>
      rw [pathValue,ih,List.length_cons,Nat.cast_succ,bitPrefix_succ]
      cases b <;> simp only [binaryValue,digit,Bool.false_eq_true,if_false,if_true] <;> ring
theorem start_source (i : Control) (f k gap : V) :
    ArithmeticSite215.startValue gap (regValue f) k (source i).1=entryValue (number i : V) f k gap := by
  have hn : (source i).1.length+(64-(source i).1.length)=64 := Nat.add_sub_of_le (by have:=source_length i; omega)
  have hv : ((source i).1.length:V)+(gap+((64-(source i).1.length:Nat):V))=(64:V)+gap := by
    calc
      _=(((source i).1.length+(64-(source i).1.length):Nat):V)+gap := by rw [Nat.cast_add]; ring
      _=_ := by rw [hn]; rfl
  rw [ArithmeticSite215.start_format,path_affine,←bitPrefix_add,hv,bitPrefix_add,entry_format]

theorem values_write (f value : V) (r : Fin 9) :
    regValue (write r value f)=Function.update (regValue f) r value := by
  funext p
  by_cases h:r=p
  · subst p; simp only [reg_write_same,Function.update_self]
  · rw [reg_write_other r p value f h,Function.update_of_ne (fun hp => h hp.symm)]

theorem opcode_at (i : Control) : opcodeValue table215 (number i : V)=(edgeOpcode (source i).2:V) := by
  have hi:i.val<table215.length := by rw [table215_length]; exact i.isLt
  have h:=table_row_at i
  rw [List.getElem?_eq_getElem hi,Option.some.injEq] at h
  rw [show (number i:V)=((i.val+1:Nat):V) from rfl,opcodeValue_at i.val hi,h]
  rfl
theorem opcode_nonzero (i : Control) : opcodeValue table215 (number i : V)≠0 := by
  rw [opcode_at]
  cases he:(source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r | decnz r | brk r | cont r | halt => simp [edgeOpcode]
theorem opcode_supported (q : V) (hq:opcodeValue table215 q≠0) :
    ∃ i:Control,q=(number i:V) := by
  obtain ⟨i,hi,he⟩:=compact_lookup_supported (V:=V) (opRows table215) 0 q 0 hq
  have hi':i<4751 := by simpa only [opRows,List.length_map,table215_length] using hi
  exact ⟨⟨i,hi'⟩,by simpa only [number,Nat.zero_add] using he⟩

end Model

def padded (P : List Bool) (N : Nat) : List Bool := P++List.replicate (N-P.length) false
def budget (overflow : Bool) (extra : Nat) : Nat := 64+overflow.toNat+extra
theorem outgoing_length (Q : List Bool) (e : Edge) (positive : Bool) :
    (outgoingPathOf Q e positive).length≤Q.length := by
  cases e with
  | node _ | halt => exact Nat.le_refl _
  | inc _ => exact le_of_eq (KSim.incPath_length Q)
  | decnz _ =>
      cases positive <;> simp only [outgoingPathOf,Bool.false_eq_true,if_false,if_true]
      · exact KSim.breakPath_length 1 Q
      · exact le_of_eq (KSim.incPath_length Q)
  | brk j => exact KSim.breakPath_length j Q
  | cont j => exact KSim.stripPath_length true j Q

theorem outgoing_clean (i : Control) (positive : Bool) (hn : (source i).2≠.halt) :
    Clean KSource215.p215 (outgoingPathOf (source i).1 (source i).2 positive) := by
  have hf:=source_follow i
  cases he:(source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | halt => exact False.elim (hn he)
  | inc r =>
      exact execute_clean KSource215.p215 (.inc r) (source i).1 (fun _=>0)
        ⟨incPath (source i).1,update (fun _=>0) r 1⟩ (by simpa only [he] using hf) rfl
  | decnz r =>
      cases positive
      · exact execute_clean KSource215.p215 (.decnz r) (source i).1 (fun _=>0)
          ⟨breakPath 1 (source i).1,fun _=>0⟩ (by simpa only [he] using hf) rfl
      · exact execute_clean KSource215.p215 (.decnz r) (source i).1 (fun _=>1)
          ⟨incPath (source i).1,update (fun _=>1) r 0⟩ (by simpa only [he] using hf) rfl
  | brk j =>
      exact execute_clean KSource215.p215 (.brk j) (source i).1 (fun _=>0)
        ⟨breakPath j (source i).1,fun _=>0⟩ (by simpa only [he] using hf) rfl
  | cont j =>
      exact execute_clean KSource215.p215 (.cont j) (source i).1 (fun _=>0)
        ⟨continuePath j (source i).1,fun _=>0⟩ (by simpa only [he] using hf) rfl

/-- Both lists have the same whole finite budget, including implicit zeros. -/
theorem resolved_padded (P : List Bool) (overflow : Bool) (extra : Nat)
    (hP:P.length≤64) (hc:Clean KSource215.p215 P) :
    padded P (budget overflow extra)=padded (source (resolveControl P)).1 (budget overflow extra) := by
  obtain ⟨e,d,hw⟩:=actual_walk_exists P
  have hs:=allSites_walk _ _ _ rfl KSites215.all_sites P e d hw
  have hd:d≤48 := by simpa only [consume_length] using KSim.checkEdge_length hs
  have hz:∀ b∈P.drop d,b=false := by
    intro b hb
    obtain ⟨j,hj⟩:=List.mem_iff_getElem?.mp hb
    have hv:bit (P.drop d) j=b := by simp [bit,hj]
    exact hv.symm.trans ((bit_drop P d j).trans (hc e d hw (d+j) (by omega)))
  have hn:64≤budget overflow extra := by unfold budget; omega
  have he:=gap_consume P (budget overflow extra-P.length) d (by omega) hz
  have hh:P.length+(budget overflow extra-P.length)=budget overflow extra := by omega
  rw [resolve_source P e d hw]
  simpa only [padded,consume_length,hh] using he

section Rebase
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def pathTarget (P : List Bool) (overflow : Bool) (extra : Nat) (gap header : V) : V :=
  frameSparse 84 1 (pathValue P (bitPrefix false (gap+((budget overflow extra-P.length:Nat):V)) header))
theorem padded_prefix (P : List Bool) (N : Nat) (gap header : V) :
    pathValue P (bitPrefix false (gap+((N-P.length:Nat):V)) header)=
      pathValue (padded P N) (bitPrefix false gap header) := by
  rw [padded,path_append,path_replicate,←bitPrefix_add,add_comm gap]
theorem target_rebase (P Q : List Bool) (overflow : Bool) (extra : Nat)
    (gap header : V) (hQ:Q.length≤64)
    (hp:padded P (budget overflow extra)=padded Q (budget overflow extra)) :
    pathTarget P overflow extra gap header=frameSparse 84 1
      (pathValue Q (bitPrefix false (gap+digit overflow+(extra:V)+((64-Q.length:Nat):V)) header)) := by
  have hn:budget overflow extra-Q.length=overflow.toNat+extra+(64-Q.length) := by unfold budget; omega
  rw [pathTarget,padded_prefix,hp,←padded_prefix,hn,Nat.cast_add,Nat.cast_add,digit_cast]
  congr 3
  ring
theorem target_entry (P : List Bool) (overflow : Bool) (extra : Nat) (f k gap : V)
    (hP:P.length≤64) (hc:Clean KSource215.p215 P) :
    pathTarget P overflow extra gap (2*plain (regValue f) k+1)=
      entryValue (number (resolveControl P):V) f k (gap+digit overflow+(extra:V)) := by
  have hq:(source (resolveControl P)).1.length≤64 := by have:=source_length (resolveControl P); omega
  rw [target_rebase P _ overflow extra gap _ hq (resolved_padded P overflow extra hP hc)]
  exact (ArithmeticSite215.start_format (gap+digit overflow+(extra:V)) (regValue f) k _).symm.trans
    (start_source (resolveControl P) f k _)
theorem target_next_entry (i : Control) (positive overflow : Bool) (extra : Nat) (f k gap : V)
    (hn:(source i).2≠.halt) :
    pathTarget (outgoingPathOf (source i).1 (source i).2 positive) overflow extra gap
      (2*plain (regValue f) k+1)=entryValue (nextControl i positive:V) f k (gap+digit overflow+(extra:V)) := by
  rw [next_number i positive hn]
  exact target_entry _ overflow extra f k gap
    (le_trans (outgoing_length _ _ _) (by have:=source_length i; omega)) (outgoing_clean i positive hn)
theorem plain_target (gap f k : V) (P : List Bool) (overflow : Bool) :
    ArithmeticSite215.targetValue gap (regValue f) k P overflow (.plain .none)=
      pathTarget P overflow 0 gap (2*plain (regValue f) k+1) := by
  rw [ArithmeticSite215.target_format,box_plain]
  cases overflow <;> rfl

/-- The actual four-field instruction, specialized through the accepted spec. -/
theorem step_at (i : Control) (f : V) :
    stepValue table215 (liveValue (number i:V) f)=ArithmeticControlBisim.sem regValue write liveValue
      ⟨edgeOpcode (source i).2,physical i,nextControl i false,nextControl i true⟩ f :=
  spec215 (number i) (rowOf KSource215.t215 (source i)) f (rows_at i)
theorem step_inc (i : Control) (r : Nat) (he:(source i).2=.inc r) (f : V) :
    stepValue table215 (liveValue (number i:V) f)=
      liveValue (nextControl i false:V) (write (physical i) (regValue f (physical i)+1) f) := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,if_true]
theorem step_decnz_zero (i : Control) (r : Nat) (he:(source i).2=.decnz r) (f : V)
    (hz:regValue f (physical i)=0) :
    stepValue table215 (liveValue (number i:V) f)=liveValue (nextControl i false:V) f := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (2:Nat)≠1 by decide,if_false,if_true,hz]
theorem step_decnz_positive (i : Control) (r : Nat) (he:(source i).2=.decnz r) (f : V)
    (hn:regValue f (physical i)≠0) :
    stepValue table215 (liveValue (number i:V) f)=
      liveValue (nextControl i true:V) (write (physical i) (regValue f (physical i)-1) f) := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (2:Nat)≠1 by decide,if_false,if_true,hn]
theorem step_break (i : Control) (j : Nat) (he:(source i).2=.brk j) (f : V) :
    stepValue table215 (liveValue (number i:V) f)=liveValue (nextControl i false:V) f := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (3:Nat)≠1 by decide,
    show (3:Nat)≠2 by decide,if_false,if_true]
theorem step_continue (i : Control) (j : Nat) (he:(source i).2=.cont j) (f : V) :
    stepValue table215 (liveValue (number i:V) f)=liveValue (nextControl i false:V) f := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (3:Nat)≠1 by decide,
    show (3:Nat)≠2 by decide,if_false,if_true]
theorem step_halt (i : Control) (he:(source i).2=.halt) (f : V) :
    stepValue table215 (liveValue (number i:V) f)=0 := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (4:Nat)≠1 by decide,
    show (4:Nat)≠2 by decide,show (4:Nat)≠3 by decide,if_false]

theorem entry_inc (i : Control) (r : Nat) (he:(source i).2=.inc r) (f k gap : V) (hk:0<k) :
    ReachPos (entryValue (number i:V) f k gap)
      (entryValue (nextControl i false:V) (write (physical i) (regValue f (physical i)+1) f)
        (k+1) (gap+digit (KSim.allOnes (source i).1))) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.inc r) := he ▸ source_leaf i
  obtain ⟨t,ht,hv⟩:=ArithmeticSite215.source_inc gap (regValue f) k hk hl
  rw [start_source,physical_inc i r he,ArithmeticSite215.increment_target,←values_write,plain_target] at hv
  have hh:=target_next_entry i false (KSim.allOnes (source i).1) 0
    (write (physical i) (regValue f (physical i)+1) f) (k+1) gap (by rw [he]; intro h; cases h)
  exact ⟨t,ht,hv.trans (by simpa only [he,outgoingPathOf,Nat.cast_zero,add_zero] using hh)⟩
theorem entry_decnz_zero (i : Control) (r : Nat) (he:(source i).2=.decnz r) (f k gap : V)
    (hk:0<k) (hz:regValue f (physical i)=0) :
    ReachPos (entryValue (number i:V) f k gap)
      (entryValue (nextControl i false:V) f k
        (gap+digit (KSim.allOnes (stripPath false 1 (source i).1)))) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.decnz r) := he ▸ source_leaf i
  have hz':getValue (regValue f) (KSim.physOf r)=0 := by
    rw [physical_decnz i r he]
    simpa only [getValue,dif_pos (physical i).isLt] using hz
  obtain ⟨t,ht,hv⟩:=ArithmeticSite215.source_decnz_zero gap (regValue f) k hk hl hz'
  rw [start_source,plain_target] at hv
  have hh:=target_next_entry i false (KSim.allOnes (stripPath false 1 (source i).1)) 0 f k gap
    (by rw [he]; intro h; cases h)
  exact ⟨t,ht,hv.trans (by simpa only [he,outgoingPathOf,Bool.false_eq_true,if_false,Nat.cast_zero,add_zero] using hh)⟩
theorem entry_decnz_positive (i : Control) (r : Nat) (he:(source i).2=.decnz r) (f k gap : V)
    (hk:0<k) (hn:regValue f (physical i)≠0) :
    ReachPos (entryValue (number i:V) f k gap)
      (entryValue (nextControl i true:V) (write (physical i) (regValue f (physical i)-1) f)
        k (gap+digit (KSim.allOnes (source i).1)+1)) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.decnz r) := he ▸ source_leaf i
  have hn':getValue (regValue f) (KSim.physOf r)≠0 := by
    rw [physical_decnz i r he]
    simpa only [getValue,dif_pos (physical i).isLt] using hn
  obtain ⟨t,ht,hv⟩:=ArithmeticSite215.source_decnz_positive gap (regValue f) k hk hl hn'
  rw [start_source,physical_decnz i r he,ArithmeticSite215.decrement_target,←values_write] at hv
  have hh:=target_next_entry i true (KSim.allOnes (source i).1) 1
    (write (physical i) (regValue f (physical i)-1) f) k gap (by rw [he]; intro h; cases h)
  refine ⟨t,ht,hv.trans ?_⟩
  simpa only [he,outgoingPathOf,if_true,pathTarget,budget,Nat.cast_one,
    show ∀ b:Bool,(if b then 1 else 0:Nat)=b.toNat by intro b; cases b <;> rfl] using hh
theorem entry_break (i : Control) (j : Nat) (he:(source i).2=.brk j) (f k gap : V) (hk:0<k) :
    ReachPos (entryValue (number i:V) f k gap)
      (entryValue (nextControl i false:V) f k (gap+digit (KSim.allOnes (stripPath false j (source i).1)))) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.brk j) := he ▸ source_leaf i
  obtain ⟨t,ht,hv⟩:=ArithmeticSite215.source_break gap (regValue f) k hk hl
  rw [start_source,plain_target] at hv
  have hh:=target_next_entry i false (KSim.allOnes (stripPath false j (source i).1)) 0 f k gap
    (by rw [he]; intro h; cases h)
  exact ⟨t,ht,hv.trans (by simpa only [he,outgoingPathOf,Nat.cast_zero,add_zero] using hh)⟩
theorem entry_continue (i : Control) (j : Nat) (he:(source i).2=.cont j) (f k gap : V) (hk:0<k) :
    ReachPos (entryValue (number i:V) f k gap) (entryValue (nextControl i false:V) f k gap) := by
  have hl:LeafAt KSource215.t215 (source i).1 (.cont j) := he ▸ source_leaf i
  obtain ⟨t,ht,hv⟩:=ArithmeticSite215.source_continue gap (regValue f) k hk hl
  rw [start_source,plain_target] at hv
  have hh:=target_next_entry i false false 0 f k gap (by rw [he]; intro h; cases h)
  exact ⟨t,ht,hv.trans (by simpa only [he,outgoingPathOf,digit_false,Nat.cast_zero,add_zero] using hh)⟩
theorem entry_source_halt (i : Control) (he:(source i).2=.halt) (f k gap : V) (hk:0<k) :
    ∃ t:V,0<t ∧ first (runFrom t (entryValue (number i:V) f k gap))=0 := by
  have hl:LeafAt KSource215.t215 (source i).1 .halt := he ▸ source_leaf i
  simpa only [start_source] using ArithmeticSite215.source_halt gap (regValue f) k hk hl

theorem step_nonzero (i : Control) (f : V) (hh:(source i).2≠.halt) :
    stepValue table215 (liveValue (number i:V) f)≠0 := by
  cases he:(source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r => rw [step_inc i r he]; exact live_ne_zero _ _
  | decnz r =>
      by_cases hz:regValue f (physical i)=0
      · rw [step_decnz_zero i r he f hz]; exact live_ne_zero _ _
      · rw [step_decnz_positive i r he f hz]; exact live_ne_zero _ _
  | brk j => rw [step_break i j he]; exact live_ne_zero _ _
  | cont j => rw [step_continue i j he]; exact live_ne_zero _ _
  | halt => exact False.elim (hh he)

/-- A valid next canonical entry and its positive clock are derived, not supplied. -/
theorem entry_step (i : Control) (f k gap : V) (hk:0<k)
    (hn:stepValue table215 (liveValue (number i:V) f)≠0) :
    ∃ j:Control,∃ f' k' gap':V,0<k' ∧
      stepValue table215 (liveValue (number i:V) f)=liveValue (number j:V) f' ∧
      ReachPos (entryValue (number i:V) f k gap) (entryValue (number j:V) f' k' gap') := by
  have finish : ∀ (positive:Bool) (f' k' gap':V), (source i).2≠.halt → 0<k' →
      stepValue table215 (liveValue (number i:V) f)=liveValue (nextControl i positive:V) f' →
      ReachPos (entryValue (number i:V) f k gap) (entryValue (nextControl i positive:V) f' k' gap') →
      ∃ j:Control,∃ f' k' gap':V,0<k' ∧
        stepValue table215 (liveValue (number i:V) f)=liveValue (number j:V) f' ∧
        ReachPos (entryValue (number i:V) f k gap) (entryValue (number j:V) f' k' gap') := by
    intro positive f' k' gap' hh hk' hs hr
    rw [next_number i positive hh] at hs hr
    exact ⟨_,f',k',gap',hk',hs,hr⟩
  cases he:(source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r =>
      exact finish false _ (k+1) _ (by rw [he]; intro h; cases h)
        (lt_of_lt_of_le hk (by simp)) (step_inc i r he f) (entry_inc i r he f k gap hk)
  | decnz r =>
      by_cases hz:regValue f (physical i)=0
      · exact finish false f k _ (by rw [he]; intro h; cases h) hk
          (step_decnz_zero i r he f hz) (entry_decnz_zero i r he f k gap hk hz)
      · exact finish true _ k _ (by rw [he]; intro h; cases h) hk
          (step_decnz_positive i r he f hz) (entry_decnz_positive i r he f k gap hk hz)
  | brk j =>
      exact finish false f k _ (by rw [he]; intro h; cases h) hk
        (step_break i j he f) (entry_break i j he f k gap hk)
  | cont j =>
      exact finish false f k gap (by rw [he]; intro h; cases h) hk
        (step_continue i j he f) (entry_continue i j he f k gap hk)
  | halt => exact False.elim (hn (step_halt i he f))
theorem entry_halt (i : Control) (f k gap : V) (hk:0<k)
    (hz:stepValue table215 (liveValue (number i:V) f)=0) :
    ∃ t:V,0<t ∧ first (runFrom t (entryValue (number i:V) f k gap))=0 := by
  have he:(source i).2=.halt := by
    by_contra hn
    exact step_nonzero i f hn hz
  exact entry_source_halt i he f k gap hk
end Rebase
end DiophantineConsistency.ArithmeticControlFrame215
