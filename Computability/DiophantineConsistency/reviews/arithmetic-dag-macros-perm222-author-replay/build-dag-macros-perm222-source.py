from pathlib import Path
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
lib=(B/'ArithmeticL2Lib254.lean').read_text();mac=(B/'ArithmeticL2Macros254.lean').read_text();ctl=(B/'ArithmeticL2Control254.lean').read_text()
def chunk(s,a,b):return s[s.index(a):s.index(b)]
header='''import BusyBeaver.ZFC.ArithmeticDagControlPerm222

/-! Actual DagPerm data and formula-macro executions over arbitrary internal
IΣ1 values. The physical file is fixed, and every execution is proved for the
accepted actual table. Pairing/unpairing and macro algebra adapt the inspected
ArithmeticL2Lib254/ArithmeticL2Macros254 proof text; their old fixed-interpreter
semantic modules are not imported or invoked. Generic transfer/copy/clear loops
are reused from ArithmeticDagLoops. This file does not prove equality123,
dispatch/root execution, a 215 tape simulation, or a source/HA endpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagMacrosPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun ArithmeticDagControlPerm222 RMDag
open ArithmeticControlFile (regValue fileValue writeValue liveValue reg_file file_reg reg_write
  write_defined live_defined)
open ArithmeticControlTable (write reg_write_same reg_write_other file_ext)
open ArithmeticCode254 (wim wel wal weq tagged)
open ArithmeticDagLoops (one_le_of_pos)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
'''
base=chunk(lib,'/-! ## The nine registers -/','/-! ## The three loop shapes -/')
base=base.replace('Dag254.dag254','DagPerm.dagPerm').replace('DagControl254','ArithmeticDagControlPerm222').replace('`Dag254`','`DagPerm`').replace('dag254','actual DagPerm')
# Scope only macro constructors; unused halt/outer break wrappers omitted.
for name,nextname in [('halt','variable {n'),('halt_car','theorem halt_cdr'),('halt_cdr','theorem brk_cdr'),('brk_car','theorem cont_car')]:
 start=base.index('theorem '+name+' ');end=base.index(nextname,start);base=base[:start]+base[end:]
setup='''
local instance run_definable : 𝚺₁-Function₂[V] (ArithmeticDagControlPerm222.run (V := V)) :=
  ArithmeticControlTable.controlRun_definable table
local instance write_definable : 𝚺₁-Function₃[V] writeValue := write_defined.to_definable

'''
instances=chunk(lib,'/-! ## Loop instances (as in `L2Lib254`) -/','/-! ## Pairing -/')
# Retain only loop instances genuinely used below.
for name in ['loop197','loop192','loop199','loop214']:
 start=instances.index('theorem '+name+' ');comment=instances.rfind('/--',0,start)
 end=instances.find('\n/--',start)
 if end<0:end=len(instances)
 instances=instances[:comment]+instances[end:]
instances=instances.replace('have h := transfer ', 'have h := ArithmeticDagLoops.transfer R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec ')
instances=instances.replace('have h := copy2 ', 'have h := ArithmeticDagLoops.copy2 R.run_zero R.run_add R.run_one ArithmeticDagControlPerm222.spec ')
pair=chunk(lib,'/-! ## Pairing -/','end SetTheory.BusyBeaver.ZFC.ArithmeticL2')
macros=chunk(mac,'/-- Negation relative to the falsity code `1`. -/','end SetTheory.BusyBeaver.ZFC.ArithmeticL2')
fetch=chunk(ctl,'/-- The fetch (node 133):','/-- The MP branch (node 150). -/')
source=header+base+setup+instances+pair+'\n/-! ## Actual formula and stack macros -/\n'+macros+'\n/-! ## Actual fetch -/\n'+fetch+'\nend SetTheory.BusyBeaver.ZFC.ArithmeticDagMacrosPerm222\n'
# Correct inherited historical comment labels.
source=source.replace('Loop instances (as in `L2Lib254`)','Concrete needed DagPerm loop instances').replace('node_110','node160').replace('node_108','node158')
(B/'ArithmeticDagMacrosPerm222.lean').write_text(source)
print(len(source.splitlines()))
