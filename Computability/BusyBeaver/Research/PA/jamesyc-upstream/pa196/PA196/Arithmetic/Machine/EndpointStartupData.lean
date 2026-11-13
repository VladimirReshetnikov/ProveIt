module
public import PA196.Arithmetic.Machine.EndpointZipNatTape
public import PA196.Startup
public import PA196.Conjugacy
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA196.Arithmetic.Machine.PA.Startup
/-- Exact corrected complete physical file, including all 26 one-valued spares. -/
abbrev startupFile := PA196.Startup.physicalFile
def nativeFrame := PA196.Conjugacy.mapConf PA196.Startup.clean
def finalConfig := ZipNatTape.encode nativeFrame
theorem final_control : finalConfig.control=target 81 := by decide +kernel
theorem final_left : finalConfig.left=1 := by decide +kernel
theorem full_file_length : startupFile.length=35 := by decide +kernel
/-- Lifts the already kernel-checked exact 58,154-step literal startup. -/
theorem blank_run_58154 : NatTape.run 58154 NatTape.blank=some finalConfig := by
  have h : M6.Zip.run PA196.Table.machine 58154
      (PA196.Conjugacy.mapConf PA196.Startup.blank)=some nativeFrame := by
    rw [PA196.Conjugacy.run_conjugate 58154 _ (by decide),PA196.Startup.startup_exact]
    rfl
  have hh := ZipNatTape.run_forward 58154 _ _ h
  have hb : ZipNatTape.encode (PA196.Conjugacy.mapConf PA196.Startup.blank)=NatTape.blank := by decide +kernel
  rw [hb] at hh
  exact hh
#print axioms blank_run_58154
end PA196.Arithmetic.Machine.PA.Startup
