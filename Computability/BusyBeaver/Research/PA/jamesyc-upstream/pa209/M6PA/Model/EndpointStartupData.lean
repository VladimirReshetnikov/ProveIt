module
public import M6PA.Model.EndpointZipNatTape
public import M6.Startup
public import M6.Conjugacy
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Arithmetic.PA.Startup
/-- Exact corrected complete physical file, including all 26 one-valued spares. -/
abbrev startupFile := M6.Startup.physicalFile
def nativeFrame := M6.Conjugacy.mapConf M6.Startup.clean
def finalConfig := ZipNatTape.encode nativeFrame
theorem final_control : finalConfig.control=target 81 := by decide +kernel
theorem final_left : finalConfig.left=1 := by decide +kernel
theorem full_file_length : startupFile.length=35 := by decide +kernel
/-- Lifts the already kernel-checked exact 58,210-step literal startup. -/
theorem blank_run_58210 : NatTape.run 58210 NatTape.blank=some finalConfig := by
  have h : M6.Zip.run M6.Table.machine 58210
      (M6.Conjugacy.mapConf M6.Startup.blank)=some nativeFrame := by
    rw [M6.Conjugacy.run_conjugate 58210 _ (by decide),M6.Startup.startup_exact]
    rfl
  have hh := ZipNatTape.run_forward 58210 _ _ h
  have hb : ZipNatTape.encode (M6.Conjugacy.mapConf M6.Startup.blank)=NatTape.blank := by decide +kernel
  rw [hb] at hh
  exact hh
#print axioms blank_run_58210
end M6.Arithmetic.PA.Startup
