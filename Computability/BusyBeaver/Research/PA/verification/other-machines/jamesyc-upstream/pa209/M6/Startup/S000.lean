module
public import M6.Startup.Data
@[expose] public section
namespace M6.Startup
open M6.Zip
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem run0000 : run Literal.machine 128 c0000 = some c0001 := by decide +kernel
theorem run0001 : run Literal.machine 128 c0001 = some c0002 := by decide +kernel
theorem run0002 : run Literal.machine 128 c0002 = some c0003 := by decide +kernel
theorem run0003 : run Literal.machine 128 c0003 = some c0004 := by decide +kernel
theorem run0004 : run Literal.machine 128 c0004 = some c0005 := by decide +kernel
theorem run0005 : run Literal.machine 128 c0005 = some c0006 := by decide +kernel
theorem run0006 : run Literal.machine 128 c0006 = some c0007 := by decide +kernel
theorem run0007 : run Literal.machine 128 c0007 = some c0008 := by decide +kernel
theorem run0008 : run Literal.machine 128 c0008 = some c0009 := by decide +kernel
theorem run0009 : run Literal.machine 128 c0009 = some c0010 := by decide +kernel
theorem run0010 : run Literal.machine 128 c0010 = some c0011 := by decide +kernel
theorem run0011 : run Literal.machine 128 c0011 = some c0012 := by decide +kernel
end M6.Startup
