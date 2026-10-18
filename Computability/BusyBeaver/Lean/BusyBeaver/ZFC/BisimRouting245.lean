import BusyBeaver.ZFC.BisimRouting245Chunk000
import BusyBeaver.ZFC.BisimRouting245Chunk001
import BusyBeaver.ZFC.BisimRouting245Chunk002
import BusyBeaver.ZFC.BisimRouting245Chunk003
import BusyBeaver.ZFC.BisimRouting245Chunk004
import BusyBeaver.ZFC.BisimRouting245Chunk005
import BusyBeaver.ZFC.BisimRouting245Chunk006
import BusyBeaver.ZFC.BisimRouting245Chunk007
import BusyBeaver.ZFC.BisimRouting245Chunk008
import BusyBeaver.ZFC.BisimRouting245Chunk009
import BusyBeaver.ZFC.BisimRouting245Chunk010
import BusyBeaver.ZFC.BisimRouting245Chunk011
import BusyBeaver.ZFC.BisimRouting245Chunk012
import BusyBeaver.ZFC.BisimRouting245Chunk013
import BusyBeaver.ZFC.BisimRouting245Chunk014
import BusyBeaver.ZFC.BisimRouting245Chunk015
import BusyBeaver.ZFC.BisimRouting245Chunk016
import BusyBeaver.ZFC.BisimRouting245Chunk017
import BusyBeaver.ZFC.BisimRouting245Chunk018
import BusyBeaver.ZFC.BisimRouting245Chunk019
import BusyBeaver.ZFC.BisimRouting245Chunk020
import BusyBeaver.ZFC.BisimRouting245Chunk021
import BusyBeaver.ZFC.BisimRouting245Chunk022
import BusyBeaver.ZFC.BisimRouting245Chunk023
import BusyBeaver.ZFC.BisimRouting245Chunk024
import BusyBeaver.ZFC.BisimRouting245Chunk025
import BusyBeaver.ZFC.BisimRouting245Chunk026
import BusyBeaver.ZFC.BisimRouting245Chunk027
import BusyBeaver.ZFC.BisimRouting245Chunk028
import BusyBeaver.ZFC.BisimRouting245Chunk029
import BusyBeaver.ZFC.BisimRouting245Chunk030
import BusyBeaver.ZFC.BisimRouting245Chunk031
import BusyBeaver.ZFC.BisimRouting245Chunk032
import BusyBeaver.ZFC.BisimRouting245Chunk033
import BusyBeaver.ZFC.BisimRouting245Chunk034
import BusyBeaver.ZFC.BisimRouting245Chunk035
import BusyBeaver.ZFC.BisimRouting245Chunk036
import BusyBeaver.ZFC.BisimRouting245Chunk037
import BusyBeaver.ZFC.BisimRouting245Chunk038
import BusyBeaver.ZFC.BisimRouting245Chunk039
import BusyBeaver.ZFC.BisimRouting245Chunk040
import BusyBeaver.ZFC.BisimRouting245Chunk041
import BusyBeaver.ZFC.BisimRouting245Chunk042
import BusyBeaver.ZFC.BisimRouting245Chunk043
import BusyBeaver.ZFC.BisimRouting245Chunk044
import BusyBeaver.ZFC.BisimRouting245Chunk045
import BusyBeaver.ZFC.BisimRouting245Chunk046
import BusyBeaver.ZFC.BisimRouting245Chunk047
import BusyBeaver.ZFC.BisimRouting245Chunk048
import BusyBeaver.ZFC.BisimRouting245Chunk049
import BusyBeaver.ZFC.BisimRouting245Chunk050
import BusyBeaver.ZFC.BisimRouting245Chunk051
import BusyBeaver.ZFC.BisimRouting245Chunk052
import BusyBeaver.ZFC.BisimRouting245Chunk053
import BusyBeaver.ZFC.BisimRouting245Chunk054
import BusyBeaver.ZFC.BisimRouting245Chunk055
import BusyBeaver.ZFC.BisimRouting245Chunk056
import BusyBeaver.ZFC.BisimRouting245Chunk057
import BusyBeaver.ZFC.BisimRouting245Chunk058
import BusyBeaver.ZFC.BisimRouting245Chunk059
import BusyBeaver.ZFC.BisimRouting245Chunk060
import BusyBeaver.ZFC.BisimRouting245Chunk061
import BusyBeaver.ZFC.BisimRouting245Chunk062
import BusyBeaver.ZFC.BisimRouting245Chunk063
import BusyBeaver.ZFC.BisimRouting245Chunk064
import BusyBeaver.ZFC.BisimRouting245Chunk065
import BusyBeaver.ZFC.BisimRouting245Chunk066
import BusyBeaver.ZFC.BisimRouting245Chunk067
import BusyBeaver.ZFC.BisimRouting245Chunk068
import BusyBeaver.ZFC.BisimRouting245Chunk069
import BusyBeaver.ZFC.BisimRouting245Chunk070
import BusyBeaver.ZFC.BisimRouting245Chunk071
import BusyBeaver.ZFC.BisimRouting245Chunk072
import BusyBeaver.ZFC.BisimRouting245Chunk073
import BusyBeaver.ZFC.BisimRouting245Chunk074
import BusyBeaver.ZFC.BisimRouting245Chunk075
import BusyBeaver.ZFC.BisimRouting245Chunk076
import BusyBeaver.ZFC.BisimRouting245Chunk077
import BusyBeaver.ZFC.BisimRouting245Chunk078
import BusyBeaver.ZFC.BisimRouting245Chunk079
import BusyBeaver.ZFC.BisimRouting245Chunk080
import BusyBeaver.ZFC.BisimRouting245Chunk081
import BusyBeaver.ZFC.BisimRouting245Chunk082
import BusyBeaver.ZFC.BisimRouting245Chunk083
import BusyBeaver.ZFC.BisimRouting245Chunk084
import BusyBeaver.ZFC.BisimRouting245Chunk085
import BusyBeaver.ZFC.BisimRouting245Chunk086
import BusyBeaver.ZFC.BisimRouting245Chunk087
import BusyBeaver.ZFC.BisimRouting245Chunk088
import BusyBeaver.ZFC.BisimRouting245Chunk089
import BusyBeaver.ZFC.BisimRouting245Chunk090
import BusyBeaver.ZFC.BisimRouting245Chunk091
import BusyBeaver.ZFC.BisimRouting245Chunk092
import BusyBeaver.ZFC.BisimRouting245Chunk093
import BusyBeaver.ZFC.BisimRouting245Chunk094

/-! Complete source-program halting equivalence, conditional on no external
coverage premises: all95 exact blocks are assembled structurally below.
This is a source-program theorem, not a binary-machine or PA endpoint. -/
set_option autoImplicit false
namespace SetTheory.BusyBeaver.ZFC.BisimRouting245
open RegisterPath RMBisim

theorem all_ok : allC BisimRouting245Data.test BisimRouting245Data.cert = true := by
  rw [BisimRouting245Data.allC_decomposition]
  simp only [BisimRouting245Chunk000.checked,
    BisimRouting245Chunk001.checked,
    BisimRouting245Chunk002.checked,
    BisimRouting245Chunk003.checked,
    BisimRouting245Chunk004.checked,
    BisimRouting245Chunk005.checked,
    BisimRouting245Chunk006.checked,
    BisimRouting245Chunk007.checked,
    BisimRouting245Chunk008.checked,
    BisimRouting245Chunk009.checked,
    BisimRouting245Chunk010.checked,
    BisimRouting245Chunk011.checked,
    BisimRouting245Chunk012.checked,
    BisimRouting245Chunk013.checked,
    BisimRouting245Chunk014.checked,
    BisimRouting245Chunk015.checked,
    BisimRouting245Chunk016.checked,
    BisimRouting245Chunk017.checked,
    BisimRouting245Chunk018.checked,
    BisimRouting245Chunk019.checked,
    BisimRouting245Chunk020.checked,
    BisimRouting245Chunk021.checked,
    BisimRouting245Chunk022.checked,
    BisimRouting245Chunk023.checked,
    BisimRouting245Chunk024.checked,
    BisimRouting245Chunk025.checked,
    BisimRouting245Chunk026.checked,
    BisimRouting245Chunk027.checked,
    BisimRouting245Chunk028.checked,
    BisimRouting245Chunk029.checked,
    BisimRouting245Chunk030.checked,
    BisimRouting245Chunk031.checked,
    BisimRouting245Chunk032.checked,
    BisimRouting245Chunk033.checked,
    BisimRouting245Chunk034.checked,
    BisimRouting245Chunk035.checked,
    BisimRouting245Chunk036.checked,
    BisimRouting245Chunk037.checked,
    BisimRouting245Chunk038.checked,
    BisimRouting245Chunk039.checked,
    BisimRouting245Chunk040.checked,
    BisimRouting245Chunk041.checked,
    BisimRouting245Chunk042.checked,
    BisimRouting245Chunk043.checked,
    BisimRouting245Chunk044.checked,
    BisimRouting245Chunk045.checked,
    BisimRouting245Chunk046.checked,
    BisimRouting245Chunk047.checked,
    BisimRouting245Chunk048.checked,
    BisimRouting245Chunk049.checked,
    BisimRouting245Chunk050.checked,
    BisimRouting245Chunk051.checked,
    BisimRouting245Chunk052.checked,
    BisimRouting245Chunk053.checked,
    BisimRouting245Chunk054.checked,
    BisimRouting245Chunk055.checked,
    BisimRouting245Chunk056.checked,
    BisimRouting245Chunk057.checked,
    BisimRouting245Chunk058.checked,
    BisimRouting245Chunk059.checked,
    BisimRouting245Chunk060.checked,
    BisimRouting245Chunk061.checked,
    BisimRouting245Chunk062.checked,
    BisimRouting245Chunk063.checked,
    BisimRouting245Chunk064.checked,
    BisimRouting245Chunk065.checked,
    BisimRouting245Chunk066.checked,
    BisimRouting245Chunk067.checked,
    BisimRouting245Chunk068.checked,
    BisimRouting245Chunk069.checked,
    BisimRouting245Chunk070.checked,
    BisimRouting245Chunk071.checked,
    BisimRouting245Chunk072.checked,
    BisimRouting245Chunk073.checked,
    BisimRouting245Chunk074.checked,
    BisimRouting245Chunk075.checked,
    BisimRouting245Chunk076.checked,
    BisimRouting245Chunk077.checked,
    BisimRouting245Chunk078.checked,
    BisimRouting245Chunk079.checked,
    BisimRouting245Chunk080.checked,
    BisimRouting245Chunk081.checked,
    BisimRouting245Chunk082.checked,
    BisimRouting245Chunk083.checked,
    BisimRouting245Chunk084.checked,
    BisimRouting245Chunk085.checked,
    BisimRouting245Chunk086.checked,
    BisimRouting245Chunk087.checked,
    BisimRouting245Chunk088.checked,
    BisimRouting245Chunk089.checked,
    BisimRouting245Chunk090.checked,
    BisimRouting245Chunk091.checked,
    BisimRouting245Chunk092.checked,
    BisimRouting245Chunk093.checked,
    BisimRouting245Chunk094.checked, Bool.and_self]

theorem initial_programs :
    branchOk (ptree Prog254.program) (ptree ProgramRouting245.program)
      BisimRouting245Data.cert [] [] 0 = true := by
  rw [ActualTree254.tree_eq, TreeRouting245.tree_eq]
  exact BisimRouting245Data.initial_ok

theorem all_ok_programs :
    allC (entryOk (ptree Prog254.program) (ptree ProgramRouting245.program)
      BisimRouting245Data.cert) BisimRouting245Data.cert = true := by
  rw [ActualTree254.tree_eq, TreeRouting245.tree_eq]
  exact all_ok

/-- Same arbitrary register function, empty pointers, no execution/value bound. -/
theorem program_halts_iff (R : Registers) :
    Halts ProgramRouting245.program ⟨[], R⟩ ↔ Halts Prog254.program ⟨[], R⟩ :=
  (check_halts_iff initial_programs all_ok_programs R).symm

theorem program_nonhalting_iff (R : Registers) :
    ¬Halts ProgramRouting245.program ⟨[], R⟩ ↔ ¬Halts Prog254.program ⟨[], R⟩ :=
  not_congr (program_halts_iff R)

end SetTheory.BusyBeaver.ZFC.BisimRouting245
