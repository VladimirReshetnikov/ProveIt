import DirectBFSCoverage000
import DirectBFSCoverage001
import DirectBFSCoverage002
import DirectBFSCoverage003
import DirectBFSCoverage004
import DirectBFSCoverage005
import DirectBFSCoverage006
import DirectBFSCoverage007
import DirectBFSCoverage008
import DirectBFSCoverage009
import DirectBFSCoverage010
import DirectBFSCoverage011
import DirectBFSCoverage012
import DirectBFSCoverage013
import DirectBFSCoverage014
import DirectBFSCoverage015
import DirectBFSCoverage016
import DirectBFSCoverage017
import DirectBFSCoverage018
import DirectBFSCoverage019
import DirectBFSCoverage020
import DirectBFSCoverage021
import DirectBFSCoverage022
import DirectBFSCoverage023
import DirectBFSCoverage024
import DirectBFSCoverage025
import DirectBFSCoverage026
import DirectBFSCoverage027
import DirectBFSCoverage028
import DirectBFSCoverage029
import DirectBFSCoverage030
import DirectBFSCoverage031
import DirectBFSCoverage032
import DirectBFSCoverage033
import DirectBFSCoverage034
import DirectBFSCoverage035
import DirectBFSCoverage036
import DirectBFSCoverage037
import DirectBFSCoverage038
import DirectBFSCoverage039
import DirectBFSCoverage040
import DirectBFSCoverage041
import DirectBFSCoverage042
import DirectBFSCoverage043
import DirectBFSCoverage044
import DirectBFSCoverage045
import DirectBFSCoverage046
import DirectBFSCoverage047
import DirectBFSCoverage048
import DirectBFSCoverage049
import DirectBFSCoverage050
import DirectBFSCoverage051
import DirectBFSCoverage052
import DirectBFSCoverage053
import DirectBFSCoverage054
import DirectBFSCoverage055
import DirectBFSCoverage056
import DirectBFSCoverage057
import DirectBFSCoverage058
import DirectBFSConjugacyShape
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 30000000
namespace DirectBFSCoverageAggregate
open DirectBFSConjugacyChunk DirectBFSCoverage DirectBFSConjugacyBase

theorem rows_all : checkRows 0 943=true := by
  have h000 := DirectBFSCoverage.rows_000
  have h001 := DirectBFSCoverage.rows_001
  have h002 := DirectBFSCoverage.rows_002
  have h003 := DirectBFSCoverage.rows_003
  have h004 := DirectBFSCoverage.rows_004
  have h005 := DirectBFSCoverage.rows_005
  have h006 := DirectBFSCoverage.rows_006
  have h007 := DirectBFSCoverage.rows_007
  have h008 := DirectBFSCoverage.rows_008
  have h009 := DirectBFSCoverage.rows_009
  have h010 := DirectBFSCoverage.rows_010
  have h011 := DirectBFSCoverage.rows_011
  have h012 := DirectBFSCoverage.rows_012
  have h013 := DirectBFSCoverage.rows_013
  have h014 := DirectBFSCoverage.rows_014
  have h015 := DirectBFSCoverage.rows_015
  have h016 := DirectBFSCoverage.rows_016
  have h017 := DirectBFSCoverage.rows_017
  have h018 := DirectBFSCoverage.rows_018
  have h019 := DirectBFSCoverage.rows_019
  have h020 := DirectBFSCoverage.rows_020
  have h021 := DirectBFSCoverage.rows_021
  have h022 := DirectBFSCoverage.rows_022
  have h023 := DirectBFSCoverage.rows_023
  have h024 := DirectBFSCoverage.rows_024
  have h025 := DirectBFSCoverage.rows_025
  have h026 := DirectBFSCoverage.rows_026
  have h027 := DirectBFSCoverage.rows_027
  have h028 := DirectBFSCoverage.rows_028
  have h029 := DirectBFSCoverage.rows_029
  have h030 := DirectBFSCoverage.rows_030
  have h031 := DirectBFSCoverage.rows_031
  have h032 := DirectBFSCoverage.rows_032
  have h033 := DirectBFSCoverage.rows_033
  have h034 := DirectBFSCoverage.rows_034
  have h035 := DirectBFSCoverage.rows_035
  have h036 := DirectBFSCoverage.rows_036
  have h037 := DirectBFSCoverage.rows_037
  have h038 := DirectBFSCoverage.rows_038
  have h039 := DirectBFSCoverage.rows_039
  have h040 := DirectBFSCoverage.rows_040
  have h041 := DirectBFSCoverage.rows_041
  have h042 := DirectBFSCoverage.rows_042
  have h043 := DirectBFSCoverage.rows_043
  have h044 := DirectBFSCoverage.rows_044
  have h045 := DirectBFSCoverage.rows_045
  have h046 := DirectBFSCoverage.rows_046
  have h047 := DirectBFSCoverage.rows_047
  have h048 := DirectBFSCoverage.rows_048
  have h049 := DirectBFSCoverage.rows_049
  have h050 := DirectBFSCoverage.rows_050
  have h051 := DirectBFSCoverage.rows_051
  have h052 := DirectBFSCoverage.rows_052
  have h053 := DirectBFSCoverage.rows_053
  have h054 := DirectBFSCoverage.rows_054
  have h055 := DirectBFSCoverage.rows_055
  have h056 := DirectBFSCoverage.rows_056
  have h057 := DirectBFSCoverage.rows_057
  have h058 := DirectBFSCoverage.rows_058
  unfold checkRows at h000 h001 h002 h003 h004 h005 h006 h007 h008 h009 h010 h011 h012 h013 h014 h015 h016 h017 h018 h019 h020 h021 h022 h023 h024 h025 h026 h027 h028 h029 h030 h031 h032 h033 h034 h035 h036 h037 h038 h039 h040 h041 h042 h043 h044 h045 h046 h047 h048 h049 h050 h051 h052 h053 h054 h055 h056 h057 h058 ⊢
  have hr : List.range' 0 943=((((((((((((((((((((((((((((((((((((((((((((((((((((((((((List.range' 0 16 ++ List.range' 16 16) ++ List.range' 32 16) ++ List.range' 48 16) ++ List.range' 64 16) ++ List.range' 80 16) ++ List.range' 96 16) ++ List.range' 112 16) ++ List.range' 128 16) ++ List.range' 144 16) ++ List.range' 160 16) ++ List.range' 176 16) ++ List.range' 192 16) ++ List.range' 208 16) ++ List.range' 224 16) ++ List.range' 240 16) ++ List.range' 256 16) ++ List.range' 272 16) ++ List.range' 288 16) ++ List.range' 304 16) ++ List.range' 320 16) ++ List.range' 336 16) ++ List.range' 352 16) ++ List.range' 368 16) ++ List.range' 384 16) ++ List.range' 400 16) ++ List.range' 416 16) ++ List.range' 432 16) ++ List.range' 448 16) ++ List.range' 464 16) ++ List.range' 480 16) ++ List.range' 496 16) ++ List.range' 512 16) ++ List.range' 528 16) ++ List.range' 544 16) ++ List.range' 560 16) ++ List.range' 576 16) ++ List.range' 592 16) ++ List.range' 608 16) ++ List.range' 624 16) ++ List.range' 640 16) ++ List.range' 656 16) ++ List.range' 672 16) ++ List.range' 688 16) ++ List.range' 704 16) ++ List.range' 720 16) ++ List.range' 736 16) ++ List.range' 752 16) ++ List.range' 768 16) ++ List.range' 784 16) ++ List.range' 800 16) ++ List.range' 816 16) ++ List.range' 832 16) ++ List.range' 848 16) ++ List.range' 864 16) ++ List.range' 880 16) ++ List.range' 896 16) ++ List.range' 912 16) ++ List.range' 928 15) := by
    decide
  rw [hr]
  simp only [List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, Bool.true_and]

theorem inverse_all : checkRowInverse 0 943=true := by
  have h000 := DirectBFSCoverage.inverse_000
  have h001 := DirectBFSCoverage.inverse_001
  have h002 := DirectBFSCoverage.inverse_002
  have h003 := DirectBFSCoverage.inverse_003
  have h004 := DirectBFSCoverage.inverse_004
  have h005 := DirectBFSCoverage.inverse_005
  have h006 := DirectBFSCoverage.inverse_006
  have h007 := DirectBFSCoverage.inverse_007
  have h008 := DirectBFSCoverage.inverse_008
  have h009 := DirectBFSCoverage.inverse_009
  have h010 := DirectBFSCoverage.inverse_010
  have h011 := DirectBFSCoverage.inverse_011
  have h012 := DirectBFSCoverage.inverse_012
  have h013 := DirectBFSCoverage.inverse_013
  have h014 := DirectBFSCoverage.inverse_014
  have h015 := DirectBFSCoverage.inverse_015
  have h016 := DirectBFSCoverage.inverse_016
  have h017 := DirectBFSCoverage.inverse_017
  have h018 := DirectBFSCoverage.inverse_018
  have h019 := DirectBFSCoverage.inverse_019
  have h020 := DirectBFSCoverage.inverse_020
  have h021 := DirectBFSCoverage.inverse_021
  have h022 := DirectBFSCoverage.inverse_022
  have h023 := DirectBFSCoverage.inverse_023
  have h024 := DirectBFSCoverage.inverse_024
  have h025 := DirectBFSCoverage.inverse_025
  have h026 := DirectBFSCoverage.inverse_026
  have h027 := DirectBFSCoverage.inverse_027
  have h028 := DirectBFSCoverage.inverse_028
  have h029 := DirectBFSCoverage.inverse_029
  have h030 := DirectBFSCoverage.inverse_030
  have h031 := DirectBFSCoverage.inverse_031
  have h032 := DirectBFSCoverage.inverse_032
  have h033 := DirectBFSCoverage.inverse_033
  have h034 := DirectBFSCoverage.inverse_034
  have h035 := DirectBFSCoverage.inverse_035
  have h036 := DirectBFSCoverage.inverse_036
  have h037 := DirectBFSCoverage.inverse_037
  have h038 := DirectBFSCoverage.inverse_038
  have h039 := DirectBFSCoverage.inverse_039
  have h040 := DirectBFSCoverage.inverse_040
  have h041 := DirectBFSCoverage.inverse_041
  have h042 := DirectBFSCoverage.inverse_042
  have h043 := DirectBFSCoverage.inverse_043
  have h044 := DirectBFSCoverage.inverse_044
  have h045 := DirectBFSCoverage.inverse_045
  have h046 := DirectBFSCoverage.inverse_046
  have h047 := DirectBFSCoverage.inverse_047
  have h048 := DirectBFSCoverage.inverse_048
  have h049 := DirectBFSCoverage.inverse_049
  have h050 := DirectBFSCoverage.inverse_050
  have h051 := DirectBFSCoverage.inverse_051
  have h052 := DirectBFSCoverage.inverse_052
  have h053 := DirectBFSCoverage.inverse_053
  have h054 := DirectBFSCoverage.inverse_054
  have h055 := DirectBFSCoverage.inverse_055
  have h056 := DirectBFSCoverage.inverse_056
  have h057 := DirectBFSCoverage.inverse_057
  have h058 := DirectBFSCoverage.inverse_058
  unfold checkRowInverse at h000 h001 h002 h003 h004 h005 h006 h007 h008 h009 h010 h011 h012 h013 h014 h015 h016 h017 h018 h019 h020 h021 h022 h023 h024 h025 h026 h027 h028 h029 h030 h031 h032 h033 h034 h035 h036 h037 h038 h039 h040 h041 h042 h043 h044 h045 h046 h047 h048 h049 h050 h051 h052 h053 h054 h055 h056 h057 h058 ⊢
  have hr : List.range' 0 943=((((((((((((((((((((((((((((((((((((((((((((((((((((((((((List.range' 0 16 ++ List.range' 16 16) ++ List.range' 32 16) ++ List.range' 48 16) ++ List.range' 64 16) ++ List.range' 80 16) ++ List.range' 96 16) ++ List.range' 112 16) ++ List.range' 128 16) ++ List.range' 144 16) ++ List.range' 160 16) ++ List.range' 176 16) ++ List.range' 192 16) ++ List.range' 208 16) ++ List.range' 224 16) ++ List.range' 240 16) ++ List.range' 256 16) ++ List.range' 272 16) ++ List.range' 288 16) ++ List.range' 304 16) ++ List.range' 320 16) ++ List.range' 336 16) ++ List.range' 352 16) ++ List.range' 368 16) ++ List.range' 384 16) ++ List.range' 400 16) ++ List.range' 416 16) ++ List.range' 432 16) ++ List.range' 448 16) ++ List.range' 464 16) ++ List.range' 480 16) ++ List.range' 496 16) ++ List.range' 512 16) ++ List.range' 528 16) ++ List.range' 544 16) ++ List.range' 560 16) ++ List.range' 576 16) ++ List.range' 592 16) ++ List.range' 608 16) ++ List.range' 624 16) ++ List.range' 640 16) ++ List.range' 656 16) ++ List.range' 672 16) ++ List.range' 688 16) ++ List.range' 704 16) ++ List.range' 720 16) ++ List.range' 736 16) ++ List.range' 752 16) ++ List.range' 768 16) ++ List.range' 784 16) ++ List.range' 800 16) ++ List.range' 816 16) ++ List.range' 832 16) ++ List.range' 848 16) ++ List.range' 864 16) ++ List.range' 880 16) ++ List.range' 896 16) ++ List.range' 912 16) ++ List.range' 928 15) := by
    decide
  rw [hr]
  simp only [List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, Bool.true_and]

theorem horizontal_all : checkHorizontal 0 250=true := by
  have h000 := DirectBFSCoverage.horizontal_000
  have h001 := DirectBFSCoverage.horizontal_001
  have h002 := DirectBFSCoverage.horizontal_002
  have h003 := DirectBFSCoverage.horizontal_003
  have h004 := DirectBFSCoverage.horizontal_004
  have h005 := DirectBFSCoverage.horizontal_005
  have h006 := DirectBFSCoverage.horizontal_006
  have h007 := DirectBFSCoverage.horizontal_007
  have h008 := DirectBFSCoverage.horizontal_008
  have h009 := DirectBFSCoverage.horizontal_009
  have h010 := DirectBFSCoverage.horizontal_010
  have h011 := DirectBFSCoverage.horizontal_011
  have h012 := DirectBFSCoverage.horizontal_012
  have h013 := DirectBFSCoverage.horizontal_013
  have h014 := DirectBFSCoverage.horizontal_014
  have h015 := DirectBFSCoverage.horizontal_015
  unfold checkHorizontal at h000 h001 h002 h003 h004 h005 h006 h007 h008 h009 h010 h011 h012 h013 h014 h015 ⊢
  have hr : List.range' 0 250=(((((((((((((((List.range' 0 16 ++ List.range' 16 16) ++ List.range' 32 16) ++ List.range' 48 16) ++ List.range' 64 16) ++ List.range' 80 16) ++ List.range' 96 16) ++ List.range' 112 16) ++ List.range' 128 16) ++ List.range' 144 16) ++ List.range' 160 16) ++ List.range' 176 16) ++ List.range' 192 16) ++ List.range' 208 16) ++ List.range' 224 16) ++ List.range' 240 10) := by
    decide
  rw [hr]
  simp only [List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, Bool.true_and]

theorem vertical_all : checkVertical 0 439=true := by
  have h000 := DirectBFSCoverage.vertical_000
  have h001 := DirectBFSCoverage.vertical_001
  have h002 := DirectBFSCoverage.vertical_002
  have h003 := DirectBFSCoverage.vertical_003
  have h004 := DirectBFSCoverage.vertical_004
  have h005 := DirectBFSCoverage.vertical_005
  have h006 := DirectBFSCoverage.vertical_006
  have h007 := DirectBFSCoverage.vertical_007
  have h008 := DirectBFSCoverage.vertical_008
  have h009 := DirectBFSCoverage.vertical_009
  have h010 := DirectBFSCoverage.vertical_010
  have h011 := DirectBFSCoverage.vertical_011
  have h012 := DirectBFSCoverage.vertical_012
  have h013 := DirectBFSCoverage.vertical_013
  have h014 := DirectBFSCoverage.vertical_014
  have h015 := DirectBFSCoverage.vertical_015
  have h016 := DirectBFSCoverage.vertical_016
  have h017 := DirectBFSCoverage.vertical_017
  have h018 := DirectBFSCoverage.vertical_018
  have h019 := DirectBFSCoverage.vertical_019
  have h020 := DirectBFSCoverage.vertical_020
  have h021 := DirectBFSCoverage.vertical_021
  have h022 := DirectBFSCoverage.vertical_022
  have h023 := DirectBFSCoverage.vertical_023
  have h024 := DirectBFSCoverage.vertical_024
  have h025 := DirectBFSCoverage.vertical_025
  have h026 := DirectBFSCoverage.vertical_026
  have h027 := DirectBFSCoverage.vertical_027
  unfold checkVertical at h000 h001 h002 h003 h004 h005 h006 h007 h008 h009 h010 h011 h012 h013 h014 h015 h016 h017 h018 h019 h020 h021 h022 h023 h024 h025 h026 h027 ⊢
  have hr : List.range' 0 439=(((((((((((((((((((((((((((List.range' 0 16 ++ List.range' 16 16) ++ List.range' 32 16) ++ List.range' 48 16) ++ List.range' 64 16) ++ List.range' 80 16) ++ List.range' 96 16) ++ List.range' 112 16) ++ List.range' 128 16) ++ List.range' 144 16) ++ List.range' 160 16) ++ List.range' 176 16) ++ List.range' 192 16) ++ List.range' 208 16) ++ List.range' 224 16) ++ List.range' 240 16) ++ List.range' 256 16) ++ List.range' 272 16) ++ List.range' 288 16) ++ List.range' 304 16) ++ List.range' 320 16) ++ List.range' 336 16) ++ List.range' 352 16) ++ List.range' 368 16) ++ List.range' 384 16) ++ List.range' 400 16) ++ List.range' 416 16) ++ List.range' 432 7) := by
    decide
  rw [hr]
  simp only [List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, Bool.true_and]

theorem inversebounds_all : (List.range' 0 943).all (fun j => decide (rowMap.getD j 0 < 943 ∧ rowInverse.getD j 0 < 943))=true := by
  have h000 := DirectBFSCoverage.inversebounds_000
  have h001 := DirectBFSCoverage.inversebounds_001
  have h002 := DirectBFSCoverage.inversebounds_002
  have h003 := DirectBFSCoverage.inversebounds_003
  have h004 := DirectBFSCoverage.inversebounds_004
  have h005 := DirectBFSCoverage.inversebounds_005
  have h006 := DirectBFSCoverage.inversebounds_006
  have h007 := DirectBFSCoverage.inversebounds_007
  have h008 := DirectBFSCoverage.inversebounds_008
  have h009 := DirectBFSCoverage.inversebounds_009
  have h010 := DirectBFSCoverage.inversebounds_010
  have h011 := DirectBFSCoverage.inversebounds_011
  have h012 := DirectBFSCoverage.inversebounds_012
  have h013 := DirectBFSCoverage.inversebounds_013
  have h014 := DirectBFSCoverage.inversebounds_014
  have h015 := DirectBFSCoverage.inversebounds_015
  have h016 := DirectBFSCoverage.inversebounds_016
  have h017 := DirectBFSCoverage.inversebounds_017
  have h018 := DirectBFSCoverage.inversebounds_018
  have h019 := DirectBFSCoverage.inversebounds_019
  have h020 := DirectBFSCoverage.inversebounds_020
  have h021 := DirectBFSCoverage.inversebounds_021
  have h022 := DirectBFSCoverage.inversebounds_022
  have h023 := DirectBFSCoverage.inversebounds_023
  have h024 := DirectBFSCoverage.inversebounds_024
  have h025 := DirectBFSCoverage.inversebounds_025
  have h026 := DirectBFSCoverage.inversebounds_026
  have h027 := DirectBFSCoverage.inversebounds_027
  have h028 := DirectBFSCoverage.inversebounds_028
  have h029 := DirectBFSCoverage.inversebounds_029
  have h030 := DirectBFSCoverage.inversebounds_030
  have h031 := DirectBFSCoverage.inversebounds_031
  have h032 := DirectBFSCoverage.inversebounds_032
  have h033 := DirectBFSCoverage.inversebounds_033
  have h034 := DirectBFSCoverage.inversebounds_034
  have h035 := DirectBFSCoverage.inversebounds_035
  have h036 := DirectBFSCoverage.inversebounds_036
  have h037 := DirectBFSCoverage.inversebounds_037
  have h038 := DirectBFSCoverage.inversebounds_038
  have h039 := DirectBFSCoverage.inversebounds_039
  have h040 := DirectBFSCoverage.inversebounds_040
  have h041 := DirectBFSCoverage.inversebounds_041
  have h042 := DirectBFSCoverage.inversebounds_042
  have h043 := DirectBFSCoverage.inversebounds_043
  have h044 := DirectBFSCoverage.inversebounds_044
  have h045 := DirectBFSCoverage.inversebounds_045
  have h046 := DirectBFSCoverage.inversebounds_046
  have h047 := DirectBFSCoverage.inversebounds_047
  have h048 := DirectBFSCoverage.inversebounds_048
  have h049 := DirectBFSCoverage.inversebounds_049
  have h050 := DirectBFSCoverage.inversebounds_050
  have h051 := DirectBFSCoverage.inversebounds_051
  have h052 := DirectBFSCoverage.inversebounds_052
  have h053 := DirectBFSCoverage.inversebounds_053
  have h054 := DirectBFSCoverage.inversebounds_054
  have h055 := DirectBFSCoverage.inversebounds_055
  have h056 := DirectBFSCoverage.inversebounds_056
  have h057 := DirectBFSCoverage.inversebounds_057
  have h058 := DirectBFSCoverage.inversebounds_058
  have hr : List.range' 0 943=((((((((((((((((((((((((((((((((((((((((((((((((((((((((((List.range' 0 16 ++ List.range' 16 16) ++ List.range' 32 16) ++ List.range' 48 16) ++ List.range' 64 16) ++ List.range' 80 16) ++ List.range' 96 16) ++ List.range' 112 16) ++ List.range' 128 16) ++ List.range' 144 16) ++ List.range' 160 16) ++ List.range' 176 16) ++ List.range' 192 16) ++ List.range' 208 16) ++ List.range' 224 16) ++ List.range' 240 16) ++ List.range' 256 16) ++ List.range' 272 16) ++ List.range' 288 16) ++ List.range' 304 16) ++ List.range' 320 16) ++ List.range' 336 16) ++ List.range' 352 16) ++ List.range' 368 16) ++ List.range' 384 16) ++ List.range' 400 16) ++ List.range' 416 16) ++ List.range' 432 16) ++ List.range' 448 16) ++ List.range' 464 16) ++ List.range' 480 16) ++ List.range' 496 16) ++ List.range' 512 16) ++ List.range' 528 16) ++ List.range' 544 16) ++ List.range' 560 16) ++ List.range' 576 16) ++ List.range' 592 16) ++ List.range' 608 16) ++ List.range' 624 16) ++ List.range' 640 16) ++ List.range' 656 16) ++ List.range' 672 16) ++ List.range' 688 16) ++ List.range' 704 16) ++ List.range' 720 16) ++ List.range' 736 16) ++ List.range' 752 16) ++ List.range' 768 16) ++ List.range' 784 16) ++ List.range' 800 16) ++ List.range' 816 16) ++ List.range' 832 16) ++ List.range' 848 16) ++ List.range' 864 16) ++ List.range' 880 16) ++ List.range' 896 16) ++ List.range' 912 16) ++ List.range' 928 15) := by
    decide
  rw [hr]
  simp only [List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, Bool.true_and]

theorem horizontalbounds_all : (List.range' 0 250).all (fun j => decide (horizontal.getD j 0 < 250 ∧ horizontalInverse.getD j 0 < 250))=true := by
  have h000 := DirectBFSCoverage.horizontalbounds_000
  have h001 := DirectBFSCoverage.horizontalbounds_001
  have h002 := DirectBFSCoverage.horizontalbounds_002
  have h003 := DirectBFSCoverage.horizontalbounds_003
  have h004 := DirectBFSCoverage.horizontalbounds_004
  have h005 := DirectBFSCoverage.horizontalbounds_005
  have h006 := DirectBFSCoverage.horizontalbounds_006
  have h007 := DirectBFSCoverage.horizontalbounds_007
  have h008 := DirectBFSCoverage.horizontalbounds_008
  have h009 := DirectBFSCoverage.horizontalbounds_009
  have h010 := DirectBFSCoverage.horizontalbounds_010
  have h011 := DirectBFSCoverage.horizontalbounds_011
  have h012 := DirectBFSCoverage.horizontalbounds_012
  have h013 := DirectBFSCoverage.horizontalbounds_013
  have h014 := DirectBFSCoverage.horizontalbounds_014
  have h015 := DirectBFSCoverage.horizontalbounds_015
  have hr : List.range' 0 250=(((((((((((((((List.range' 0 16 ++ List.range' 16 16) ++ List.range' 32 16) ++ List.range' 48 16) ++ List.range' 64 16) ++ List.range' 80 16) ++ List.range' 96 16) ++ List.range' 112 16) ++ List.range' 128 16) ++ List.range' 144 16) ++ List.range' 160 16) ++ List.range' 176 16) ++ List.range' 192 16) ++ List.range' 208 16) ++ List.range' 224 16) ++ List.range' 240 10) := by
    decide
  rw [hr]
  simp only [List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, Bool.true_and]

theorem verticalbounds_all : (List.range' 0 439).all (fun j => decide (vertical.getD j 0 < 439 ∧ verticalInverse.getD j 0 < 439))=true := by
  have h000 := DirectBFSCoverage.verticalbounds_000
  have h001 := DirectBFSCoverage.verticalbounds_001
  have h002 := DirectBFSCoverage.verticalbounds_002
  have h003 := DirectBFSCoverage.verticalbounds_003
  have h004 := DirectBFSCoverage.verticalbounds_004
  have h005 := DirectBFSCoverage.verticalbounds_005
  have h006 := DirectBFSCoverage.verticalbounds_006
  have h007 := DirectBFSCoverage.verticalbounds_007
  have h008 := DirectBFSCoverage.verticalbounds_008
  have h009 := DirectBFSCoverage.verticalbounds_009
  have h010 := DirectBFSCoverage.verticalbounds_010
  have h011 := DirectBFSCoverage.verticalbounds_011
  have h012 := DirectBFSCoverage.verticalbounds_012
  have h013 := DirectBFSCoverage.verticalbounds_013
  have h014 := DirectBFSCoverage.verticalbounds_014
  have h015 := DirectBFSCoverage.verticalbounds_015
  have h016 := DirectBFSCoverage.verticalbounds_016
  have h017 := DirectBFSCoverage.verticalbounds_017
  have h018 := DirectBFSCoverage.verticalbounds_018
  have h019 := DirectBFSCoverage.verticalbounds_019
  have h020 := DirectBFSCoverage.verticalbounds_020
  have h021 := DirectBFSCoverage.verticalbounds_021
  have h022 := DirectBFSCoverage.verticalbounds_022
  have h023 := DirectBFSCoverage.verticalbounds_023
  have h024 := DirectBFSCoverage.verticalbounds_024
  have h025 := DirectBFSCoverage.verticalbounds_025
  have h026 := DirectBFSCoverage.verticalbounds_026
  have h027 := DirectBFSCoverage.verticalbounds_027
  have hr : List.range' 0 439=(((((((((((((((((((((((((((List.range' 0 16 ++ List.range' 16 16) ++ List.range' 32 16) ++ List.range' 48 16) ++ List.range' 64 16) ++ List.range' 80 16) ++ List.range' 96 16) ++ List.range' 112 16) ++ List.range' 128 16) ++ List.range' 144 16) ++ List.range' 160 16) ++ List.range' 176 16) ++ List.range' 192 16) ++ List.range' 208 16) ++ List.range' 224 16) ++ List.range' 240 16) ++ List.range' 256 16) ++ List.range' 272 16) ++ List.range' 288 16) ++ List.range' 304 16) ++ List.range' 320 16) ++ List.range' 336 16) ++ List.range' 352 16) ++ List.range' 368 16) ++ List.range' 384 16) ++ List.range' 400 16) ++ List.range' 416 16) ++ List.range' 432 7) := by
    decide
  rw [hr]
  simp only [List.all_append, h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, Bool.true_and]
#print axioms DirectBFSCoverageAggregate.rows_all
#print axioms DirectBFSCoverageAggregate.inverse_all
#print axioms DirectBFSCoverageAggregate.horizontal_all
#print axioms DirectBFSCoverageAggregate.vertical_all
#print axioms DirectBFSCoverageAggregate.inversebounds_all
#print axioms DirectBFSCoverageAggregate.horizontalbounds_all
#print axioms DirectBFSCoverageAggregate.verticalbounds_all
end DirectBFSCoverageAggregate
