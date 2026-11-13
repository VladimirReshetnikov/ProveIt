module
public import M6PA.Model.OriginalCoverage.S000
public import M6PA.Model.OriginalCoverage.S001
public import M6PA.Model.OriginalCoverage.S002
public import M6PA.Model.OriginalCoverage.S003
public import M6PA.Model.OriginalCoverage.S004
public import M6PA.Model.OriginalCoverage.S005
public import M6PA.Model.OriginalCoverage.S006
public import M6PA.Model.OriginalCoverage.S007
public import M6PA.Model.OriginalCoverage.S008
public import M6PA.Model.OriginalCoverage.S009
public import M6PA.Model.OriginalCoverage.S010
public import M6PA.Model.OriginalCoverage.S011
public import M6PA.Model.OriginalCoverage.S012
public import M6PA.Model.OriginalCoverage.S013
public import M6PA.Model.OriginalCoverage.S014
public import M6PA.Model.OriginalCoverage.S015
public import M6PA.Model.OriginalCoverage.S016
public import M6PA.Model.OriginalCoverage.S017
public import M6PA.Model.OriginalCoverage.S018
public import M6PA.Model.OriginalCoverage.S019
public import M6PA.Model.OriginalCoverage.S020
public import M6PA.Model.OriginalCoverage.S021
public import M6PA.Model.OriginalCoverage.S022
public import M6PA.Model.OriginalCoverage.S023
public import M6PA.Model.OriginalCoverage.S024
public import M6PA.Model.OriginalCoverage.S025
public import M6PA.Model.OriginalCoverage.S026
public import M6PA.Model.OriginalCoverage.S027
public import M6PA.Model.OriginalCoverage.S028
public import M6PA.Model.OriginalCoverage.S029
public import M6PA.Model.OriginalCoverage.S030
public import M6PA.Model.OriginalCoverage.S031
public import M6PA.Model.OriginalCoverage.S032
public import M6PA.Model.OriginalCoverage.S033
public import M6PA.Model.OriginalCoverage.S034
public import M6PA.Model.OriginalCoverage.S035
public import M6PA.Model.OriginalCoverage.S036
public import M6PA.Model.OriginalCoverage.S037
public import M6PA.Model.OriginalCoverage.S038
public import M6PA.Model.OriginalCoverage.S039
public import M6PA.Model.OriginalCoverage.S040
public import M6PA.Model.OriginalCoverage.S041
public import M6PA.Model.OriginalCoverage.S042
public import M6PA.Model.OriginalCoverage.S043
public import M6PA.Model.OriginalCoverage.S044
public import M6PA.Model.OriginalCoverage.S045
public import M6PA.Model.OriginalCoverage.S046
public import M6PA.Model.OriginalCoverage.S047
public import M6PA.Model.OriginalCoverage.S048
public import M6PA.Model.OriginalCoverage.S049
public import M6PA.Model.OriginalCoverage.S050
public import M6PA.Model.OriginalCoverage.S051
public import M6PA.Model.OriginalCoverage.S052
public import M6PA.Model.OriginalCoverage.S053
public import M6PA.Model.OriginalCoverage.S054
public import M6PA.Model.OriginalCoverage.S055
public import M6PA.Model.OriginalCoverage.S056
public import M6PA.Model.OriginalCoverage.S057
public import M6PA.Model.OriginalCoverage.S058
public import M6PA.Model.OriginalCoverage.S059
public import M6PA.Model.OriginalCoverage.S060
public import M6PA.Model.OriginalCoverage.S061
@[expose] public section
namespace M6.Arithmetic.OriginalCoverage
theorem checked (i : Nat) (hi : i < 3947) : OriginalCheck.checkAt i = true := by
  by_cases h0 : i < 64
  · exact OriginalCheck.block_sound S000.checked (by omega) h0
  by_cases h1 : i < 128
  · exact OriginalCheck.block_sound S001.checked (by omega) h1
  by_cases h2 : i < 192
  · exact OriginalCheck.block_sound S002.checked (by omega) h2
  by_cases h3 : i < 256
  · exact OriginalCheck.block_sound S003.checked (by omega) h3
  by_cases h4 : i < 320
  · exact OriginalCheck.block_sound S004.checked (by omega) h4
  by_cases h5 : i < 384
  · exact OriginalCheck.block_sound S005.checked (by omega) h5
  by_cases h6 : i < 448
  · exact OriginalCheck.block_sound S006.checked (by omega) h6
  by_cases h7 : i < 512
  · exact OriginalCheck.block_sound S007.checked (by omega) h7
  by_cases h8 : i < 576
  · exact OriginalCheck.block_sound S008.checked (by omega) h8
  by_cases h9 : i < 640
  · exact OriginalCheck.block_sound S009.checked (by omega) h9
  by_cases h10 : i < 704
  · exact OriginalCheck.block_sound S010.checked (by omega) h10
  by_cases h11 : i < 768
  · exact OriginalCheck.block_sound S011.checked (by omega) h11
  by_cases h12 : i < 832
  · exact OriginalCheck.block_sound S012.checked (by omega) h12
  by_cases h13 : i < 896
  · exact OriginalCheck.block_sound S013.checked (by omega) h13
  by_cases h14 : i < 960
  · exact OriginalCheck.block_sound S014.checked (by omega) h14
  by_cases h15 : i < 1024
  · exact OriginalCheck.block_sound S015.checked (by omega) h15
  by_cases h16 : i < 1088
  · exact OriginalCheck.block_sound S016.checked (by omega) h16
  by_cases h17 : i < 1152
  · exact OriginalCheck.block_sound S017.checked (by omega) h17
  by_cases h18 : i < 1216
  · exact OriginalCheck.block_sound S018.checked (by omega) h18
  by_cases h19 : i < 1280
  · exact OriginalCheck.block_sound S019.checked (by omega) h19
  by_cases h20 : i < 1344
  · exact OriginalCheck.block_sound S020.checked (by omega) h20
  by_cases h21 : i < 1408
  · exact OriginalCheck.block_sound S021.checked (by omega) h21
  by_cases h22 : i < 1472
  · exact OriginalCheck.block_sound S022.checked (by omega) h22
  by_cases h23 : i < 1536
  · exact OriginalCheck.block_sound S023.checked (by omega) h23
  by_cases h24 : i < 1600
  · exact OriginalCheck.block_sound S024.checked (by omega) h24
  by_cases h25 : i < 1664
  · exact OriginalCheck.block_sound S025.checked (by omega) h25
  by_cases h26 : i < 1728
  · exact OriginalCheck.block_sound S026.checked (by omega) h26
  by_cases h27 : i < 1792
  · exact OriginalCheck.block_sound S027.checked (by omega) h27
  by_cases h28 : i < 1856
  · exact OriginalCheck.block_sound S028.checked (by omega) h28
  by_cases h29 : i < 1920
  · exact OriginalCheck.block_sound S029.checked (by omega) h29
  by_cases h30 : i < 1984
  · exact OriginalCheck.block_sound S030.checked (by omega) h30
  by_cases h31 : i < 2048
  · exact OriginalCheck.block_sound S031.checked (by omega) h31
  by_cases h32 : i < 2112
  · exact OriginalCheck.block_sound S032.checked (by omega) h32
  by_cases h33 : i < 2176
  · exact OriginalCheck.block_sound S033.checked (by omega) h33
  by_cases h34 : i < 2240
  · exact OriginalCheck.block_sound S034.checked (by omega) h34
  by_cases h35 : i < 2304
  · exact OriginalCheck.block_sound S035.checked (by omega) h35
  by_cases h36 : i < 2368
  · exact OriginalCheck.block_sound S036.checked (by omega) h36
  by_cases h37 : i < 2432
  · exact OriginalCheck.block_sound S037.checked (by omega) h37
  by_cases h38 : i < 2496
  · exact OriginalCheck.block_sound S038.checked (by omega) h38
  by_cases h39 : i < 2560
  · exact OriginalCheck.block_sound S039.checked (by omega) h39
  by_cases h40 : i < 2624
  · exact OriginalCheck.block_sound S040.checked (by omega) h40
  by_cases h41 : i < 2688
  · exact OriginalCheck.block_sound S041.checked (by omega) h41
  by_cases h42 : i < 2752
  · exact OriginalCheck.block_sound S042.checked (by omega) h42
  by_cases h43 : i < 2816
  · exact OriginalCheck.block_sound S043.checked (by omega) h43
  by_cases h44 : i < 2880
  · exact OriginalCheck.block_sound S044.checked (by omega) h44
  by_cases h45 : i < 2944
  · exact OriginalCheck.block_sound S045.checked (by omega) h45
  by_cases h46 : i < 3008
  · exact OriginalCheck.block_sound S046.checked (by omega) h46
  by_cases h47 : i < 3072
  · exact OriginalCheck.block_sound S047.checked (by omega) h47
  by_cases h48 : i < 3136
  · exact OriginalCheck.block_sound S048.checked (by omega) h48
  by_cases h49 : i < 3200
  · exact OriginalCheck.block_sound S049.checked (by omega) h49
  by_cases h50 : i < 3264
  · exact OriginalCheck.block_sound S050.checked (by omega) h50
  by_cases h51 : i < 3328
  · exact OriginalCheck.block_sound S051.checked (by omega) h51
  by_cases h52 : i < 3392
  · exact OriginalCheck.block_sound S052.checked (by omega) h52
  by_cases h53 : i < 3456
  · exact OriginalCheck.block_sound S053.checked (by omega) h53
  by_cases h54 : i < 3520
  · exact OriginalCheck.block_sound S054.checked (by omega) h54
  by_cases h55 : i < 3584
  · exact OriginalCheck.block_sound S055.checked (by omega) h55
  by_cases h56 : i < 3648
  · exact OriginalCheck.block_sound S056.checked (by omega) h56
  by_cases h57 : i < 3712
  · exact OriginalCheck.block_sound S057.checked (by omega) h57
  by_cases h58 : i < 3776
  · exact OriginalCheck.block_sound S058.checked (by omega) h58
  by_cases h59 : i < 3840
  · exact OriginalCheck.block_sound S059.checked (by omega) h59
  by_cases h60 : i < 3904
  · exact OriginalCheck.block_sound S060.checked (by omega) h60
  exact OriginalCheck.block_sound S061.checked (by omega) (by omega)
#print axioms checked
end M6.Arithmetic.OriginalCoverage
