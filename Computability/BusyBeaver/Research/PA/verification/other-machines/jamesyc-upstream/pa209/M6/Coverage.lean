module
public import M6.Coverage.S000
public import M6.Coverage.S001
public import M6.Coverage.S002
public import M6.Coverage.S003
public import M6.Coverage.S004
public import M6.Coverage.S005
public import M6.Coverage.S006
public import M6.Coverage.S007
public import M6.Coverage.S008
public import M6.Coverage.S009
public import M6.Coverage.S010
public import M6.Coverage.S011
public import M6.Coverage.S012
public import M6.Coverage.S013
public import M6.Coverage.S014
public import M6.Coverage.S015
public import M6.Coverage.S016
public import M6.Coverage.S017
public import M6.Coverage.S018
public import M6.Coverage.S019
public import M6.Coverage.S020
public import M6.Coverage.S021
public import M6.Coverage.S022
public import M6.Coverage.S023
public import M6.Coverage.S024
public import M6.Coverage.S025
public import M6.Coverage.S026
public import M6.Coverage.S027
public import M6.Coverage.S028
public import M6.Coverage.S029
public import M6.Coverage.S030
public import M6.Coverage.S031
public import M6.Coverage.S032
public import M6.Coverage.S033
public import M6.Coverage.S034
public import M6.Coverage.S035
public import M6.Coverage.S036
public import M6.Coverage.S037
public import M6.Coverage.S038
public import M6.Coverage.S039
public import M6.Coverage.S040
public import M6.Coverage.S041
public import M6.Coverage.S042
public import M6.Coverage.S043
public import M6.Coverage.S044
public import M6.Coverage.S045
public import M6.Coverage.S046
public import M6.Coverage.S047
public import M6.Coverage.S048
public import M6.Coverage.S049
public import M6.Coverage.S050
public import M6.Coverage.S051
public import M6.Coverage.S052
public import M6.Coverage.S053
public import M6.Coverage.S054
public import M6.Coverage.S055
public import M6.Coverage.S056
public import M6.Coverage.S057
public import M6.Coverage.S058
public import M6.Coverage.S059
public import M6.Coverage.S060
public import M6.Coverage.S061
@[expose] public section
namespace M6.Coverage
theorem complete : CompilerCorrectness.Coverage Program.sites Program.path 3948 := by
  intro i hi
  by_cases h31 : i < 1984
  ·
    by_cases h15 : i < 960
    ·
      by_cases h7 : i < 448
      ·
        by_cases h3 : i < 192
        ·
          by_cases h1 : i < 64
          ·
            exact CheckCoverage.checked_at i (CheckCoverage.block_sound S000.checked (by omega) (by omega))
          ·
            by_cases h2 : i < 128
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S001.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S002.checked (by omega) (by omega))
        ·
          by_cases h5 : i < 320
          ·
            by_cases h4 : i < 256
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S003.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S004.checked (by omega) (by omega))
          ·
            by_cases h6 : i < 384
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S005.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S006.checked (by omega) (by omega))
      ·
        by_cases h11 : i < 704
        ·
          by_cases h9 : i < 576
          ·
            by_cases h8 : i < 512
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S007.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S008.checked (by omega) (by omega))
          ·
            by_cases h10 : i < 640
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S009.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S010.checked (by omega) (by omega))
        ·
          by_cases h13 : i < 832
          ·
            by_cases h12 : i < 768
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S011.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S012.checked (by omega) (by omega))
          ·
            by_cases h14 : i < 896
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S013.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S014.checked (by omega) (by omega))
    ·
      by_cases h23 : i < 1472
      ·
        by_cases h19 : i < 1216
        ·
          by_cases h17 : i < 1088
          ·
            by_cases h16 : i < 1024
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S015.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S016.checked (by omega) (by omega))
          ·
            by_cases h18 : i < 1152
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S017.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S018.checked (by omega) (by omega))
        ·
          by_cases h21 : i < 1344
          ·
            by_cases h20 : i < 1280
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S019.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S020.checked (by omega) (by omega))
          ·
            by_cases h22 : i < 1408
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S021.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S022.checked (by omega) (by omega))
      ·
        by_cases h27 : i < 1728
        ·
          by_cases h25 : i < 1600
          ·
            by_cases h24 : i < 1536
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S023.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S024.checked (by omega) (by omega))
          ·
            by_cases h26 : i < 1664
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S025.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S026.checked (by omega) (by omega))
        ·
          by_cases h29 : i < 1856
          ·
            by_cases h28 : i < 1792
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S027.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S028.checked (by omega) (by omega))
          ·
            by_cases h30 : i < 1920
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S029.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S030.checked (by omega) (by omega))
  ·
    by_cases h46 : i < 2944
    ·
      by_cases h38 : i < 2432
      ·
        by_cases h34 : i < 2176
        ·
          by_cases h32 : i < 2048
          ·
            exact CheckCoverage.checked_at i (CheckCoverage.block_sound S031.checked (by omega) (by omega))
          ·
            by_cases h33 : i < 2112
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S032.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S033.checked (by omega) (by omega))
        ·
          by_cases h36 : i < 2304
          ·
            by_cases h35 : i < 2240
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S034.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S035.checked (by omega) (by omega))
          ·
            by_cases h37 : i < 2368
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S036.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S037.checked (by omega) (by omega))
      ·
        by_cases h42 : i < 2688
        ·
          by_cases h40 : i < 2560
          ·
            by_cases h39 : i < 2496
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S038.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S039.checked (by omega) (by omega))
          ·
            by_cases h41 : i < 2624
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S040.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S041.checked (by omega) (by omega))
        ·
          by_cases h44 : i < 2816
          ·
            by_cases h43 : i < 2752
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S042.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S043.checked (by omega) (by omega))
          ·
            by_cases h45 : i < 2880
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S044.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S045.checked (by omega) (by omega))
    ·
      by_cases h54 : i < 3456
      ·
        by_cases h50 : i < 3200
        ·
          by_cases h48 : i < 3072
          ·
            by_cases h47 : i < 3008
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S046.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S047.checked (by omega) (by omega))
          ·
            by_cases h49 : i < 3136
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S048.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S049.checked (by omega) (by omega))
        ·
          by_cases h52 : i < 3328
          ·
            by_cases h51 : i < 3264
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S050.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S051.checked (by omega) (by omega))
          ·
            by_cases h53 : i < 3392
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S052.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S053.checked (by omega) (by omega))
      ·
        by_cases h58 : i < 3712
        ·
          by_cases h56 : i < 3584
          ·
            by_cases h55 : i < 3520
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S054.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S055.checked (by omega) (by omega))
          ·
            by_cases h57 : i < 3648
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S056.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S057.checked (by omega) (by omega))
        ·
          by_cases h60 : i < 3840
          ·
            by_cases h59 : i < 3776
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S058.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S059.checked (by omega) (by omega))
          ·
            by_cases h61 : i < 3904
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S060.checked (by omega) (by omega))
            ·
              exact CheckCoverage.checked_at i (CheckCoverage.block_sound S061.checked (by omega) (by omega))
#print axioms complete
end M6.Coverage
