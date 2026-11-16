module
public import M6.Crosswalk.S000
public import M6.Crosswalk.S001
public import M6.Crosswalk.S002
public import M6.Crosswalk.S003
public import M6.Crosswalk.S004
public import M6.Crosswalk.S005
public import M6.Crosswalk.S006
public import M6.Crosswalk.S007
public import M6.Crosswalk.S008
public import M6.Crosswalk.S009
public import M6.Crosswalk.S010
public import M6.Crosswalk.S011
public import M6.Crosswalk.S012
public import M6.Crosswalk.S013
public import M6.Crosswalk.S014
public import M6.Crosswalk.S015
public import M6.Crosswalk.S016
public import M6.Crosswalk.S017
public import M6.Crosswalk.S018
public import M6.Crosswalk.S019
public import M6.Crosswalk.S020
public import M6.Crosswalk.S021
public import M6.Crosswalk.S022
public import M6.Crosswalk.S023
public import M6.Crosswalk.S024
public import M6.Crosswalk.S025
public import M6.Crosswalk.S026
public import M6.Crosswalk.S027
public import M6.Crosswalk.S028
public import M6.Crosswalk.S029
public import M6.Crosswalk.S030
public import M6.Crosswalk.S031
public import M6.Crosswalk.S032
public import M6.Crosswalk.S033
public import M6.Crosswalk.S034
public import M6.Crosswalk.S035
public import M6.Crosswalk.S036
public import M6.Crosswalk.S037
public import M6.Crosswalk.S038
public import M6.Crosswalk.S039
public import M6.Crosswalk.S040
public import M6.Crosswalk.S041
public import M6.Crosswalk.S042
public import M6.Crosswalk.S043
public import M6.Crosswalk.S044
public import M6.Crosswalk.S045
public import M6.Crosswalk.S046
public import M6.Crosswalk.S047
public import M6.Crosswalk.S048
public import M6.Crosswalk.S049
public import M6.Crosswalk.S050
public import M6.Crosswalk.S051
public import M6.Crosswalk.S052
public import M6.Crosswalk.S053
public import M6.Crosswalk.S054
public import M6.Crosswalk.S055
public import M6.Crosswalk.S056
public import M6.Crosswalk.S057
public import M6.Crosswalk.S058
public import M6.Crosswalk.S059
public import M6.Crosswalk.S060
public import M6.Crosswalk.S061
@[expose] public section
namespace M6.SourceCrosswalk
theorem code_crosswalk (i : Nat) (hi : i < 3947) :
    (CheckCoverage.codeAt i).map collapseInstruction =
      (originalCodeAt (collapse i)).map normalize := by
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
            exact block_sound S000.checked (by omega) (by omega)
          ·
            by_cases h2 : i < 128
            ·
              exact block_sound S001.checked (by omega) (by omega)
            ·
              exact block_sound S002.checked (by omega) (by omega)
        ·
          by_cases h5 : i < 320
          ·
            by_cases h4 : i < 256
            ·
              exact block_sound S003.checked (by omega) (by omega)
            ·
              exact block_sound S004.checked (by omega) (by omega)
          ·
            by_cases h6 : i < 384
            ·
              exact block_sound S005.checked (by omega) (by omega)
            ·
              exact block_sound S006.checked (by omega) (by omega)
      ·
        by_cases h11 : i < 704
        ·
          by_cases h9 : i < 576
          ·
            by_cases h8 : i < 512
            ·
              exact block_sound S007.checked (by omega) (by omega)
            ·
              exact block_sound S008.checked (by omega) (by omega)
          ·
            by_cases h10 : i < 640
            ·
              exact block_sound S009.checked (by omega) (by omega)
            ·
              exact block_sound S010.checked (by omega) (by omega)
        ·
          by_cases h13 : i < 832
          ·
            by_cases h12 : i < 768
            ·
              exact block_sound S011.checked (by omega) (by omega)
            ·
              exact block_sound S012.checked (by omega) (by omega)
          ·
            by_cases h14 : i < 896
            ·
              exact block_sound S013.checked (by omega) (by omega)
            ·
              exact block_sound S014.checked (by omega) (by omega)
    ·
      by_cases h23 : i < 1472
      ·
        by_cases h19 : i < 1216
        ·
          by_cases h17 : i < 1088
          ·
            by_cases h16 : i < 1024
            ·
              exact block_sound S015.checked (by omega) (by omega)
            ·
              exact block_sound S016.checked (by omega) (by omega)
          ·
            by_cases h18 : i < 1152
            ·
              exact block_sound S017.checked (by omega) (by omega)
            ·
              exact block_sound S018.checked (by omega) (by omega)
        ·
          by_cases h21 : i < 1344
          ·
            by_cases h20 : i < 1280
            ·
              exact block_sound S019.checked (by omega) (by omega)
            ·
              exact block_sound S020.checked (by omega) (by omega)
          ·
            by_cases h22 : i < 1408
            ·
              exact block_sound S021.checked (by omega) (by omega)
            ·
              exact block_sound S022.checked (by omega) (by omega)
      ·
        by_cases h27 : i < 1728
        ·
          by_cases h25 : i < 1600
          ·
            by_cases h24 : i < 1536
            ·
              exact block_sound S023.checked (by omega) (by omega)
            ·
              exact block_sound S024.checked (by omega) (by omega)
          ·
            by_cases h26 : i < 1664
            ·
              exact block_sound S025.checked (by omega) (by omega)
            ·
              exact block_sound S026.checked (by omega) (by omega)
        ·
          by_cases h29 : i < 1856
          ·
            by_cases h28 : i < 1792
            ·
              exact block_sound S027.checked (by omega) (by omega)
            ·
              exact block_sound S028.checked (by omega) (by omega)
          ·
            by_cases h30 : i < 1920
            ·
              exact block_sound S029.checked (by omega) (by omega)
            ·
              exact block_sound S030.checked (by omega) (by omega)
  ·
    by_cases h46 : i < 2944
    ·
      by_cases h38 : i < 2432
      ·
        by_cases h34 : i < 2176
        ·
          by_cases h32 : i < 2048
          ·
            exact block_sound S031.checked (by omega) (by omega)
          ·
            by_cases h33 : i < 2112
            ·
              exact block_sound S032.checked (by omega) (by omega)
            ·
              exact block_sound S033.checked (by omega) (by omega)
        ·
          by_cases h36 : i < 2304
          ·
            by_cases h35 : i < 2240
            ·
              exact block_sound S034.checked (by omega) (by omega)
            ·
              exact block_sound S035.checked (by omega) (by omega)
          ·
            by_cases h37 : i < 2368
            ·
              exact block_sound S036.checked (by omega) (by omega)
            ·
              exact block_sound S037.checked (by omega) (by omega)
      ·
        by_cases h42 : i < 2688
        ·
          by_cases h40 : i < 2560
          ·
            by_cases h39 : i < 2496
            ·
              exact block_sound S038.checked (by omega) (by omega)
            ·
              exact block_sound S039.checked (by omega) (by omega)
          ·
            by_cases h41 : i < 2624
            ·
              exact block_sound S040.checked (by omega) (by omega)
            ·
              exact block_sound S041.checked (by omega) (by omega)
        ·
          by_cases h44 : i < 2816
          ·
            by_cases h43 : i < 2752
            ·
              exact block_sound S042.checked (by omega) (by omega)
            ·
              exact block_sound S043.checked (by omega) (by omega)
          ·
            by_cases h45 : i < 2880
            ·
              exact block_sound S044.checked (by omega) (by omega)
            ·
              exact block_sound S045.checked (by omega) (by omega)
    ·
      by_cases h54 : i < 3456
      ·
        by_cases h50 : i < 3200
        ·
          by_cases h48 : i < 3072
          ·
            by_cases h47 : i < 3008
            ·
              exact block_sound S046.checked (by omega) (by omega)
            ·
              exact block_sound S047.checked (by omega) (by omega)
          ·
            by_cases h49 : i < 3136
            ·
              exact block_sound S048.checked (by omega) (by omega)
            ·
              exact block_sound S049.checked (by omega) (by omega)
        ·
          by_cases h52 : i < 3328
          ·
            by_cases h51 : i < 3264
            ·
              exact block_sound S050.checked (by omega) (by omega)
            ·
              exact block_sound S051.checked (by omega) (by omega)
          ·
            by_cases h53 : i < 3392
            ·
              exact block_sound S052.checked (by omega) (by omega)
            ·
              exact block_sound S053.checked (by omega) (by omega)
      ·
        by_cases h58 : i < 3712
        ·
          by_cases h56 : i < 3584
          ·
            by_cases h55 : i < 3520
            ·
              exact block_sound S054.checked (by omega) (by omega)
            ·
              exact block_sound S055.checked (by omega) (by omega)
          ·
            by_cases h57 : i < 3648
            ·
              exact block_sound S056.checked (by omega) (by omega)
            ·
              exact block_sound S057.checked (by omega) (by omega)
        ·
          by_cases h60 : i < 3840
          ·
            by_cases h59 : i < 3776
            ·
              exact block_sound S058.checked (by omega) (by omega)
            ·
              exact block_sound S059.checked (by omega) (by omega)
          ·
            by_cases h61 : i < 3904
            ·
              exact block_sound S060.checked (by omega) (by omega)
            ·
              exact block_sound S061.checked (by omega) (by omega)
#print axioms code_crosswalk
end M6.SourceCrosswalk
