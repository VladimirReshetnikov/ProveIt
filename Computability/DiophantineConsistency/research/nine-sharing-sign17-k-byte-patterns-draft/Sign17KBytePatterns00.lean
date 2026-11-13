import DiophantineConsistency.Sign17KRadixStreamCurrent

/-! SOURCE ONLY. Radix/byte numeric fixtures; source file provenance is external. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KBytePatterns00

theorem pattern000 :
    Nat.ofDigits CurrentKernel2011.radix [0, 0, 0, 0, 0, 0, 0, 0] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem pattern001 :
    Nat.ofDigits CurrentKernel2011.radix [0, 0, 1, 0, 262144, 131072, 65536, 32768] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  decide +kernel

theorem pattern002 :
    Nat.ofDigits CurrentKernel2011.radix [16384, 8192, 4096, 2048, 0, 34359738368, 17179869184, 8589934592] =
      Nat.ofDigits 256 [0, 64, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 4, 0] := by
  decide +kernel

theorem pattern003 :
    Nat.ofDigits CurrentKernel2011.radix [4294967296, 2147483648, 1073741824, 536870912, 268435456, 134217728, 67108864, 33554432] =
      Nat.ofDigits 256 [0, 0, 0, 0, 1, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 4, 0, 0] := by
  decide +kernel

theorem pattern004 :
    Nat.ofDigits CurrentKernel2011.radix [16777216, 8388608, 4194304, 2097152, 1048576, 524288, 0, 0] =
      Nat.ofDigits 256 [0, 0, 0, 1, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem pattern005 :
    Nat.ofDigits CurrentKernel2011.radix [0, 0, 0, 0, 0, 0, 0, 17592186044416] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32] := by
  decide +kernel

theorem pattern006 :
    Nat.ofDigits CurrentKernel2011.radix [8796093022208, 4398046511104, 2199023255552, 1099511627776, 549755813888, 274877906944, 137438953472, 68719476736] =
      Nat.ofDigits 256 [0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 32, 0] := by
  decide +kernel

theorem pattern007 :
    Nat.ofDigits CurrentKernel2011.radix [2050, 5666818, 6719490, 7770114, 8296450, 9340930, 9865218, 10391554] =
      Nat.ofDigits 256 [2, 8, 0, 0, 0, 0, 1, 60, 43, 0, 0, 128, 0, 162, 25, 0, 0, 64, 0, 210, 14, 0, 0, 32, 128, 233, 7, 0, 0, 16, 64, 116, 4, 0, 0, 8, 32, 90, 2, 0, 0, 4, 32, 61, 1, 0, 0] := by
  decide +kernel

theorem pattern008 :
    Nat.ofDigits CurrentKernel2011.radix [13019138, 14594050, 15118338, 16171010, 17221634, 18272258, 19322882, 20373506] =
      Nat.ofDigits 256 [2, 168, 198, 0, 0, 0, 1, 88, 111, 0, 0, 128, 0, 172, 57, 0, 0, 64, 0, 216, 30, 0, 0, 32, 128, 108, 16, 0, 0, 16, 128, 182, 8, 0, 0, 8, 96, 155, 4, 0, 0, 4, 192, 109, 2, 0, 0] := by
  decide +kernel

theorem pattern009 :
    Nat.ofDigits CurrentKernel2011.radix [21424130, 22474754, 23525378, 29259778, 32968706, 40306690, 42405890, 44511234] =
      Nat.ofDigits 256 [2, 232, 70, 1, 0, 0, 1, 120, 171, 0, 0, 128, 0, 190, 89, 0, 0, 64, 0, 207, 55, 0, 0, 32, 0, 113, 31, 0, 0, 16, 64, 56, 19, 0, 0, 8, 64, 28, 10, 0, 0, 4, 96, 78, 5, 0, 0] := by
  decide +kernel

theorem pattern010 :
    Nat.ofDigits CurrentKernel2011.radix [49195010, 51286018, 60250114, 61300738, 67594242, 68644866, 74907650, 76457986] =
      Nat.ofDigits 256 [2, 168, 238, 2, 0, 0, 1, 72, 135, 1, 0, 128, 0, 214, 229, 0, 0, 64, 0, 236, 116, 0, 0, 32, 128, 118, 64, 0, 0, 16, 128, 187, 32, 0, 0, 8, 0, 220, 17, 0, 0, 4, 80, 29, 9, 0, 0] := by
  decide +kernel

theorem pattern011 :
    Nat.ofDigits CurrentKernel2011.radix [77563906, 81223682, 87527426, 93235202, 93790210, 96380930, 100569090, 114200578] =
      Nat.ofDigits 256 [2, 136, 159, 4, 0, 0, 1, 176, 107, 2, 0, 128, 0, 228, 77, 1, 0, 64, 0, 213, 177, 0, 0, 32, 0, 114, 89, 0, 0, 16, 64, 245, 45, 0, 0, 8, 64, 250, 23, 0, 0, 4, 32, 157, 13, 0, 0] := by
  decide +kernel

theorem pattern012 :
    Nat.ofDigits CurrentKernel2011.radix [118398978, 124233730, 124694530, 125734914, 153595906, 159889410, 160894978, 163489794] =
      Nat.ofDigits 256 [2, 160, 14, 7, 0, 0, 1, 212, 179, 3, 0, 128, 0, 172, 219, 1, 0, 64, 0, 210, 239, 0, 0, 32, 0, 123, 146, 0, 0, 16, 192, 61, 76, 0, 0, 8, 64, 92, 38, 0, 0, 4, 80, 125, 19, 0, 0] := by
  decide +kernel

theorem pattern013 :
    Nat.ofDigits CurrentKernel2011.radix [164048898, 165586946, 191348738, 194496514, 764418050, 1302341634, 1613236226, 1671956482] =
      Nat.ofDigits 256 [2, 48, 199, 9, 0, 0, 1, 84, 239, 4, 0, 128, 0, 240, 217, 2, 0, 64, 0, 249, 114, 1, 0, 32, 128, 1, 217, 2, 0, 16, 64, 1, 109, 2, 0, 8, 32, 160, 128, 1, 0, 4, 16, 80, 199, 0, 0] := by
  decide +kernel

theorem pattern014 :
    Nat.ofDigits CurrentKernel2011.radix [2149582850, 2695890946, 2964850690, 2965899266, 3274704898, 3513780226, 4051699714, 4589619202] =
      Nat.ofDigits 256 [2, 8, 32, 128, 0, 0, 1, 4, 88, 80, 0, 128, 0, 2, 46, 44, 0, 64, 0, 1, 25, 22, 0, 32, 128, 0, 51, 12, 0, 16, 64, 128, 139, 6, 0, 8, 32, 0, 198, 3, 0, 4, 16, 32, 35, 2, 0] := by
  decide +kernel

theorem pattern015 :
    Nat.ofDigits CurrentKernel2011.radix [5127538690, 5665458178, 5680138242, 5682235394, 5934942210, 6472861698, 6546262018, 7010781186] =
      Nat.ofDigits 256 [2, 8, 160, 49, 1, 0, 1, 4, 216, 168, 0, 128, 0, 2, 164, 84, 0, 64, 0, 1, 86, 42, 0, 32, 128, 0, 28, 22, 0, 16, 64, 128, 14, 12, 0, 8, 32, 192, 24, 6, 0, 4, 16, 192, 67, 3, 0] := by
  decide +kernel

end DiophantineConsistency.Sign17KBytePatterns00
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern000
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern001
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern002
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern003
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern004
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern005
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern006
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern007
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern008
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern009
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern010
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern011
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern012
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern013
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern014
#print axioms DiophantineConsistency.Sign17KBytePatterns00.pattern015
