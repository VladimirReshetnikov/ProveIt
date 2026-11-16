import PA194HXContracts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXNativeLabels
/-- Native control name attached to each dense control of the HX literal table. -/
def labels : List Nat := [74, 0, 64, 94, 66, 198, 54, 40, 113, 4, 302, 97, 6, 10, 16, 1, 2, 3, 5, 9, 15, 23, 34, 75, 84, 53, 310, 68, 69, 214, 62, 77, 213, 31, 188, 312, 28, 73, 87, 88, 92, 90, 21, 47, 95, 111, 11, 38, 41, 42, 82, 83, 301, 122, 103, 104, 185, 105, 106, 24, 55, 63, 27, 110, 128, 26, 18, 20, 25, 13, 49, 33, 93, 45, 137, 108, 123, 124, 107, 98, 72, 59, 58, 125, 35, 22, 30, 39, 127, 8, 141, 194, 96, 36, 91, 32, 109, 60, 70, 138, 126, 19, 114, 56, 81, 71, 139, 46, 14, 161, 17, 101, 100, 51, 48, 130, 29, 57, 80, 190, 61, 2000, 174, 164, 144, 43, 44, 99, 2001, 2033, 2002, 2005, 2034, 2039, 12, 2003, 2006, 2023, 2025, 2035, 2052, 2040, 2004, 2007, 2014, 2046, 2029, 2026, 2036, 166, 2041, 2066, 2008, 2050, 2064, 2028, 2030, 2031, 2027, 2015, 179, 2042, 2047, 221, 2009, 2019, 2051, 2065, 2032, 2020, 2044, 2017, 2043, 2048, 2053, 196, 217, 2010, 2011, 2059, 2056, 2061, 2021, 2045, 2049, 2054, 197, 2012, 2063, 2057, 2058, 2062, 2038, 2013, 254]
def nativeOf (q : Nat) : Nat := labels[q]?.getD 254

def mapped (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  (PA194HX.Literal.machine q b).map (fun (w,d,k) => (w,d,nativeOf k))

def rowCheck (q : Nat) : Bool :=
  (PA194HXContracts.cachedMachine (nativeOf q) false == mapped q false) &&
  (PA194HXContracts.cachedMachine (nativeOf q) true == mapped q true)

def blockCheck (base count : Nat) : Bool :=
  (List.range count).all (fun j => rowCheck (base+j))

theorem size : labels.length = 195 := by decide +kernel
theorem distinct : labels.Nodup := by decide +kernel
theorem initial : nativeOf 0 = 74 := by decide +kernel
theorem terminal : nativeOf 194 = 254 := by decide +kernel
theorem rows0 : blockCheck 0 8 = true := by decide +kernel
theorem rows8 : blockCheck 8 8 = true := by decide +kernel
theorem rows16 : blockCheck 16 8 = true := by decide +kernel
theorem rows24 : blockCheck 24 8 = true := by decide +kernel
theorem rows32 : blockCheck 32 8 = true := by decide +kernel
theorem rows40 : blockCheck 40 8 = true := by decide +kernel
theorem rows48 : blockCheck 48 8 = true := by decide +kernel
theorem rows56 : blockCheck 56 8 = true := by decide +kernel
theorem rows64 : blockCheck 64 8 = true := by decide +kernel
theorem rows72 : blockCheck 72 8 = true := by decide +kernel
theorem rows80 : blockCheck 80 8 = true := by decide +kernel
theorem rows88 : blockCheck 88 8 = true := by decide +kernel
theorem rows96 : blockCheck 96 8 = true := by decide +kernel
theorem rows104 : blockCheck 104 8 = true := by decide +kernel
theorem rows112 : blockCheck 112 8 = true := by decide +kernel
theorem rows120 : blockCheck 120 8 = true := by decide +kernel
theorem rows128 : blockCheck 128 8 = true := by decide +kernel
theorem rows136 : blockCheck 136 8 = true := by decide +kernel
theorem rows144 : blockCheck 144 8 = true := by decide +kernel
theorem rows152 : blockCheck 152 8 = true := by decide +kernel
theorem rows160 : blockCheck 160 8 = true := by decide +kernel
theorem rows168 : blockCheck 168 8 = true := by decide +kernel
theorem rows176 : blockCheck 176 8 = true := by decide +kernel
theorem rows184 : blockCheck 184 8 = true := by decide +kernel
theorem rows192 : blockCheck 192 2 = true := by decide +kernel

#print axioms rows0
#print axioms rows192
end PA194HXNativeLabels
