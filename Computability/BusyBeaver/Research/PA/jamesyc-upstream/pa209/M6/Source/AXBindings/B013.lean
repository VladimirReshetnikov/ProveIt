module
public import M6.Legacy213.FastCodes
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row2087_p0 : resolveAt exactSites 2087 = some (AXPushParam.relocate 2062 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p1 : resolveAt exactSites 2088 = some (AXPushParam.relocate 2062 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p2 : resolveAt exactSites 2089 = some (AXPushParam.relocate 2062 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p3 : resolveAt exactSites 2090 = some (AXPushParam.relocate 2062 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p4 : resolveAt exactSites 2091 = some (AXPushParam.relocate 2062 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p5 : resolveAt exactSites 2092 = some (AXPushParam.relocate 2062 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p6 : resolveAt exactSites 2093 = some (AXPushParam.relocate 2062 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p7 : resolveAt exactSites 2094 = some (AXPushParam.relocate 2062 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p8 : resolveAt exactSites 2095 = some (AXPushParam.relocate 2062 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p9 : resolveAt exactSites 2096 = some (AXPushParam.relocate 2062 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p10 : resolveAt exactSites 2097 = some (AXPushParam.relocate 2062 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p11 : resolveAt exactSites 2098 = some (AXPushParam.relocate 2062 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p12 : resolveAt exactSites 2099 = some (AXPushParam.relocate 2062 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p13 : resolveAt exactSites 2100 = some (AXPushParam.relocate 2062 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p14 : resolveAt exactSites 2101 = some (AXPushParam.relocate 2062 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p15 : resolveAt exactSites 2102 = some (AXPushParam.relocate 2062 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p16 : resolveAt exactSites 2103 = some (AXPushParam.relocate 2062 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p17 : resolveAt exactSites 2104 = some (AXPushParam.relocate 2062 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2087_p18 : resolveAt exactSites 2105 = some (AXPushParam.relocate 2062 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2087_p : AXPushParam.Bound exactSites 2062 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2087_p0
  · exact row2087_p1
  · exact row2087_p2
  · exact row2087_p3
  · exact row2087_p4
  · exact row2087_p5
  · exact row2087_p6
  · exact row2087_p7
  · exact row2087_p8
  · exact row2087_p9
  · exact row2087_p10
  · exact row2087_p11
  · exact row2087_p12
  · exact row2087_p13
  · exact row2087_p14
  · exact row2087_p15
  · exact row2087_p16
  · exact row2087_p17
  · exact row2087_p18
theorem block2087 : AXMacro.Realizes exactSites .push 2087 2106 :=
  AXMacro.push_realizes bound2087_p
private theorem row2106_c0 : resolveAt exactSites 2106 = some (CopyToT.expected 5 2106 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2106_c1 : resolveAt exactSites 2107 = some (CopyToT.expected 5 2106 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2106_c2 : resolveAt exactSites 2108 = some (CopyToT.expected 5 2106 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2106_c3 : resolveAt exactSites 2109 = some (CopyToT.expected 5 2106 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2106_c4 : resolveAt exactSites 2110 = some (CopyToT.expected 5 2106 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2106_c5 : resolveAt exactSites 2111 = some (CopyToT.expected 5 2106 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2106_c6 : resolveAt exactSites 2112 = some (CopyToT.expected 5 2106 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2106_c : CopyToT.Bound exactSites 5 2106 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2106_c0
  · exact row2106_c1
  · exact row2106_c2
  · exact row2106_c3
  · exact row2106_c4
  · exact row2106_c5
  · exact row2106_c6
theorem block2106 : AXMacro.Realizes exactSites .copyH 2106 2113 :=
  AXMacro.copyH_realizes bound2106_c
private theorem row2113_p0 : resolveAt exactSites 2113 = some (AXPushParam.relocate 2088 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p1 : resolveAt exactSites 2114 = some (AXPushParam.relocate 2088 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p2 : resolveAt exactSites 2115 = some (AXPushParam.relocate 2088 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p3 : resolveAt exactSites 2116 = some (AXPushParam.relocate 2088 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p4 : resolveAt exactSites 2117 = some (AXPushParam.relocate 2088 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p5 : resolveAt exactSites 2118 = some (AXPushParam.relocate 2088 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p6 : resolveAt exactSites 2119 = some (AXPushParam.relocate 2088 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p7 : resolveAt exactSites 2120 = some (AXPushParam.relocate 2088 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p8 : resolveAt exactSites 2121 = some (AXPushParam.relocate 2088 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p9 : resolveAt exactSites 2122 = some (AXPushParam.relocate 2088 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p10 : resolveAt exactSites 2123 = some (AXPushParam.relocate 2088 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p11 : resolveAt exactSites 2124 = some (AXPushParam.relocate 2088 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p12 : resolveAt exactSites 2125 = some (AXPushParam.relocate 2088 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p13 : resolveAt exactSites 2126 = some (AXPushParam.relocate 2088 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p14 : resolveAt exactSites 2127 = some (AXPushParam.relocate 2088 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p15 : resolveAt exactSites 2128 = some (AXPushParam.relocate 2088 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p16 : resolveAt exactSites 2129 = some (AXPushParam.relocate 2088 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p17 : resolveAt exactSites 2130 = some (AXPushParam.relocate 2088 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2113_p18 : resolveAt exactSites 2131 = some (AXPushParam.relocate 2088 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2113_p : AXPushParam.Bound exactSites 2088 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2113_p0
  · exact row2113_p1
  · exact row2113_p2
  · exact row2113_p3
  · exact row2113_p4
  · exact row2113_p5
  · exact row2113_p6
  · exact row2113_p7
  · exact row2113_p8
  · exact row2113_p9
  · exact row2113_p10
  · exact row2113_p11
  · exact row2113_p12
  · exact row2113_p13
  · exact row2113_p14
  · exact row2113_p15
  · exact row2113_p16
  · exact row2113_p17
  · exact row2113_p18
theorem block2113 : AXMacro.Realizes exactSites .push 2113 2132 :=
  AXMacro.push_realizes bound2113_p
private theorem row2132_c0 : resolveAt exactSites 2132 = some (CopyToT.expected 3 2132 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2132_c1 : resolveAt exactSites 2133 = some (CopyToT.expected 3 2132 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2132_c2 : resolveAt exactSites 2134 = some (CopyToT.expected 3 2132 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2132_c3 : resolveAt exactSites 2135 = some (CopyToT.expected 3 2132 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2132_c4 : resolveAt exactSites 2136 = some (CopyToT.expected 3 2132 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2132_c5 : resolveAt exactSites 2137 = some (CopyToT.expected 3 2132 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2132_c6 : resolveAt exactSites 2138 = some (CopyToT.expected 3 2132 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2132_c : CopyToT.Bound exactSites 3 2132 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2132_c0
  · exact row2132_c1
  · exact row2132_c2
  · exact row2132_c3
  · exact row2132_c4
  · exact row2132_c5
  · exact row2132_c6
theorem block2132 : AXMacro.Realizes exactSites .copyA 2132 2139 :=
  AXMacro.copyA_realizes bound2132_c
private theorem row2139_u0 : resolveAt exactSites 2139 = some (UnpairPartial.expected 2139 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u1 : resolveAt exactSites 2140 = some (UnpairPartial.expected 2139 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u2 : resolveAt exactSites 2141 = some (UnpairPartial.expected 2139 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u3 : resolveAt exactSites 2142 = some (UnpairPartial.expected 2139 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u4 : resolveAt exactSites 2143 = some (UnpairPartial.expected 2139 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u5 : resolveAt exactSites 2144 = some (UnpairPartial.expected 2139 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u6 : resolveAt exactSites 2145 = some (UnpairPartial.expected 2139 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u7 : resolveAt exactSites 2146 = some (UnpairPartial.expected 2139 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u8 : resolveAt exactSites 2147 = some (UnpairPartial.expected 2139 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u9 : resolveAt exactSites 2148 = some (UnpairPartial.expected 2139 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_u10 : resolveAt exactSites 2149 = some (UnpairPartial.expected 2139 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2139_u : UnpairPartial.Bound exactSites 2139 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2139_u0
  · exact row2139_u1
  · exact row2139_u2
  · exact row2139_u3
  · exact row2139_u4
  · exact row2139_u5
  · exact row2139_u6
  · exact row2139_u7
  · exact row2139_u8
  · exact row2139_u9
  · exact row2139_u10
private theorem row2139_q0 : resolveAt exactSites 2150 = some (AXPair.relocate 2119 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q1 : resolveAt exactSites 2151 = some (AXPair.relocate 2119 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q2 : resolveAt exactSites 2152 = some (AXPair.relocate 2119 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q3 : resolveAt exactSites 2153 = some (AXPair.relocate 2119 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q4 : resolveAt exactSites 2154 = some (AXPair.relocate 2119 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q5 : resolveAt exactSites 2155 = some (AXPair.relocate 2119 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q6 : resolveAt exactSites 2156 = some (AXPair.relocate 2119 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q7 : resolveAt exactSites 2157 = some (AXPair.relocate 2119 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q8 : resolveAt exactSites 2158 = some (AXPair.relocate 2119 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_q9 : resolveAt exactSites 2159 = some (AXPair.relocate 2119 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2139_q : AXPair.Bound exactSites 2119 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2139_q0
  · exact row2139_q1
  · exact row2139_q2
  · exact row2139_q3
  · exact row2139_q4
  · exact row2139_q5
  · exact row2139_q6
  · exact row2139_q7
  · exact row2139_q8
  · exact row2139_q9
private theorem row2139_m0 : resolveAt exactSites 2160 = some (AXTimes4.expected 2160 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_m1 : resolveAt exactSites 2161 = some (AXTimes4.expected 2160 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_m2 : resolveAt exactSites 2162 = some (AXTimes4.expected 2160 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_m3 : resolveAt exactSites 2163 = some (AXTimes4.expected 2160 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_m4 : resolveAt exactSites 2164 = some (AXTimes4.expected 2160 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2139_m5 : resolveAt exactSites 2165 = some (AXTimes4.expected 2160 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2139_m : AXTimes4.Bound exactSites 2160 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2139_m0
  · exact row2139_m1
  · exact row2139_m2
  · exact row2139_m3
  · exact row2139_m4
  · exact row2139_m5
theorem block2139 : AXMacro.Realizes exactSites .cons 2139 2166 :=
  AXMacro.cons_realizes bound2139_u bound2139_q bound2139_m
private theorem row2166_u0 : resolveAt exactSites 2166 = some (UnpairPartial.expected 2166 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u1 : resolveAt exactSites 2167 = some (UnpairPartial.expected 2166 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u2 : resolveAt exactSites 2168 = some (UnpairPartial.expected 2166 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u3 : resolveAt exactSites 2169 = some (UnpairPartial.expected 2166 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u4 : resolveAt exactSites 2170 = some (UnpairPartial.expected 2166 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u5 : resolveAt exactSites 2171 = some (UnpairPartial.expected 2166 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u6 : resolveAt exactSites 2172 = some (UnpairPartial.expected 2166 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u7 : resolveAt exactSites 2173 = some (UnpairPartial.expected 2166 7) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u8 : resolveAt exactSites 2174 = some (UnpairPartial.expected 2166 8) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u9 : resolveAt exactSites 2175 = some (UnpairPartial.expected 2166 9) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_u10 : resolveAt exactSites 2176 = some (UnpairPartial.expected 2166 10) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2166_u : UnpairPartial.Bound exactSites 2166 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2166_u0
  · exact row2166_u1
  · exact row2166_u2
  · exact row2166_u3
  · exact row2166_u4
  · exact row2166_u5
  · exact row2166_u6
  · exact row2166_u7
  · exact row2166_u8
  · exact row2166_u9
  · exact row2166_u10
private theorem row2166_q0 : resolveAt exactSites 2177 = some (AXPair.relocate 2146 (AXPair.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q1 : resolveAt exactSites 2178 = some (AXPair.relocate 2146 (AXPair.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q2 : resolveAt exactSites 2179 = some (AXPair.relocate 2146 (AXPair.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q3 : resolveAt exactSites 2180 = some (AXPair.relocate 2146 (AXPair.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q4 : resolveAt exactSites 2181 = some (AXPair.relocate 2146 (AXPair.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q5 : resolveAt exactSites 2182 = some (AXPair.relocate 2146 (AXPair.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q6 : resolveAt exactSites 2183 = some (AXPair.relocate 2146 (AXPair.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q7 : resolveAt exactSites 2184 = some (AXPair.relocate 2146 (AXPair.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q8 : resolveAt exactSites 2185 = some (AXPair.relocate 2146 (AXPair.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_q9 : resolveAt exactSites 2186 = some (AXPair.relocate 2146 (AXPair.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2166_q : AXPair.Bound exactSites 2146 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2166_q0
  · exact row2166_q1
  · exact row2166_q2
  · exact row2166_q3
  · exact row2166_q4
  · exact row2166_q5
  · exact row2166_q6
  · exact row2166_q7
  · exact row2166_q8
  · exact row2166_q9
private theorem row2166_m0 : resolveAt exactSites 2187 = some (AXTimes4.expected 2187 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_m1 : resolveAt exactSites 2188 = some (AXTimes4.expected 2187 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_m2 : resolveAt exactSites 2189 = some (AXTimes4.expected 2187 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_m3 : resolveAt exactSites 2190 = some (AXTimes4.expected 2187 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_m4 : resolveAt exactSites 2191 = some (AXTimes4.expected 2187 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2166_m5 : resolveAt exactSites 2192 = some (AXTimes4.expected 2187 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2166_m : AXTimes4.Bound exactSites 2187 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2166_m0
  · exact row2166_m1
  · exact row2166_m2
  · exact row2166_m3
  · exact row2166_m4
  · exact row2166_m5
theorem block2166 : AXMacro.Realizes exactSites .cons 2166 2193 :=
  AXMacro.cons_realizes bound2166_u bound2166_q bound2166_m
private theorem row2193_i0 : resolveAt exactSites 2193 = some (Instruction.inc 1 (some 2194)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2193 : AXMacro.Realizes exactSites .incT 2193 2194 :=
  AXMacro.inc_realizes row2193_i0
private theorem row2194_i0 : resolveAt exactSites 2194 = some (Instruction.inc 1 (some 2195)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
theorem block2194 : AXMacro.Realizes exactSites .incT 2194 2195 :=
  AXMacro.inc_realizes row2194_i0
private theorem row2195_p0 : resolveAt exactSites 2195 = some (AXPushParam.relocate 2170 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p1 : resolveAt exactSites 2196 = some (AXPushParam.relocate 2170 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p2 : resolveAt exactSites 2197 = some (AXPushParam.relocate 2170 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p3 : resolveAt exactSites 2198 = some (AXPushParam.relocate 2170 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p4 : resolveAt exactSites 2199 = some (AXPushParam.relocate 2170 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p5 : resolveAt exactSites 2200 = some (AXPushParam.relocate 2170 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p6 : resolveAt exactSites 2201 = some (AXPushParam.relocate 2170 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p7 : resolveAt exactSites 2202 = some (AXPushParam.relocate 2170 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p8 : resolveAt exactSites 2203 = some (AXPushParam.relocate 2170 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p9 : resolveAt exactSites 2204 = some (AXPushParam.relocate 2170 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p10 : resolveAt exactSites 2205 = some (AXPushParam.relocate 2170 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p11 : resolveAt exactSites 2206 = some (AXPushParam.relocate 2170 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p12 : resolveAt exactSites 2207 = some (AXPushParam.relocate 2170 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p13 : resolveAt exactSites 2208 = some (AXPushParam.relocate 2170 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p14 : resolveAt exactSites 2209 = some (AXPushParam.relocate 2170 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p15 : resolveAt exactSites 2210 = some (AXPushParam.relocate 2170 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p16 : resolveAt exactSites 2211 = some (AXPushParam.relocate 2170 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p17 : resolveAt exactSites 2212 = some (AXPushParam.relocate 2170 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2195_p18 : resolveAt exactSites 2213 = some (AXPushParam.relocate 2170 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2195_p : AXPushParam.Bound exactSites 2170 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2195_p0
  · exact row2195_p1
  · exact row2195_p2
  · exact row2195_p3
  · exact row2195_p4
  · exact row2195_p5
  · exact row2195_p6
  · exact row2195_p7
  · exact row2195_p8
  · exact row2195_p9
  · exact row2195_p10
  · exact row2195_p11
  · exact row2195_p12
  · exact row2195_p13
  · exact row2195_p14
  · exact row2195_p15
  · exact row2195_p16
  · exact row2195_p17
  · exact row2195_p18
theorem block2195 : AXMacro.Realizes exactSites .push 2195 2214 :=
  AXMacro.push_realizes bound2195_p
private theorem row2214_c0 : resolveAt exactSites 2214 = some (CopyToT.expected 4 2214 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2214_c1 : resolveAt exactSites 2215 = some (CopyToT.expected 4 2214 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2214_c2 : resolveAt exactSites 2216 = some (CopyToT.expected 4 2214 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2214_c3 : resolveAt exactSites 2217 = some (CopyToT.expected 4 2214 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2214_c4 : resolveAt exactSites 2218 = some (CopyToT.expected 4 2214 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2214_c5 : resolveAt exactSites 2219 = some (CopyToT.expected 4 2214 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2214_c6 : resolveAt exactSites 2220 = some (CopyToT.expected 4 2214 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2214_c : CopyToT.Bound exactSites 4 2214 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2214_c0
  · exact row2214_c1
  · exact row2214_c2
  · exact row2214_c3
  · exact row2214_c4
  · exact row2214_c5
  · exact row2214_c6
theorem block2214 : AXMacro.Realizes exactSites .copyD 2214 2221 :=
  AXMacro.copyD_realizes bound2214_c
private theorem row2221_p0 : resolveAt exactSites 2221 = some (AXPushParam.relocate 2196 (AXPushParam.expected 0)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p1 : resolveAt exactSites 2222 = some (AXPushParam.relocate 2196 (AXPushParam.expected 1)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p2 : resolveAt exactSites 2223 = some (AXPushParam.relocate 2196 (AXPushParam.expected 2)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p3 : resolveAt exactSites 2224 = some (AXPushParam.relocate 2196 (AXPushParam.expected 3)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p4 : resolveAt exactSites 2225 = some (AXPushParam.relocate 2196 (AXPushParam.expected 4)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p5 : resolveAt exactSites 2226 = some (AXPushParam.relocate 2196 (AXPushParam.expected 5)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p6 : resolveAt exactSites 2227 = some (AXPushParam.relocate 2196 (AXPushParam.expected 6)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p7 : resolveAt exactSites 2228 = some (AXPushParam.relocate 2196 (AXPushParam.expected 7)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p8 : resolveAt exactSites 2229 = some (AXPushParam.relocate 2196 (AXPushParam.expected 8)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p9 : resolveAt exactSites 2230 = some (AXPushParam.relocate 2196 (AXPushParam.expected 9)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p10 : resolveAt exactSites 2231 = some (AXPushParam.relocate 2196 (AXPushParam.expected 10)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p11 : resolveAt exactSites 2232 = some (AXPushParam.relocate 2196 (AXPushParam.expected 11)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p12 : resolveAt exactSites 2233 = some (AXPushParam.relocate 2196 (AXPushParam.expected 12)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p13 : resolveAt exactSites 2234 = some (AXPushParam.relocate 2196 (AXPushParam.expected 13)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p14 : resolveAt exactSites 2235 = some (AXPushParam.relocate 2196 (AXPushParam.expected 14)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p15 : resolveAt exactSites 2236 = some (AXPushParam.relocate 2196 (AXPushParam.expected 15)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p16 : resolveAt exactSites 2237 = some (AXPushParam.relocate 2196 (AXPushParam.expected 16)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p17 : resolveAt exactSites 2238 = some (AXPushParam.relocate 2196 (AXPushParam.expected 17)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2221_p18 : resolveAt exactSites 2239 = some (AXPushParam.relocate 2196 (AXPushParam.expected 18)) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2221_p : AXPushParam.Bound exactSites 2196 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2221_p0
  · exact row2221_p1
  · exact row2221_p2
  · exact row2221_p3
  · exact row2221_p4
  · exact row2221_p5
  · exact row2221_p6
  · exact row2221_p7
  · exact row2221_p8
  · exact row2221_p9
  · exact row2221_p10
  · exact row2221_p11
  · exact row2221_p12
  · exact row2221_p13
  · exact row2221_p14
  · exact row2221_p15
  · exact row2221_p16
  · exact row2221_p17
  · exact row2221_p18
theorem block2221 : AXMacro.Realizes exactSites .push 2221 2240 :=
  AXMacro.push_realizes bound2221_p
private theorem row2240_c0 : resolveAt exactSites 2240 = some (CopyToT.expected 5 2240 0) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2240_c1 : resolveAt exactSites 2241 = some (CopyToT.expected 5 2240 1) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2240_c2 : resolveAt exactSites 2242 = some (CopyToT.expected 5 2240 2) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2240_c3 : resolveAt exactSites 2243 = some (CopyToT.expected 5 2240 3) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2240_c4 : resolveAt exactSites 2244 = some (CopyToT.expected 5 2240 4) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2240_c5 : resolveAt exactSites 2245 = some (CopyToT.expected 5 2240 5) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem row2240_c6 : resolveAt exactSites 2246 = some (CopyToT.expected 5 2240 6) := by
  rw [M6.Legacy213.FastCodes.baseline_resolve]
  rfl
private theorem bound2240_c : CopyToT.Bound exactSites 5 2240 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2240_c0
  · exact row2240_c1
  · exact row2240_c2
  · exact row2240_c3
  · exact row2240_c4
  · exact row2240_c5
  · exact row2240_c6
theorem block2240 : AXMacro.Realizes exactSites .copyH 2240 2247 :=
  AXMacro.copyH_realizes bound2240_c
def code013 : List AXMacro.Op := [.push,.copyH,.push,.copyA,.cons,.cons,.incT,.incT,.push,.copyD,.push,.copyH]
theorem plan013 : AXMacro.Plan exactSites 2087 2247 code013 :=
  AXMacro.Plan.cons block2087 ( AXMacro.Plan.cons block2106 ( AXMacro.Plan.cons block2113 ( AXMacro.Plan.cons block2132 ( AXMacro.Plan.cons block2139 ( AXMacro.Plan.cons block2166 ( AXMacro.Plan.cons block2193 ( AXMacro.Plan.cons block2194 ( AXMacro.Plan.cons block2195 ( AXMacro.Plan.cons block2214 ( AXMacro.Plan.cons block2221 ( AXMacro.Plan.cons block2240 ( AXMacro.Plan.nil 2247))))))))))))
#print axioms plan013
end M6.Source.AXAll

