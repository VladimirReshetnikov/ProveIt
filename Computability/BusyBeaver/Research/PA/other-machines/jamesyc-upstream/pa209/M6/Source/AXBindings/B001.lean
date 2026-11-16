module
public import M6.Source.AXMacroPlan
public import M6.Source.AXMacroRead
public import M6.Source.AXHead3Plan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXAll
private theorem row172_u0 : resolveAt exactSites 172 = some (UnpairPartial.expected 172 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u1 : resolveAt exactSites 173 = some (UnpairPartial.expected 172 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u2 : resolveAt exactSites 174 = some (UnpairPartial.expected 172 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u3 : resolveAt exactSites 175 = some (UnpairPartial.expected 172 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u4 : resolveAt exactSites 176 = some (UnpairPartial.expected 172 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u5 : resolveAt exactSites 177 = some (UnpairPartial.expected 172 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u6 : resolveAt exactSites 178 = some (UnpairPartial.expected 172 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u7 : resolveAt exactSites 179 = some (UnpairPartial.expected 172 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u8 : resolveAt exactSites 180 = some (UnpairPartial.expected 172 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u9 : resolveAt exactSites 181 = some (UnpairPartial.expected 172 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_u10 : resolveAt exactSites 182 = some (UnpairPartial.expected 172 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound172_u : UnpairPartial.Bound exactSites 172 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row172_u0
  · exact row172_u1
  · exact row172_u2
  · exact row172_u3
  · exact row172_u4
  · exact row172_u5
  · exact row172_u6
  · exact row172_u7
  · exact row172_u8
  · exact row172_u9
  · exact row172_u10
private theorem row172_q0 : resolveAt exactSites 183 = some (AXPair.relocate 152 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q1 : resolveAt exactSites 184 = some (AXPair.relocate 152 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q2 : resolveAt exactSites 185 = some (AXPair.relocate 152 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q3 : resolveAt exactSites 186 = some (AXPair.relocate 152 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q4 : resolveAt exactSites 187 = some (AXPair.relocate 152 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q5 : resolveAt exactSites 188 = some (AXPair.relocate 152 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q6 : resolveAt exactSites 189 = some (AXPair.relocate 152 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q7 : resolveAt exactSites 190 = some (AXPair.relocate 152 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q8 : resolveAt exactSites 191 = some (AXPair.relocate 152 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_q9 : resolveAt exactSites 192 = some (AXPair.relocate 152 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound172_q : AXPair.Bound exactSites 152 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row172_q0
  · exact row172_q1
  · exact row172_q2
  · exact row172_q3
  · exact row172_q4
  · exact row172_q5
  · exact row172_q6
  · exact row172_q7
  · exact row172_q8
  · exact row172_q9
private theorem row172_m0 : resolveAt exactSites 193 = some (AXTimes4.expected 193 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_m1 : resolveAt exactSites 194 = some (AXTimes4.expected 193 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_m2 : resolveAt exactSites 195 = some (AXTimes4.expected 193 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_m3 : resolveAt exactSites 196 = some (AXTimes4.expected 193 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_m4 : resolveAt exactSites 197 = some (AXTimes4.expected 193 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row172_m5 : resolveAt exactSites 198 = some (AXTimes4.expected 193 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound172_m : AXTimes4.Bound exactSites 193 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row172_m0
  · exact row172_m1
  · exact row172_m2
  · exact row172_m3
  · exact row172_m4
  · exact row172_m5
theorem block172 : AXMacro.Realizes exactSites .cons 172 199 :=
  AXMacro.cons_realizes bound172_u bound172_q bound172_m
private theorem row199_r0 : resolveAt exactSites 199 = some ((AXMacro.readerD 199).instruction unpairExpected[0]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r1 : resolveAt exactSites 200 = some ((AXMacro.readerD 199).instruction unpairExpected[1]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r2 : resolveAt exactSites 201 = some ((AXMacro.readerD 199).instruction unpairExpected[2]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r3 : resolveAt exactSites 202 = some ((AXMacro.readerD 199).instruction unpairExpected[3]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r4 : resolveAt exactSites 203 = some ((AXMacro.readerD 199).instruction unpairExpected[4]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r5 : resolveAt exactSites 204 = some ((AXMacro.readerD 199).instruction unpairExpected[5]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r6 : resolveAt exactSites 205 = some ((AXMacro.readerD 199).instruction unpairExpected[6]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r7 : resolveAt exactSites 206 = some ((AXMacro.readerD 199).instruction unpairExpected[7]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r8 : resolveAt exactSites 207 = some ((AXMacro.readerD 199).instruction unpairExpected[8]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r9 : resolveAt exactSites 208 = some ((AXMacro.readerD 199).instruction unpairExpected[9]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r10 : resolveAt exactSites 209 = some ((AXMacro.readerD 199).instruction unpairExpected[10]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r11 : resolveAt exactSites 210 = some ((AXMacro.readerD 199).instruction unpairExpected[11]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r12 : resolveAt exactSites 211 = some ((AXMacro.readerD 199).instruction unpairExpected[12]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row199_r13 : resolveAt exactSites 212 = some ((AXMacro.readerD 199).instruction unpairExpected[13]) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound199_r : (AXMacro.readerD 199).Bound := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row199_r0
  · exact row199_r1
  · exact row199_r2
  · exact row199_r3
  · exact row199_r4
  · exact row199_r5
  · exact row199_r6
  · exact row199_r7
  · exact row199_r8
  · exact row199_r9
  · exact row199_r10
  · exact row199_r11
  · exact row199_r12
  · exact row199_r13
theorem block199 : AXMacro.Realizes exactSites .readD 199 213 :=
  AXMacro.readD_realizes 199 bound199_r
private theorem row213_p0 : resolveAt exactSites 213 = some (AXPushParam.relocate 188 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p1 : resolveAt exactSites 214 = some (AXPushParam.relocate 188 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p2 : resolveAt exactSites 215 = some (AXPushParam.relocate 188 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p3 : resolveAt exactSites 216 = some (AXPushParam.relocate 188 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p4 : resolveAt exactSites 217 = some (AXPushParam.relocate 188 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p5 : resolveAt exactSites 218 = some (AXPushParam.relocate 188 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p6 : resolveAt exactSites 219 = some (AXPushParam.relocate 188 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p7 : resolveAt exactSites 220 = some (AXPushParam.relocate 188 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p8 : resolveAt exactSites 221 = some (AXPushParam.relocate 188 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p9 : resolveAt exactSites 222 = some (AXPushParam.relocate 188 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p10 : resolveAt exactSites 223 = some (AXPushParam.relocate 188 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p11 : resolveAt exactSites 224 = some (AXPushParam.relocate 188 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p12 : resolveAt exactSites 225 = some (AXPushParam.relocate 188 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p13 : resolveAt exactSites 226 = some (AXPushParam.relocate 188 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p14 : resolveAt exactSites 227 = some (AXPushParam.relocate 188 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p15 : resolveAt exactSites 228 = some (AXPushParam.relocate 188 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p16 : resolveAt exactSites 229 = some (AXPushParam.relocate 188 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p17 : resolveAt exactSites 230 = some (AXPushParam.relocate 188 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row213_p18 : resolveAt exactSites 231 = some (AXPushParam.relocate 188 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound213_p : AXPushParam.Bound exactSites 188 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row213_p0
  · exact row213_p1
  · exact row213_p2
  · exact row213_p3
  · exact row213_p4
  · exact row213_p5
  · exact row213_p6
  · exact row213_p7
  · exact row213_p8
  · exact row213_p9
  · exact row213_p10
  · exact row213_p11
  · exact row213_p12
  · exact row213_p13
  · exact row213_p14
  · exact row213_p15
  · exact row213_p16
  · exact row213_p17
  · exact row213_p18
theorem block213 : AXMacro.Realizes exactSites .push 213 232 :=
  AXMacro.push_realizes bound213_p
private theorem row232_c0 : resolveAt exactSites 232 = some (CopyToT.expected 4 232 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row232_c1 : resolveAt exactSites 233 = some (CopyToT.expected 4 232 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row232_c2 : resolveAt exactSites 234 = some (CopyToT.expected 4 232 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row232_c3 : resolveAt exactSites 235 = some (CopyToT.expected 4 232 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row232_c4 : resolveAt exactSites 236 = some (CopyToT.expected 4 232 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row232_c5 : resolveAt exactSites 237 = some (CopyToT.expected 4 232 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row232_c6 : resolveAt exactSites 238 = some (CopyToT.expected 4 232 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound232_c : CopyToT.Bound exactSites 4 232 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row232_c0
  · exact row232_c1
  · exact row232_c2
  · exact row232_c3
  · exact row232_c4
  · exact row232_c5
  · exact row232_c6
theorem block232 : AXMacro.Realizes exactSites .copyD 232 239 :=
  AXMacro.copyD_realizes bound232_c
private theorem row239_u0 : resolveAt exactSites 239 = some (UnpairPartial.expected 239 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u1 : resolveAt exactSites 240 = some (UnpairPartial.expected 239 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u2 : resolveAt exactSites 241 = some (UnpairPartial.expected 239 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u3 : resolveAt exactSites 242 = some (UnpairPartial.expected 239 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u4 : resolveAt exactSites 243 = some (UnpairPartial.expected 239 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u5 : resolveAt exactSites 244 = some (UnpairPartial.expected 239 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u6 : resolveAt exactSites 245 = some (UnpairPartial.expected 239 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u7 : resolveAt exactSites 246 = some (UnpairPartial.expected 239 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u8 : resolveAt exactSites 247 = some (UnpairPartial.expected 239 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u9 : resolveAt exactSites 248 = some (UnpairPartial.expected 239 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_u10 : resolveAt exactSites 249 = some (UnpairPartial.expected 239 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound239_u : UnpairPartial.Bound exactSites 239 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row239_u0
  · exact row239_u1
  · exact row239_u2
  · exact row239_u3
  · exact row239_u4
  · exact row239_u5
  · exact row239_u6
  · exact row239_u7
  · exact row239_u8
  · exact row239_u9
  · exact row239_u10
private theorem row239_q0 : resolveAt exactSites 250 = some (AXPair.relocate 219 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q1 : resolveAt exactSites 251 = some (AXPair.relocate 219 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q2 : resolveAt exactSites 252 = some (AXPair.relocate 219 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q3 : resolveAt exactSites 253 = some (AXPair.relocate 219 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q4 : resolveAt exactSites 254 = some (AXPair.relocate 219 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q5 : resolveAt exactSites 255 = some (AXPair.relocate 219 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q6 : resolveAt exactSites 256 = some (AXPair.relocate 219 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q7 : resolveAt exactSites 257 = some (AXPair.relocate 219 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q8 : resolveAt exactSites 258 = some (AXPair.relocate 219 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_q9 : resolveAt exactSites 259 = some (AXPair.relocate 219 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound239_q : AXPair.Bound exactSites 219 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row239_q0
  · exact row239_q1
  · exact row239_q2
  · exact row239_q3
  · exact row239_q4
  · exact row239_q5
  · exact row239_q6
  · exact row239_q7
  · exact row239_q8
  · exact row239_q9
private theorem row239_m0 : resolveAt exactSites 260 = some (AXTimes4.expected 260 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_m1 : resolveAt exactSites 261 = some (AXTimes4.expected 260 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_m2 : resolveAt exactSites 262 = some (AXTimes4.expected 260 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_m3 : resolveAt exactSites 263 = some (AXTimes4.expected 260 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_m4 : resolveAt exactSites 264 = some (AXTimes4.expected 260 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row239_m5 : resolveAt exactSites 265 = some (AXTimes4.expected 260 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound239_m : AXTimes4.Bound exactSites 260 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row239_m0
  · exact row239_m1
  · exact row239_m2
  · exact row239_m3
  · exact row239_m4
  · exact row239_m5
theorem block239 : AXMacro.Realizes exactSites .cons 239 266 :=
  AXMacro.cons_realizes bound239_u bound239_q bound239_m
private theorem row266_p0 : resolveAt exactSites 266 = some (AXPushParam.relocate 241 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p1 : resolveAt exactSites 267 = some (AXPushParam.relocate 241 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p2 : resolveAt exactSites 268 = some (AXPushParam.relocate 241 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p3 : resolveAt exactSites 269 = some (AXPushParam.relocate 241 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p4 : resolveAt exactSites 270 = some (AXPushParam.relocate 241 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p5 : resolveAt exactSites 271 = some (AXPushParam.relocate 241 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p6 : resolveAt exactSites 272 = some (AXPushParam.relocate 241 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p7 : resolveAt exactSites 273 = some (AXPushParam.relocate 241 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p8 : resolveAt exactSites 274 = some (AXPushParam.relocate 241 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p9 : resolveAt exactSites 275 = some (AXPushParam.relocate 241 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p10 : resolveAt exactSites 276 = some (AXPushParam.relocate 241 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p11 : resolveAt exactSites 277 = some (AXPushParam.relocate 241 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p12 : resolveAt exactSites 278 = some (AXPushParam.relocate 241 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p13 : resolveAt exactSites 279 = some (AXPushParam.relocate 241 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p14 : resolveAt exactSites 280 = some (AXPushParam.relocate 241 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p15 : resolveAt exactSites 281 = some (AXPushParam.relocate 241 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p16 : resolveAt exactSites 282 = some (AXPushParam.relocate 241 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p17 : resolveAt exactSites 283 = some (AXPushParam.relocate 241 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row266_p18 : resolveAt exactSites 284 = some (AXPushParam.relocate 241 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound266_p : AXPushParam.Bound exactSites 241 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row266_p0
  · exact row266_p1
  · exact row266_p2
  · exact row266_p3
  · exact row266_p4
  · exact row266_p5
  · exact row266_p6
  · exact row266_p7
  · exact row266_p8
  · exact row266_p9
  · exact row266_p10
  · exact row266_p11
  · exact row266_p12
  · exact row266_p13
  · exact row266_p14
  · exact row266_p15
  · exact row266_p16
  · exact row266_p17
  · exact row266_p18
theorem block266 : AXMacro.Realizes exactSites .push 266 285 :=
  AXMacro.push_realizes bound266_p
private theorem row285_c0 : resolveAt exactSites 285 = some (CopyToT.expected 4 285 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row285_c1 : resolveAt exactSites 286 = some (CopyToT.expected 4 285 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row285_c2 : resolveAt exactSites 287 = some (CopyToT.expected 4 285 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row285_c3 : resolveAt exactSites 288 = some (CopyToT.expected 4 285 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row285_c4 : resolveAt exactSites 289 = some (CopyToT.expected 4 285 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row285_c5 : resolveAt exactSites 290 = some (CopyToT.expected 4 285 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row285_c6 : resolveAt exactSites 291 = some (CopyToT.expected 4 285 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound285_c : CopyToT.Bound exactSites 4 285 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row285_c0
  · exact row285_c1
  · exact row285_c2
  · exact row285_c3
  · exact row285_c4
  · exact row285_c5
  · exact row285_c6
theorem block285 : AXMacro.Realizes exactSites .copyD 285 292 :=
  AXMacro.copyD_realizes bound285_c
private theorem row292_p0 : resolveAt exactSites 292 = some (AXPushParam.relocate 267 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p1 : resolveAt exactSites 293 = some (AXPushParam.relocate 267 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p2 : resolveAt exactSites 294 = some (AXPushParam.relocate 267 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p3 : resolveAt exactSites 295 = some (AXPushParam.relocate 267 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p4 : resolveAt exactSites 296 = some (AXPushParam.relocate 267 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p5 : resolveAt exactSites 297 = some (AXPushParam.relocate 267 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p6 : resolveAt exactSites 298 = some (AXPushParam.relocate 267 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p7 : resolveAt exactSites 299 = some (AXPushParam.relocate 267 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p8 : resolveAt exactSites 300 = some (AXPushParam.relocate 267 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p9 : resolveAt exactSites 301 = some (AXPushParam.relocate 267 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p10 : resolveAt exactSites 302 = some (AXPushParam.relocate 267 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p11 : resolveAt exactSites 303 = some (AXPushParam.relocate 267 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p12 : resolveAt exactSites 304 = some (AXPushParam.relocate 267 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p13 : resolveAt exactSites 305 = some (AXPushParam.relocate 267 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p14 : resolveAt exactSites 306 = some (AXPushParam.relocate 267 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p15 : resolveAt exactSites 307 = some (AXPushParam.relocate 267 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p16 : resolveAt exactSites 308 = some (AXPushParam.relocate 267 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p17 : resolveAt exactSites 309 = some (AXPushParam.relocate 267 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row292_p18 : resolveAt exactSites 310 = some (AXPushParam.relocate 267 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound292_p : AXPushParam.Bound exactSites 267 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row292_p0
  · exact row292_p1
  · exact row292_p2
  · exact row292_p3
  · exact row292_p4
  · exact row292_p5
  · exact row292_p6
  · exact row292_p7
  · exact row292_p8
  · exact row292_p9
  · exact row292_p10
  · exact row292_p11
  · exact row292_p12
  · exact row292_p13
  · exact row292_p14
  · exact row292_p15
  · exact row292_p16
  · exact row292_p17
  · exact row292_p18
theorem block292 : AXMacro.Realizes exactSites .push 292 311 :=
  AXMacro.push_realizes bound292_p
private theorem row311_c0 : resolveAt exactSites 311 = some (CopyToT.expected 3 311 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row311_c1 : resolveAt exactSites 312 = some (CopyToT.expected 3 311 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row311_c2 : resolveAt exactSites 313 = some (CopyToT.expected 3 311 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row311_c3 : resolveAt exactSites 314 = some (CopyToT.expected 3 311 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row311_c4 : resolveAt exactSites 315 = some (CopyToT.expected 3 311 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row311_c5 : resolveAt exactSites 316 = some (CopyToT.expected 3 311 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row311_c6 : resolveAt exactSites 317 = some (CopyToT.expected 3 311 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound311_c : CopyToT.Bound exactSites 3 311 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row311_c0
  · exact row311_c1
  · exact row311_c2
  · exact row311_c3
  · exact row311_c4
  · exact row311_c5
  · exact row311_c6
theorem block311 : AXMacro.Realizes exactSites .copyA 311 318 :=
  AXMacro.copyA_realizes bound311_c
private theorem row318_u0 : resolveAt exactSites 318 = some (UnpairPartial.expected 318 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u1 : resolveAt exactSites 319 = some (UnpairPartial.expected 318 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u2 : resolveAt exactSites 320 = some (UnpairPartial.expected 318 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u3 : resolveAt exactSites 321 = some (UnpairPartial.expected 318 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u4 : resolveAt exactSites 322 = some (UnpairPartial.expected 318 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u5 : resolveAt exactSites 323 = some (UnpairPartial.expected 318 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u6 : resolveAt exactSites 324 = some (UnpairPartial.expected 318 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u7 : resolveAt exactSites 325 = some (UnpairPartial.expected 318 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u8 : resolveAt exactSites 326 = some (UnpairPartial.expected 318 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u9 : resolveAt exactSites 327 = some (UnpairPartial.expected 318 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_u10 : resolveAt exactSites 328 = some (UnpairPartial.expected 318 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound318_u : UnpairPartial.Bound exactSites 318 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row318_u0
  · exact row318_u1
  · exact row318_u2
  · exact row318_u3
  · exact row318_u4
  · exact row318_u5
  · exact row318_u6
  · exact row318_u7
  · exact row318_u8
  · exact row318_u9
  · exact row318_u10
private theorem row318_q0 : resolveAt exactSites 329 = some (AXPair.relocate 298 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q1 : resolveAt exactSites 330 = some (AXPair.relocate 298 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q2 : resolveAt exactSites 331 = some (AXPair.relocate 298 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q3 : resolveAt exactSites 332 = some (AXPair.relocate 298 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q4 : resolveAt exactSites 333 = some (AXPair.relocate 298 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q5 : resolveAt exactSites 334 = some (AXPair.relocate 298 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q6 : resolveAt exactSites 335 = some (AXPair.relocate 298 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q7 : resolveAt exactSites 336 = some (AXPair.relocate 298 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q8 : resolveAt exactSites 337 = some (AXPair.relocate 298 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_q9 : resolveAt exactSites 338 = some (AXPair.relocate 298 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound318_q : AXPair.Bound exactSites 298 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row318_q0
  · exact row318_q1
  · exact row318_q2
  · exact row318_q3
  · exact row318_q4
  · exact row318_q5
  · exact row318_q6
  · exact row318_q7
  · exact row318_q8
  · exact row318_q9
private theorem row318_m0 : resolveAt exactSites 339 = some (AXTimes4.expected 339 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_m1 : resolveAt exactSites 340 = some (AXTimes4.expected 339 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_m2 : resolveAt exactSites 341 = some (AXTimes4.expected 339 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_m3 : resolveAt exactSites 342 = some (AXTimes4.expected 339 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_m4 : resolveAt exactSites 343 = some (AXTimes4.expected 339 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row318_m5 : resolveAt exactSites 344 = some (AXTimes4.expected 339 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound318_m : AXTimes4.Bound exactSites 339 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row318_m0
  · exact row318_m1
  · exact row318_m2
  · exact row318_m3
  · exact row318_m4
  · exact row318_m5
theorem block318 : AXMacro.Realizes exactSites .cons 318 345 :=
  AXMacro.cons_realizes bound318_u bound318_q bound318_m
private theorem row345_p0 : resolveAt exactSites 345 = some (AXPushParam.relocate 320 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p1 : resolveAt exactSites 346 = some (AXPushParam.relocate 320 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p2 : resolveAt exactSites 347 = some (AXPushParam.relocate 320 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p3 : resolveAt exactSites 348 = some (AXPushParam.relocate 320 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p4 : resolveAt exactSites 349 = some (AXPushParam.relocate 320 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p5 : resolveAt exactSites 350 = some (AXPushParam.relocate 320 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p6 : resolveAt exactSites 351 = some (AXPushParam.relocate 320 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p7 : resolveAt exactSites 352 = some (AXPushParam.relocate 320 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p8 : resolveAt exactSites 353 = some (AXPushParam.relocate 320 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p9 : resolveAt exactSites 354 = some (AXPushParam.relocate 320 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p10 : resolveAt exactSites 355 = some (AXPushParam.relocate 320 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p11 : resolveAt exactSites 356 = some (AXPushParam.relocate 320 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p12 : resolveAt exactSites 357 = some (AXPushParam.relocate 320 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p13 : resolveAt exactSites 358 = some (AXPushParam.relocate 320 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p14 : resolveAt exactSites 359 = some (AXPushParam.relocate 320 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p15 : resolveAt exactSites 360 = some (AXPushParam.relocate 320 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p16 : resolveAt exactSites 361 = some (AXPushParam.relocate 320 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p17 : resolveAt exactSites 362 = some (AXPushParam.relocate 320 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row345_p18 : resolveAt exactSites 363 = some (AXPushParam.relocate 320 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound345_p : AXPushParam.Bound exactSites 320 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row345_p0
  · exact row345_p1
  · exact row345_p2
  · exact row345_p3
  · exact row345_p4
  · exact row345_p5
  · exact row345_p6
  · exact row345_p7
  · exact row345_p8
  · exact row345_p9
  · exact row345_p10
  · exact row345_p11
  · exact row345_p12
  · exact row345_p13
  · exact row345_p14
  · exact row345_p15
  · exact row345_p16
  · exact row345_p17
  · exact row345_p18
theorem block345 : AXMacro.Realizes exactSites .push 345 364 :=
  AXMacro.push_realizes bound345_p
private theorem row364_c0 : resolveAt exactSites 364 = some (CopyToT.expected 5 364 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row364_c1 : resolveAt exactSites 365 = some (CopyToT.expected 5 364 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row364_c2 : resolveAt exactSites 366 = some (CopyToT.expected 5 364 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row364_c3 : resolveAt exactSites 367 = some (CopyToT.expected 5 364 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row364_c4 : resolveAt exactSites 368 = some (CopyToT.expected 5 364 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row364_c5 : resolveAt exactSites 369 = some (CopyToT.expected 5 364 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row364_c6 : resolveAt exactSites 370 = some (CopyToT.expected 5 364 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound364_c : CopyToT.Bound exactSites 5 364 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row364_c0
  · exact row364_c1
  · exact row364_c2
  · exact row364_c3
  · exact row364_c4
  · exact row364_c5
  · exact row364_c6
theorem block364 : AXMacro.Realizes exactSites .copyH 364 371 :=
  AXMacro.copyH_realizes bound364_c
def code001 : List AXMacro.Op := [.cons,.readD,.push,.copyD,.cons,.push,.copyD,.push,.copyA,.cons,.push,.copyH]
theorem plan001 : AXMacro.Plan exactSites 172 371 code001 :=
  AXMacro.Plan.cons block172 ( AXMacro.Plan.cons block199 ( AXMacro.Plan.cons block213 ( AXMacro.Plan.cons block232 ( AXMacro.Plan.cons block239 ( AXMacro.Plan.cons block266 ( AXMacro.Plan.cons block285 ( AXMacro.Plan.cons block292 ( AXMacro.Plan.cons block311 ( AXMacro.Plan.cons block318 ( AXMacro.Plan.cons block345 ( AXMacro.Plan.cons block364 ( AXMacro.Plan.nil 371))))))))))))
#print axioms plan001
end M6.Source.AXAll

