import DiophantineConsistency.DecimalMachine215

/-!
# Authenticated decimal-machine data for the printed Wang table

The literal action, target and rail caches below are checked in Lean's kernel.
The action equalities cover all 430 decoded inputs. Rail equalities retain the
printed target-set cardinality, including the empty interval at q = 0.
-/

namespace DiophantineConsistency.WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

abbrev Action := Bool × Bool × ℕ

/-- A finite evaluation cache, authenticated below against all 430 actions. -/
def actionCache : Array Action := #[
  (true, true, 1), (true, true, 0), (false, true, 2), (false, true, 0), (true, true, 3), (true, false, 4),
  (true, false, 5), (true, false, 6), (false, false, 5), (true, false, 4), (false, false, 7), (true, false, 4),
  (false, false, 8), (false, false, 9), (true, true, 10), (false, false, 7), (false, false, 7), (false, false, 8),
  (true, false, 6), (true, false, 9), (false, true, 10), (false, true, 11), (false, false, 12), (false, true, 11),
  (true, false, 13), (false, false, 13), (false, false, 13), (true, false, 14), (false, false, 15), (true, false, 14),
  (false, false, 16), (true, false, 14), (false, false, 17), (true, false, 14), (false, false, 18), (true, false, 14),
  (false, false, 19), (true, false, 14), (false, false, 20), (true, false, 14), (false, false, 21), (true, false, 14),
  (false, false, 22), (true, false, 14), (false, true, 22), (true, true, 23), (false, true, 24), (true, true, 25),
  (false, true, 26), (true, true, 27), (false, true, 28), (true, true, 29), (false, true, 30), (false, false, 5),
  (false, true, 31), (true, true, 32), (false, true, 33), (true, true, 34), (false, true, 35), (true, true, 36),
  (false, false, 37), (false, true, 38), (false, true, 39), (true, true, 40), (false, true, 39), (true, true, 41),
  (false, true, 42), (true, true, 43), (false, true, 44), (true, true, 45), (false, true, 46), (true, true, 47),
  (false, true, 41), (true, true, 48), (false, false, 29), (true, true, 49), (false, true, 50), (true, true, 38),
  (false, false, 37), (false, true, 51), (false, true, 30), (true, false, 52), (false, false, 53), (true, false, 54),
  (false, true, 30), (true, true, 55), (false, true, 56), (true, true, 40), (false, true, 57), (false, true, 58),
  (false, true, 59), (false, false, 12), (false, true, 57), (false, true, 60), (false, true, 61), (false, false, 8),
  (false, true, 62), (true, true, 63), (false, true, 64), (true, true, 65), (false, true, 12), (true, true, 50),
  (false, true, 66), (true, true, 51), (false, true, 67), (true, false, 68), (false, true, 69), (true, true, 70),
  (false, true, 44), (true, true, 71), (false, true, 69), (true, true, 72), (false, false, 73), (true, false, 55),
  (false, false, 74), (false, true, 0), (false, true, 75), (true, true, 58), (false, true, 76), (false, true, 60),
  (false, true, 77), (true, true, 60), (false, true, 78), (true, true, 79), (false, true, 80), (true, true, 215),
  (false, false, 81), (true, true, 54), (false, false, 82), (true, false, 83), (false, true, 84), (true, true, 85),
  (false, true, 60), (true, true, 66), (false, true, 57), (false, true, 77), (false, true, 86), (true, true, 54),
  (false, true, 76), (false, true, 66), (false, false, 28), (true, true, 87), (false, true, 88), (false, false, 12),
  (false, true, 89), (false, false, 90), (false, true, 91), (true, true, 90), (true, true, 74), (true, false, 13),
  (false, true, 51), (true, true, 75), (false, false, 74), (false, true, 92), (false, true, 93), (true, true, 77),
  (false, true, 46), (true, true, 94), (false, true, 95), (true, true, 68), (false, true, 96), (true, true, 97),
  (false, true, 98), (true, true, 99), (false, false, 100), (true, false, 101), (false, true, 102), (true, true, 103),
  (false, true, 104), (true, true, 105), (false, true, 106), (true, true, 107), (false, true, 108), (true, true, 109),
  (false, true, 110), (false, false, 12), (false, false, 42), (true, false, 86), (false, true, 111), (true, true, 112),
  (false, true, 41), (false, false, 12), (false, true, 57), (false, true, 93), (false, true, 113), (true, true, 92),
  (false, true, 38), (true, true, 93), (false, true, 114), (false, false, 8), (false, true, 73), (true, true, 115),
  (false, true, 116), (true, true, 44), (false, true, 117), (true, true, 118), (false, true, 33), (true, true, 119),
  (false, true, 120), (true, true, 121), (false, true, 104), (true, true, 122), (false, true, 123), (true, true, 124),
  (false, true, 125), (true, true, 126), (false, true, 127), (true, true, 128), (false, true, 95), (true, true, 129),
  (false, true, 95), (true, true, 130), (false, true, 131), (true, true, 132), (false, true, 133), (false, false, 8),
  (false, true, 57), (false, true, 75), (false, true, 110), (true, true, 56), (false, true, 76), (false, true, 93),
  (false, true, 44), (false, false, 11), (false, true, 56), (true, true, 90), (true, true, 0), (true, true, 92),
  (false, true, 37), (true, true, 134), (false, true, 135), (true, true, 136), (false, true, 108), (true, true, 118),
  (false, false, 137), (false, false, 13), (false, true, 111), (false, false, 8), (false, true, 138), (true, true, 105),
  (false, true, 139), (true, true, 140), (false, true, 141), (true, true, 142), (false, true, 143), (true, true, 127),
  (false, true, 110), (true, true, 110), (false, true, 144), (true, true, 145), (false, true, 105), (true, true, 104),
  (false, true, 99), (true, true, 123), (false, true, 126), (true, true, 99), (false, true, 64), (true, true, 110),
  (false, true, 146), (true, true, 34), (false, true, 52), (true, true, 138), (false, true, 63), (true, true, 147),
  (false, true, 148), (true, true, 149), (false, true, 80), (true, true, 117), (false, true, 150), (true, true, 151),
  (false, true, 152), (true, true, 87), (false, true, 141), (true, true, 140), (false, true, 86), (true, true, 153),
  (false, true, 44), (true, true, 154), (false, true, 152), (true, false, 70), (false, true, 56), (true, true, 139),
  (false, true, 153), (true, true, 155), (false, true, 56), (true, true, 156), (false, true, 157), (true, true, 158),
  (false, true, 159), (true, true, 160), (false, false, 161), (true, true, 162), (false, true, 46), (true, false, 137),
  (false, true, 99), (true, true, 163), (false, true, 145), (true, true, 164), (false, true, 112), (true, true, 52),
  (false, true, 81), (true, true, 73), (false, false, 164), (true, true, 105), (false, false, 37), (false, true, 50),
  (false, true, 91), (true, true, 88), (false, true, 155), (false, false, 12), (false, false, 53), (true, true, 165),
  (false, true, 166), (false, false, 12), (false, true, 105), (true, true, 79), (false, true, 99), (true, false, 103),
  (false, true, 79), (true, true, 83), (false, true, 167), (true, true, 168), (false, true, 126), (true, true, 169),
  (false, true, 79), (true, true, 104), (false, true, 81), (true, true, 125), (false, true, 170), (true, true, 133),
  (false, true, 53), (true, false, 40), (false, true, 123), (true, true, 123), (false, true, 84), (true, true, 158),
  (false, true, 171), (true, true, 158), (false, true, 151), (true, true, 172), (false, true, 158), (true, true, 173),
  (false, true, 104), (true, true, 79), (false, true, 102), (true, true, 174), (false, true, 175), (true, true, 176),
  (false, true, 177), (true, true, 104), (false, true, 99), (true, true, 178), (false, true, 179), (true, true, 180),
  (false, true, 82), (true, true, 181), (false, true, 167), (true, true, 182), (false, true, 183), (true, true, 181),
  (false, true, 184), (true, true, 185), (false, false, 186), (true, true, 187), (false, true, 123), (true, true, 168),
  (false, true, 188), (true, true, 189), (false, false, 190), (true, false, 83), (false, true, 181), (true, true, 146),
  (false, true, 184), (true, true, 191), (false, true, 82), (true, true, 99), (false, true, 192), (true, true, 161),
  (false, true, 190), (true, true, 193), (false, true, 175), (true, true, 82), (false, true, 184), (true, true, 194),
  (false, true, 123), (true, true, 184), (false, true, 127), (true, true, 195), (false, true, 196), (true, true, 197),
  (false, true, 198), (true, true, 186), (false, true, 187), (true, true, 181), (false, true, 199), (true, true, 196),
  (false, true, 200), (true, true, 201), (false, true, 184), (true, true, 202), (false, true, 203), (true, true, 177),
  (false, true, 143), (true, true, 204), (false, true, 205), (true, true, 205), (false, true, 101), (true, true, 206),
  (false, true, 207), (true, true, 208), (false, true, 162), (true, false, 209), (false, true, 184), (true, true, 210),
  (false, true, 100), (true, true, 211), (false, true, 212), (true, true, 197), (false, true, 145), (true, true, 167),
  (false, true, 64), (true, true, 213), (false, true, 171), (true, true, 205), (false, true, 125), (true, true, 214),
  (false, true, 102), (true, true, 64), (false, true, 125), (true, true, 160)
 ]

def actionNat (j : ℕ) : Action := actionCache[j]?.getD (false,false,215)

def action (j : Fin 430) : Action := actionNat j.val

private theorem fromChunk (P : ℕ → Prop) {n a count : ℕ}
    (h : ∀ j : Fin count, P (a + j.val)) (ha : a ≤ n) (hb : n < a + count) : P n := by
  simpa only [Nat.add_sub_of_le ha] using h ⟨n-a, by omega⟩


private theorem action_chunk_0 : ∀ j : Fin 16,
    actionNat (0 + j.val) = DecimalMachine215.action (0 + j.val) := by
  decide +kernel

private theorem action_chunk_16 : ∀ j : Fin 16,
    actionNat (16 + j.val) = DecimalMachine215.action (16 + j.val) := by
  decide +kernel

private theorem action_chunk_32 : ∀ j : Fin 16,
    actionNat (32 + j.val) = DecimalMachine215.action (32 + j.val) := by
  decide +kernel

private theorem action_chunk_48 : ∀ j : Fin 16,
    actionNat (48 + j.val) = DecimalMachine215.action (48 + j.val) := by
  decide +kernel

private theorem action_chunk_64 : ∀ j : Fin 16,
    actionNat (64 + j.val) = DecimalMachine215.action (64 + j.val) := by
  decide +kernel

private theorem action_chunk_80 : ∀ j : Fin 16,
    actionNat (80 + j.val) = DecimalMachine215.action (80 + j.val) := by
  decide +kernel

private theorem action_chunk_96 : ∀ j : Fin 16,
    actionNat (96 + j.val) = DecimalMachine215.action (96 + j.val) := by
  decide +kernel

private theorem action_chunk_112 : ∀ j : Fin 16,
    actionNat (112 + j.val) = DecimalMachine215.action (112 + j.val) := by
  decide +kernel

private theorem action_chunk_128 : ∀ j : Fin 16,
    actionNat (128 + j.val) = DecimalMachine215.action (128 + j.val) := by
  decide +kernel

private theorem action_chunk_144 : ∀ j : Fin 16,
    actionNat (144 + j.val) = DecimalMachine215.action (144 + j.val) := by
  decide +kernel

private theorem action_chunk_160 : ∀ j : Fin 16,
    actionNat (160 + j.val) = DecimalMachine215.action (160 + j.val) := by
  decide +kernel

private theorem action_chunk_176 : ∀ j : Fin 16,
    actionNat (176 + j.val) = DecimalMachine215.action (176 + j.val) := by
  decide +kernel

private theorem action_chunk_192 : ∀ j : Fin 16,
    actionNat (192 + j.val) = DecimalMachine215.action (192 + j.val) := by
  decide +kernel

private theorem action_chunk_208 : ∀ j : Fin 16,
    actionNat (208 + j.val) = DecimalMachine215.action (208 + j.val) := by
  decide +kernel

private theorem action_chunk_224 : ∀ j : Fin 16,
    actionNat (224 + j.val) = DecimalMachine215.action (224 + j.val) := by
  decide +kernel

private theorem action_chunk_240 : ∀ j : Fin 16,
    actionNat (240 + j.val) = DecimalMachine215.action (240 + j.val) := by
  decide +kernel

private theorem action_chunk_256 : ∀ j : Fin 16,
    actionNat (256 + j.val) = DecimalMachine215.action (256 + j.val) := by
  decide +kernel

private theorem action_chunk_272 : ∀ j : Fin 16,
    actionNat (272 + j.val) = DecimalMachine215.action (272 + j.val) := by
  decide +kernel

private theorem action_chunk_288 : ∀ j : Fin 16,
    actionNat (288 + j.val) = DecimalMachine215.action (288 + j.val) := by
  decide +kernel

private theorem action_chunk_304 : ∀ j : Fin 16,
    actionNat (304 + j.val) = DecimalMachine215.action (304 + j.val) := by
  decide +kernel

private theorem action_chunk_320 : ∀ j : Fin 16,
    actionNat (320 + j.val) = DecimalMachine215.action (320 + j.val) := by
  decide +kernel

private theorem action_chunk_336 : ∀ j : Fin 16,
    actionNat (336 + j.val) = DecimalMachine215.action (336 + j.val) := by
  decide +kernel

private theorem action_chunk_352 : ∀ j : Fin 16,
    actionNat (352 + j.val) = DecimalMachine215.action (352 + j.val) := by
  decide +kernel

private theorem action_chunk_368 : ∀ j : Fin 16,
    actionNat (368 + j.val) = DecimalMachine215.action (368 + j.val) := by
  decide +kernel

private theorem action_chunk_384 : ∀ j : Fin 16,
    actionNat (384 + j.val) = DecimalMachine215.action (384 + j.val) := by
  decide +kernel

private theorem action_chunk_400 : ∀ j : Fin 16,
    actionNat (400 + j.val) = DecimalMachine215.action (400 + j.val) := by
  decide +kernel

private theorem action_chunk_416 : ∀ j : Fin 14,
    actionNat (416 + j.val) = DecimalMachine215.action (416 + j.val) := by
  decide +kernel

/-- All 430 cache entries agree with the exact decimal decoder; batches only
limit the kernel's temporary normalization memory. -/
theorem action_eq_decoder : ∀ j : Fin 430, action j = DecimalMachine215.action j.val := by
  intro j
  let P := fun index => actionNat index = DecimalMachine215.action index
  change P j.val
  by_cases h0 : j.val < 16
  · exact fromChunk P (n := j.val) (a := 0) action_chunk_0 (by omega) (by omega)
  by_cases h16 : j.val < 32
  · exact fromChunk P (n := j.val) (a := 16) action_chunk_16 (by omega) (by omega)
  by_cases h32 : j.val < 48
  · exact fromChunk P (n := j.val) (a := 32) action_chunk_32 (by omega) (by omega)
  by_cases h48 : j.val < 64
  · exact fromChunk P (n := j.val) (a := 48) action_chunk_48 (by omega) (by omega)
  by_cases h64 : j.val < 80
  · exact fromChunk P (n := j.val) (a := 64) action_chunk_64 (by omega) (by omega)
  by_cases h80 : j.val < 96
  · exact fromChunk P (n := j.val) (a := 80) action_chunk_80 (by omega) (by omega)
  by_cases h96 : j.val < 112
  · exact fromChunk P (n := j.val) (a := 96) action_chunk_96 (by omega) (by omega)
  by_cases h112 : j.val < 128
  · exact fromChunk P (n := j.val) (a := 112) action_chunk_112 (by omega) (by omega)
  by_cases h128 : j.val < 144
  · exact fromChunk P (n := j.val) (a := 128) action_chunk_128 (by omega) (by omega)
  by_cases h144 : j.val < 160
  · exact fromChunk P (n := j.val) (a := 144) action_chunk_144 (by omega) (by omega)
  by_cases h160 : j.val < 176
  · exact fromChunk P (n := j.val) (a := 160) action_chunk_160 (by omega) (by omega)
  by_cases h176 : j.val < 192
  · exact fromChunk P (n := j.val) (a := 176) action_chunk_176 (by omega) (by omega)
  by_cases h192 : j.val < 208
  · exact fromChunk P (n := j.val) (a := 192) action_chunk_192 (by omega) (by omega)
  by_cases h208 : j.val < 224
  · exact fromChunk P (n := j.val) (a := 208) action_chunk_208 (by omega) (by omega)
  by_cases h224 : j.val < 240
  · exact fromChunk P (n := j.val) (a := 224) action_chunk_224 (by omega) (by omega)
  by_cases h240 : j.val < 256
  · exact fromChunk P (n := j.val) (a := 240) action_chunk_240 (by omega) (by omega)
  by_cases h256 : j.val < 272
  · exact fromChunk P (n := j.val) (a := 256) action_chunk_256 (by omega) (by omega)
  by_cases h272 : j.val < 288
  · exact fromChunk P (n := j.val) (a := 272) action_chunk_272 (by omega) (by omega)
  by_cases h288 : j.val < 304
  · exact fromChunk P (n := j.val) (a := 288) action_chunk_288 (by omega) (by omega)
  by_cases h304 : j.val < 320
  · exact fromChunk P (n := j.val) (a := 304) action_chunk_304 (by omega) (by omega)
  by_cases h320 : j.val < 336
  · exact fromChunk P (n := j.val) (a := 320) action_chunk_320 (by omega) (by omega)
  by_cases h336 : j.val < 352
  · exact fromChunk P (n := j.val) (a := 336) action_chunk_336 (by omega) (by omega)
  by_cases h352 : j.val < 368
  · exact fromChunk P (n := j.val) (a := 352) action_chunk_352 (by omega) (by omega)
  by_cases h368 : j.val < 384
  · exact fromChunk P (n := j.val) (a := 368) action_chunk_368 (by omega) (by omega)
  by_cases h384 : j.val < 400
  · exact fromChunk P (n := j.val) (a := 384) action_chunk_384 (by omega) (by omega)
  by_cases h400 : j.val < 416
  · exact fromChunk P (n := j.val) (a := 400) action_chunk_400 (by omega) (by omega)
  exact fromChunk P (n := j.val) (a := 416) action_chunk_416 (by omega) (by omega)

def decodedActions : List Action := List.ofFn (fun j : Fin 430 => DecimalMachine215.action j.val)

def cachedActions : List Action := List.ofFn action

theorem cachedActions_eq_decoded : cachedActions = decodedActions := by
  apply congrArg List.ofFn
  funext j
  exact action_eq_decoder j

/-- The printed set S_d of distinct targets of transitions moving in direction d. -/
def targetsFrom (d : Bool) (as : List Action) : Finset ℕ :=
  ((as.filter (fun a => a.2.1 == d)).map (fun a => a.2.2)).toFinset

/-- Sorted finite caches of S_0 and S_1, checked against the decoded actions. -/
def targetList (d : Bool) : List ℕ :=
  if d then [0, 1, 2, 3, 10, 11, 12, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215] else [4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 28, 29, 37, 40, 42, 52, 53, 54, 55, 68, 70, 73, 74, 81, 82, 83, 86, 90, 100, 101, 103, 137, 161, 164, 186, 190, 209]

def targets (d : Bool) : Finset ℕ := (targetList d).toFinset

theorem targets_eq_cache : ∀ d, targets d = targetsFrom d cachedActions := by
  decide +kernel

theorem targets_eq_decoded (d : Bool) : targets d = targetsFrom d decodedActions := by
  rw [← cachedActions_eq_decoded]
  exact targets_eq_cache d

/-- Intersecting with range q makes the q=0 interval empty exactly as printed. -/
def railFormula (d : Bool) (q : ℕ) : ℕ :=
  205 - 199 * d.toNat + (targets d ∩ Finset.range q).card

/-- A finite computation cache; its equality to the printed cardinality is proved. -/
def railCache (d : Bool) : Array ℕ :=
  if d then #[6, 7, 8, 9, 10, 10, 10, 10, 10, 10, 10, 11, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 199, 200, 201, 202, 203, 204] else #[205, 205, 205, 205, 205, 206, 207, 208, 209, 210, 211, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 223, 223, 223, 223, 223, 224, 225, 225, 225, 225, 225, 225, 225, 225, 226, 226, 226, 227, 227, 228, 228, 228, 228, 228, 228, 228, 228, 228, 228, 229, 230, 231, 232, 232, 232, 232, 232, 232, 232, 232, 232, 232, 232, 232, 232, 233, 233, 234, 234, 234, 235, 236, 236, 236, 236, 236, 236, 236, 237, 238, 239, 239, 239, 240, 240, 240, 240, 241, 241, 241, 241, 241, 241, 241, 241, 241, 241, 242, 243, 243, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 245, 246, 246, 246, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 247, 248, 248, 248, 248, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 249, 250, 250, 250, 250, 250, 250]

theorem targetList_nodup : ∀ d, (targetList d).Nodup := by
  decide +kernel

/-- Compute the cardinality by a duplicate-free list, avoiding repeated
construction of intersections while preserving the printed set formula. -/
theorem railFormula_eq_filter (d : Bool) (q : ℕ) : railFormula d q =
    205 - 199 * d.toNat + ((targetList d).filter (fun a => a < q)).length := by
  have hset : targets d ∩ Finset.range q =
      ((targetList d).filter (fun a => a < q)).toFinset := by
    ext a
    simp [targets]
  rw [railFormula, hset, List.toFinset_card_of_nodup
    ((targetList_nodup d).filter _)]

private theorem rail_chunk_0 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[0 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 0 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_16 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[16 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 16 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_32 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[32 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 32 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_48 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[48 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 48 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_64 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[64 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 64 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_80 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[80 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 80 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_96 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[96 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 96 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_112 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[112 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 112 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_128 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[128 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 128 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_144 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[144 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 144 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_160 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[160 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 160 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_176 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[176 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 176 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_192 : ∀ (d : Bool) (q : Fin 16),
    (railCache d)[192 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 192 + q.val)).length := by
  decide +kernel

private theorem rail_chunk_208 : ∀ (d : Bool) (q : Fin 8),
    (railCache d)[208 + q.val]?.getD 0 = 205 - 199 * d.toNat +
      ((targetList d).filter (fun a => a < 208 + q.val)).length := by
  decide +kernel

theorem railCache_eq_formula (d : Bool) (q : Fin 216) :
    (railCache d)[q.val]?.getD 0 = railFormula d q.val := by
  rw [railFormula_eq_filter]
  let P := fun index => (railCache d)[index]?.getD 0 =
    205 - 199 * d.toNat + ((targetList d).filter (fun a => a < index)).length
  change P q.val
  by_cases h0 : q.val < 16
  · exact fromChunk P (n := q.val) (a := 0) (rail_chunk_0 d) (by omega) (by omega)
  by_cases h16 : q.val < 32
  · exact fromChunk P (n := q.val) (a := 16) (rail_chunk_16 d) (by omega) (by omega)
  by_cases h32 : q.val < 48
  · exact fromChunk P (n := q.val) (a := 32) (rail_chunk_32 d) (by omega) (by omega)
  by_cases h48 : q.val < 64
  · exact fromChunk P (n := q.val) (a := 48) (rail_chunk_48 d) (by omega) (by omega)
  by_cases h64 : q.val < 80
  · exact fromChunk P (n := q.val) (a := 64) (rail_chunk_64 d) (by omega) (by omega)
  by_cases h80 : q.val < 96
  · exact fromChunk P (n := q.val) (a := 80) (rail_chunk_80 d) (by omega) (by omega)
  by_cases h96 : q.val < 112
  · exact fromChunk P (n := q.val) (a := 96) (rail_chunk_96 d) (by omega) (by omega)
  by_cases h112 : q.val < 128
  · exact fromChunk P (n := q.val) (a := 112) (rail_chunk_112 d) (by omega) (by omega)
  by_cases h128 : q.val < 144
  · exact fromChunk P (n := q.val) (a := 128) (rail_chunk_128 d) (by omega) (by omega)
  by_cases h144 : q.val < 160
  · exact fromChunk P (n := q.val) (a := 144) (rail_chunk_144 d) (by omega) (by omega)
  by_cases h160 : q.val < 176
  · exact fromChunk P (n := q.val) (a := 160) (rail_chunk_160 d) (by omega) (by omega)
  by_cases h176 : q.val < 192
  · exact fromChunk P (n := q.val) (a := 176) (rail_chunk_176 d) (by omega) (by omega)
  by_cases h192 : q.val < 208
  · exact fromChunk P (n := q.val) (a := 192) (rail_chunk_192 d) (by omega) (by omega)
  exact fromChunk P (n := q.val) (a := 208) (rail_chunk_208 d) (by omega) (by omega)


def rail (d : Bool) (q : ℕ) : ℕ :=
  if _hq : q < 216 then (railCache d)[q]?.getD 0 else railFormula d q

theorem rail_eq_formula (d : Bool) (q : ℕ) : rail d q = railFormula d q := by
  by_cases hq : q < 216
  · simpa only [rail, dif_pos hq] using railCache_eq_formula d ⟨q,hq⟩
  · simp only [rail, dif_neg hq]

/-- The rail formula is bound directly to the actual decimal actions. -/
theorem rail_eq_decoded (d : Bool) (q : ℕ) : rail d q =
    205 - 199 * d.toNat + (targetsFrom d decodedActions ∩ Finset.range q).card := by
  rw [rail_eq_formula, railFormula, targets_eq_decoded]

end DiophantineConsistency.WangTiles942
