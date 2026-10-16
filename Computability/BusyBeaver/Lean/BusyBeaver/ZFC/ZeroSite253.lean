import BusyBeaver.ZFC.WritingRuns
import BusyBeaver.ZFC.RegisterMark253
import BusyBeaver.ZFC.BreakSite253

/-!
The zero branch of literal program-counter site000 in the actual public253 machine.
Attributed source: Mira-Cult machine, Wade framework, Jeff verification, and
mira-emmy PR20 head0d544f2a2e3c18f12278441a74b7879f31cbe856.
Literal control transitions compose with the independently proved register boxes.
Intermediate dispatcher visits are permitted; the conclusion is the full frame.
The Core wrapper preserves all nine primary registers and arbitrary spares.
Composition with the existing bootstrap proves the paired binary313429/RM331
endpoint without recomputing the bootstrap or asserting first arrival.
No general reachable-PC, runtime, enumerator or consistency theorem is claimed.
-/

namespace SetTheory.BusyBeaver.ZFC.ZeroSite253

open FiniteZipper ZipperRuns WritingRuns RegisterBoxes253

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem replicate_snoc (bit : Bool) (k : Nat) (tail : List Bool) :
    List.replicate k bit ++ bit :: tail = bit :: (List.replicate k bit ++ tail) := by
  calc
    _ = (List.replicate k bit ++ [bit]) ++ tail := (List.append_assoc _ _ _).symm
    _ = _ := by rw [← List.replicate_succ', List.replicate_succ]; rfl

private abbrev pre (a b c d e : Nat) : List Nat := [a, b, c, d, e]

/-- Exact literal control and two arbitrary-length register excursions. -/
theorem zero000_zip (n a b c d e : Nat) (rest : List Nat) (h : Int) (L : List Bool) :
    zipRun machine253
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (false :: false :: false :: (List.replicate (n + 37) false ++ true ::
          (registerBits (pre a b c d e ++ 0 :: rest) ++ [false]))))
      (8 * n + 4 * width (pre a b c d e) + 406) =
      zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (false :: true :: (List.replicate (n + 38) false ++ true ::
          (registerBits (pre a b c d e ++ 0 :: rest) ++ [false]))) := by
  let pre : List Nat := [a, b, c, d, e]
  change zipRun machine253 _ (8 * n + 4 * width pre + 406) = _
  -- 0: old96 c, stepR.
  change zipRun machine253 (zAt (33 : Fin 253) h
      (true :: (List.replicate 10 false ++ L))
      (false :: (false :: (false :: (List.replicate (n + 37) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (8 * n + 4 * width pre + 406) = _
  rw [show 8 * n + 4 * width pre + 406 = (8 * n + 4 * width pre + 405) + 1 by omega, zipRun_first,
    step_right machine253 (33 : Fin 253) 34 false false _ _ _ (by decide)]
  -- 1: old110 c, stepR.
  change zipRun machine253 (zAt (34 : Fin 253) (h + 1)
      (false :: (true :: (List.replicate 10 false ++ L)))
      (false :: (false :: (List.replicate (n + 37) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (8 * n + 4 * width pre + 405) = _
  rw [show 8 * n + 4 * width pre + 405 = (8 * n + 4 * width pre + 404) + 1 by omega, zipRun_first,
    step_right machine253 (34 : Fin 253) 36 false false _ _ _ (by decide)]
  rw [show ((h + 1) + 1) = (h + 2) by omega]
  -- 2: old33 c, stepR.
  change zipRun machine253 (zAt (36 : Fin 253) (h + 2)
      (false :: (false :: (true :: (List.replicate 10 false ++ L))))
      (false :: (List.replicate (n + 37) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))) (8 * n + 4 * width pre + 404) = _
  rw [show 8 * n + 4 * width pre + 404 = (8 * n + 4 * width pre + 403) + 1 by omega, zipRun_first,
    step_right machine253 (36 : Fin 253) 40 false false _ _ _ (by decide)]
  rw [show ((h + 2) + 1) = (h + 3) by omega]
  -- 4: old47 c, stepL.
  change zipRun machine253 (zAt (40 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L)))))
      (false :: (List.replicate (n + 36) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))) (8 * n + 4 * width pre + 403) = _
  rw [show 8 * n + 4 * width pre + 403 = (8 * n + 4 * width pre + 402) + 1 by omega, zipRun_first,
    step_left machine253 (40 : Fin 253) 47 false false _ _ _ (by decide)]
  -- 5: old27 l, norm.
  change zipRun machine253 (zAt (47 : Fin 253) ((h + 3) - 1)
      (false :: (false :: (true :: (List.replicate 10 false ++ L))))
      (false :: (false :: (List.replicate (n + 36) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (8 * n + 4 * width pre + 402) = _
  rw [show ((h + 3) - 1) = (h + 2) by omega]
  -- 6: old27 c, stepL.
  change zipRun machine253 (zAt (47 : Fin 253) (h + 2)
      (false :: (false :: (true :: (List.replicate 10 false ++ L))))
      (false :: (false :: (List.replicate (n + 36) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (8 * n + 4 * width pre + 402) = _
  rw [show 8 * n + 4 * width pre + 402 = (8 * n + 4 * width pre + 401) + 1 by omega, zipRun_first,
    step_left machine253 (47 : Fin 253) 58 false false _ _ _ (by decide)]
  -- 7: old32 l, norm.
  change zipRun machine253 (zAt (58 : Fin 253) ((h + 2) - 1)
      (false :: (true :: (List.replicate 10 false ++ L)))
      (false :: (false :: (false :: (List.replicate (n + 36) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (8 * n + 4 * width pre + 401) = _
  rw [show ((h + 2) - 1) = (h + 1) by omega]
  -- 8: old32 c, stepR.
  change zipRun machine253 (zAt (58 : Fin 253) (h + 1)
      (false :: (true :: (List.replicate 10 false ++ L)))
      (false :: (false :: (false :: (List.replicate (n + 36) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (8 * n + 4 * width pre + 401) = _
  rw [show 8 * n + 4 * width pre + 401 = (8 * n + 4 * width pre + 400) + 1 by omega, zipRun_first,
    step_right machine253 (58 : Fin 253) 71 false false _ _ _ (by decide)]
  rw [show ((h + 1) + 1) = (h + 2) by omega]
  -- 9: old45 c, stepR.
  change zipRun machine253 (zAt (71 : Fin 253) (h + 2)
      (false :: (false :: (true :: (List.replicate 10 false ++ L))))
      (false :: (false :: (List.replicate (n + 36) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (8 * n + 4 * width pre + 400) = _
  rw [show 8 * n + 4 * width pre + 400 = (8 * n + 4 * width pre + 399) + 1 by omega, zipRun_first,
    step_right machine253 (71 : Fin 253) 67 false false _ _ _ (by decide)]
  rw [show ((h + 2) + 1) = (h + 3) by omega]
  -- 10: old21 c, stepR.
  change zipRun machine253 (zAt (67 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L)))))
      (false :: (List.replicate (n + 36) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))) (8 * n + 4 * width pre + 399) = _
  rw [show 8 * n + 4 * width pre + 399 = (8 * n + 4 * width pre + 398) + 1 by omega, zipRun_first,
    step_right machine253 (67 : Fin 253) 64 false false _ _ _ (by decide)]
  rw [show ((h + 3) + 1) = (h + 4) by omega]
  -- 12: old30 c, stepL.
  change zipRun machine253 (zAt (64 : Fin 253) (h + 4)
      (false :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))
      (false :: (List.replicate (n + 35) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))) (8 * n + 4 * width pre + 398) = _
  rw [show 8 * n + 4 * width pre + 398 = (8 * n + 4 * width pre + 397) + 1 by omega, zipRun_first,
    step_left machine253 (64 : Fin 253) 78 false false _ _ _ (by decide)]
  -- 13: old42 l, norm.
  change zipRun machine253 (zAt (78 : Fin 253) ((h + 4) - 1)
      (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L)))))
      (false :: (false :: (List.replicate (n + 35) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (8 * n + 4 * width pre + 397) = _
  rw [show ((h + 4) - 1) = (h + 3) by omega]
  -- 14: old42 c, stepR.
  change zipRun machine253 (zAt (78 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L)))))
      (false :: (false :: (List.replicate (n + 35) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (8 * n + 4 * width pre + 397) = _
  rw [show 8 * n + 4 * width pre + 397 = (8 * n + 4 * width pre + 396) + 1 by omega, zipRun_first,
    step_right machine253 (78 : Fin 253) 78 false true _ _ _ (by decide)]
  rw [show ((h + 3) + 1) = (h + 4) by omega]
  -- 15: old42 c, stepR.
  change zipRun machine253 (zAt (78 : Fin 253) (h + 4)
      (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))
      (false :: (List.replicate (n + 35) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))) (8 * n + 4 * width pre + 396) = _
  rw [show 8 * n + 4 * width pre + 396 = (8 * n + 4 * width pre + 395) + 1 by omega, zipRun_first,
    step_right machine253 (78 : Fin 253) 78 false true _ _ _ (by decide)]
  rw [show ((h + 4) + 1) = (h + 5) by omega]
  -- 16: old42 c, scanR.
  change zipRun machine253 (zAt (78 : Fin 253) (h + 5)
      (true :: (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L)))))))
      (List.replicate (n + 35) false ++ (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (8 * n + 4 * width pre + 395) = _
  rw [show 8 * n + 4 * width pre + 395 = (n + 35) + (7 * n + 4 * width pre + 360) by omega, zipRun_add,
    scan_right_write machine253 (78 : Fin 253) false true (by decide)]
  rw [show ((h + 5) + (((n + 35) : Nat) : Int)) = (h + (n : Int) + 40) by omega]
  -- 17: old42 c, stepL.
  change zipRun machine253 (zAt (78 : Fin 253) (h + (n : Int) + 40)
      (List.replicate (n + 35) true ++ (true :: (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))))
      (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))) (7 * n + 4 * width pre + 360) = _
  rw [show 7 * n + 4 * width pre + 360 = (7 * n + 4 * width pre + 359) + 1 by omega, zipRun_first,
    step_left machine253 (78 : Fin 253) 20 true true _ _ _ (by decide)]
  -- 18: old2 l, norm.
  change zipRun machine253 (zAt (20 : Fin 253) ((h + (n : Int) + 40) - 1)
      (List.replicate (n + 34) true ++ (true :: (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (7 * n + 4 * width pre + 359) = _
  rw [show ((h + (n : Int) + 40) - 1) = (h + (n : Int) + 39) by omega]
  -- 19: old2 c, stepL.
  change zipRun machine253 (zAt (20 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (true :: (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (7 * n + 4 * width pre + 359) = _
  rw [show 7 * n + 4 * width pre + 359 = (7 * n + 4 * width pre + 358) + 1 by omega, zipRun_first,
    step_left machine253 (20 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 20: old4 l, scanL.
  change zipRun machine253 (leftAt (22 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (true :: (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (7 * n + 4 * width pre + 358) = _
  rw [show 7 * n + 4 * width pre + 358 = (n + 34) + (6 * n + 4 * width pre + 324) by omega, zipRun_add,
    scan_left_write machine253 (22 : Fin 253) true true (by decide)]
  rw [show ((h + (n : Int) + 39) - (((n + 34) : Nat) : Int)) = (h + 5) by omega]
  -- 21: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h + 5) - 1)
      (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))
      (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (6 * n + 4 * width pre + 324) = _
  rw [show ((h + 5) - 1) = (h + 4) by omega]
  -- 22: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h + 4)
      (true :: (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L))))))
      (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (6 * n + 4 * width pre + 324) = _
  rw [show 6 * n + 4 * width pre + 324 = (6 * n + 4 * width pre + 323) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 23: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h + 4) - 1)
      (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L)))))
      (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (6 * n + 4 * width pre + 323) = _
  rw [show ((h + 4) - 1) = (h + 3) by omega]
  -- 24: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (List.replicate 10 false ++ L)))))
      (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (6 * n + 4 * width pre + 323) = _
  rw [show 6 * n + 4 * width pre + 323 = (6 * n + 4 * width pre + 322) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 25: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h + 3) - 1)
      (false :: (false :: (true :: (List.replicate 10 false ++ L))))
      (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (6 * n + 4 * width pre + 322) = _
  rw [show ((h + 3) - 1) = (h + 2) by omega]
  -- 26: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h + 2)
      (false :: (false :: (true :: (List.replicate 10 false ++ L))))
      (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (6 * n + 4 * width pre + 322) = _
  rw [show 6 * n + 4 * width pre + 322 = (6 * n + 4 * width pre + 321) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 24 false false _ _ _ (by decide)]
  -- 27: old6 l, norm.
  change zipRun machine253 (zAt (24 : Fin 253) ((h + 2) - 1)
      (false :: (true :: (List.replicate 10 false ++ L)))
      (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))) (6 * n + 4 * width pre + 321) = _
  rw [show ((h + 2) - 1) = (h + 1) by omega]
  -- 28: old6 c, stepL.
  change zipRun machine253 (zAt (24 : Fin 253) (h + 1)
      (false :: (true :: (List.replicate 10 false ++ L)))
      (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))) (6 * n + 4 * width pre + 321) = _
  rw [show 6 * n + 4 * width pre + 321 = (6 * n + 4 * width pre + 320) + 1 by omega, zipRun_first,
    step_left machine253 (24 : Fin 253) 25 false false _ _ _ (by decide)]
  -- 29: old9 l, norm.
  change zipRun machine253 (zAt (25 : Fin 253) ((h + 1) - 1)
      (true :: (List.replicate 10 false ++ L))
      (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))) (6 * n + 4 * width pre + 320) = _
  rw [show ((h + 1) - 1) = h by omega]
  -- 30: old9 c, stepL.
  change zipRun machine253 (zAt (25 : Fin 253) h
      (true :: (List.replicate 10 false ++ L))
      (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))) (6 * n + 4 * width pre + 320) = _
  rw [show 6 * n + 4 * width pre + 320 = (6 * n + 4 * width pre + 319) + 1 by omega, zipRun_first,
    step_left machine253 (25 : Fin 253) 26 false false _ _ _ (by decide)]
  -- 31: old13 l, norm.
  change zipRun machine253 (zAt (26 : Fin 253) (h - 1)
      (List.replicate 10 false ++ L)
      (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))) (6 * n + 4 * width pre + 319) = _
  -- 32: old13 c, stepL.
  change zipRun machine253 (zAt (26 : Fin 253) (h - 1)
      (List.replicate 10 false ++ L)
      (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))) (6 * n + 4 * width pre + 319) = _
  rw [show 6 * n + 4 * width pre + 319 = (6 * n + 4 * width pre + 318) + 1 by omega, zipRun_first,
    step_left machine253 (26 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 33: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h - 1) - 1)
      (List.replicate 9 false ++ L)
      (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))) (6 * n + 4 * width pre + 318) = _
  rw [show ((h - 1) - 1) = (h - 2) by omega]
  -- 34: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h - 2)
      (List.replicate 9 false ++ L)
      (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))) (6 * n + 4 * width pre + 318) = _
  rw [show 6 * n + 4 * width pre + 318 = (6 * n + 4 * width pre + 317) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 24 false false _ _ _ (by decide)]
  -- 35: old6 l, norm.
  change zipRun machine253 (zAt (24 : Fin 253) ((h - 2) - 1)
      (List.replicate 8 false ++ L)
      (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))) (6 * n + 4 * width pre + 317) = _
  rw [show ((h - 2) - 1) = (h - 3) by omega]
  -- 36: old6 c, stepL.
  change zipRun machine253 (zAt (24 : Fin 253) (h - 3)
      (List.replicate 8 false ++ L)
      (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))) (6 * n + 4 * width pre + 317) = _
  rw [show 6 * n + 4 * width pre + 317 = (6 * n + 4 * width pre + 316) + 1 by omega, zipRun_first,
    step_left machine253 (24 : Fin 253) 25 false false _ _ _ (by decide)]
  -- 37: old9 l, norm.
  change zipRun machine253 (zAt (25 : Fin 253) ((h - 3) - 1)
      (List.replicate 7 false ++ L)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))) (6 * n + 4 * width pre + 316) = _
  rw [show ((h - 3) - 1) = (h - 4) by omega]
  -- 38: old9 c, stepL.
  change zipRun machine253 (zAt (25 : Fin 253) (h - 4)
      (List.replicate 7 false ++ L)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))) (6 * n + 4 * width pre + 316) = _
  rw [show 6 * n + 4 * width pre + 316 = (6 * n + 4 * width pre + 315) + 1 by omega, zipRun_first,
    step_left machine253 (25 : Fin 253) 26 false false _ _ _ (by decide)]
  -- 39: old13 l, norm.
  change zipRun machine253 (zAt (26 : Fin 253) ((h - 4) - 1)
      (List.replicate 6 false ++ L)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))) (6 * n + 4 * width pre + 315) = _
  rw [show ((h - 4) - 1) = (h - 5) by omega]
  -- 40: old13 c, stepL.
  change zipRun machine253 (zAt (26 : Fin 253) (h - 5)
      (List.replicate 6 false ++ L)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))) (6 * n + 4 * width pre + 315) = _
  rw [show 6 * n + 4 * width pre + 315 = (6 * n + 4 * width pre + 314) + 1 by omega, zipRun_first,
    step_left machine253 (26 : Fin 253) 27 false false _ _ _ (by decide)]
  -- 41: old19 l, norm.
  change zipRun machine253 (zAt (27 : Fin 253) ((h - 5) - 1)
      (List.replicate 5 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))) (6 * n + 4 * width pre + 314) = _
  rw [show ((h - 5) - 1) = (h - 6) by omega]
  -- 42: old19 c, stepL.
  change zipRun machine253 (zAt (27 : Fin 253) (h - 6)
      (List.replicate 5 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))) (6 * n + 4 * width pre + 314) = _
  rw [show 6 * n + 4 * width pre + 314 = (6 * n + 4 * width pre + 313) + 1 by omega, zipRun_first,
    step_left machine253 (27 : Fin 253) 28 false false _ _ _ (by decide)]
  -- 43: old29 l, norm.
  change zipRun machine253 (zAt (28 : Fin 253) ((h - 6) - 1)
      (List.replicate 4 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))) (6 * n + 4 * width pre + 313) = _
  rw [show ((h - 6) - 1) = (h - 7) by omega]
  -- 44: old29 c, stepL.
  change zipRun machine253 (zAt (28 : Fin 253) (h - 7)
      (List.replicate 4 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))) (6 * n + 4 * width pre + 313) = _
  rw [show 6 * n + 4 * width pre + 313 = (6 * n + 4 * width pre + 312) + 1 by omega, zipRun_first,
    step_left machine253 (28 : Fin 253) 29 false false _ _ _ (by decide)]
  -- 45: old41 l, norm.
  change zipRun machine253 (zAt (29 : Fin 253) ((h - 7) - 1)
      (List.replicate 3 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))) (6 * n + 4 * width pre + 312) = _
  rw [show ((h - 7) - 1) = (h - 8) by omega]
  -- 46: old41 c, stepL.
  change zipRun machine253 (zAt (29 : Fin 253) (h - 8)
      (List.replicate 3 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))) (6 * n + 4 * width pre + 312) = _
  rw [show 6 * n + 4 * width pre + 312 = (6 * n + 4 * width pre + 311) + 1 by omega, zipRun_first,
    step_left machine253 (29 : Fin 253) 30 false false _ _ _ (by decide)]
  -- 47: old58 l, norm.
  change zipRun machine253 (zAt (30 : Fin 253) ((h - 8) - 1)
      (List.replicate 2 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))) (6 * n + 4 * width pre + 311) = _
  rw [show ((h - 8) - 1) = (h - 9) by omega]
  -- 48: old58 c, stepL.
  change zipRun machine253 (zAt (30 : Fin 253) (h - 9)
      (List.replicate 2 false ++ L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))) (6 * n + 4 * width pre + 311) = _
  rw [show 6 * n + 4 * width pre + 311 = (6 * n + 4 * width pre + 310) + 1 by omega, zipRun_first,
    step_left machine253 (30 : Fin 253) 31 false false _ _ _ (by decide)]
  -- 49: old74 l, norm.
  change zipRun machine253 (zAt (31 : Fin 253) ((h - 9) - 1)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))) (6 * n + 4 * width pre + 310) = _
  rw [show ((h - 9) - 1) = (h - 10) by omega]
  -- 50: old74 c, stepL.
  change zipRun machine253 (zAt (31 : Fin 253) (h - 10)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))) (6 * n + 4 * width pre + 310) = _
  rw [show 6 * n + 4 * width pre + 310 = (6 * n + 4 * width pre + 309) + 1 by omega, zipRun_first,
    step_left machine253 (31 : Fin 253) 32 false false _ _ _ (by decide)]
  -- 51: old84 l, norm.
  change zipRun machine253 (zAt (32 : Fin 253) ((h - 10) - 1)
      L
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))))) (6 * n + 4 * width pre + 309) = _
  rw [show ((h - 10) - 1) = (h - 11) by omega]
  -- 52: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 11)
      L
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))))) (6 * n + 4 * width pre + 309) = _
  rw [show 6 * n + 4 * width pre + 309 = (6 * n + 4 * width pre + 308) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 11) + 1) = (h - 10) by omega]
  -- 53: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 10)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))) (6 * n + 4 * width pre + 308) = _
  rw [show 6 * n + 4 * width pre + 308 = (6 * n + 4 * width pre + 307) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 10) + 1) = (h - 9) by omega]
  -- 54: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 9)
      (false :: (false :: L))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))) (6 * n + 4 * width pre + 307) = _
  rw [show 6 * n + 4 * width pre + 307 = (6 * n + 4 * width pre + 306) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 9) + 1) = (h - 8) by omega]
  -- 55: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 8)
      (false :: (false :: (false :: L)))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))) (6 * n + 4 * width pre + 306) = _
  rw [show 6 * n + 4 * width pre + 306 = (6 * n + 4 * width pre + 305) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 8) + 1) = (h - 7) by omega]
  -- 56: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 7)
      (false :: (false :: (false :: (false :: L))))
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))) (6 * n + 4 * width pre + 305) = _
  rw [show 6 * n + 4 * width pre + 305 = (6 * n + 4 * width pre + 304) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 7) + 1) = (h - 6) by omega]
  -- 57: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 6)
      (false :: (false :: (false :: (false :: (false :: L)))))
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))) (6 * n + 4 * width pre + 304) = _
  rw [show 6 * n + 4 * width pre + 304 = (6 * n + 4 * width pre + 303) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 6) + 1) = (h - 5) by omega]
  -- 58: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 5)
      (false :: (false :: (false :: (false :: (false :: (false :: L))))))
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))) (6 * n + 4 * width pre + 303) = _
  rw [show 6 * n + 4 * width pre + 303 = (6 * n + 4 * width pre + 302) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 5) + 1) = (h - 4) by omega]
  -- 59: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 4)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))) (6 * n + 4 * width pre + 302) = _
  rw [show 6 * n + 4 * width pre + 302 = (6 * n + 4 * width pre + 301) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 4) + 1) = (h - 3) by omega]
  -- 60: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 3)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))
      (false :: (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))) (6 * n + 4 * width pre + 301) = _
  rw [show 6 * n + 4 * width pre + 301 = (6 * n + 4 * width pre + 300) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 3) + 1) = (h - 2) by omega]
  -- 61: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 2)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))
      (false :: (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))) (6 * n + 4 * width pre + 300) = _
  rw [show 6 * n + 4 * width pre + 300 = (6 * n + 4 * width pre + 299) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 2) + 1) = (h - 1) by omega]
  -- 62: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))
      (true :: (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))) (6 * n + 4 * width pre + 299) = _
  rw [show 6 * n + 4 * width pre + 299 = (6 * n + 4 * width pre + 298) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 33 true true _ _ _ (by decide)]
  rw [show ((h - 1) + 1) = h by omega]
  -- 63: old96 c, stepR.
  change zipRun machine253 (zAt (33 : Fin 253) h
      (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))
      (false :: (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))) (6 * n + 4 * width pre + 298) = _
  rw [show 6 * n + 4 * width pre + 298 = (6 * n + 4 * width pre + 297) + 1 by omega, zipRun_first,
    step_right machine253 (33 : Fin 253) 34 false false _ _ _ (by decide)]
  -- 64: old110 c, stepR.
  change zipRun machine253 (zAt (34 : Fin 253) (h + 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))) (6 * n + 4 * width pre + 297) = _
  rw [show 6 * n + 4 * width pre + 297 = (6 * n + 4 * width pre + 296) + 1 by omega, zipRun_first,
    step_right machine253 (34 : Fin 253) 36 false false _ _ _ (by decide)]
  rw [show ((h + 1) + 1) = (h + 2) by omega]
  -- 65: old33 c, stepR.
  change zipRun machine253 (zAt (36 : Fin 253) (h + 2)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (6 * n + 4 * width pre + 296) = _
  rw [show 6 * n + 4 * width pre + 296 = (6 * n + 4 * width pre + 295) + 1 by omega, zipRun_first,
    step_right machine253 (36 : Fin 253) 40 false false _ _ _ (by decide)]
  rw [show ((h + 2) + 1) = (h + 3) by omega]
  -- 66: old47 c, stepR.
  change zipRun machine253 (zAt (40 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (true :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (6 * n + 4 * width pre + 295) = _
  rw [show 6 * n + 4 * width pre + 295 = (6 * n + 4 * width pre + 294) + 1 by omega, zipRun_first,
    step_right machine253 (40 : Fin 253) 7 true false _ _ _ (by decide)]
  rw [show ((h + 3) + 1) = (h + 4) by omega]
  -- 67: old40 c, stepR.
  change zipRun machine253 (zAt (7 : Fin 253) (h + 4)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (6 * n + 4 * width pre + 294) = _
  rw [show 6 * n + 4 * width pre + 294 = (6 * n + 4 * width pre + 293) + 1 by omega, zipRun_first,
    step_right machine253 (7 : Fin 253) 7 true true _ _ _ (by decide)]
  rw [show ((h + 4) + 1) = (h + 5) by omega]
  -- 68: old40 c, scanR.
  change zipRun machine253 (zAt (7 : Fin 253) (h + 5)
      (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))
      (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))) (6 * n + 4 * width pre + 293) = _
  rw [show 6 * n + 4 * width pre + 293 = (n + 34) + (5 * n + 4 * width pre + 259) by omega, zipRun_add,
    scan_right_write machine253 (7 : Fin 253) true true (by decide)]
  rw [show ((h + 5) + (((n + 34) : Nat) : Int)) = (h + (n : Int) + 39) by omega]
  -- 69: old40 c, stepR.
  change zipRun machine253 (zAt (7 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (5 * n + 4 * width pre + 259) = _
  rw [show 5 * n + 4 * width pre + 259 = (5 * n + 4 * width pre + 258) + 1 by omega, zipRun_first,
    step_right machine253 (7 : Fin 253) 7 true true _ _ _ (by decide)]
  rw [show ((h + (n : Int) + 39) + 1) = (h + (n : Int) + 40) by omega]
  -- 70: old40 c, stepR.
  change zipRun machine253 (zAt (7 : Fin 253) (h + (n : Int) + 40)
      (true :: (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))) (5 * n + 4 * width pre + 258) = _
  rw [show 5 * n + 4 * width pre + 258 = (5 * n + 4 * width pre + 257) + 1 by omega, zipRun_first,
    step_right machine253 (7 : Fin 253) 7 true true _ _ _ (by decide)]
  rw [show ((h + (n : Int) + 40) + 1) = (h + (n : Int) + 41) by omega]
  -- 71: old40 c, mark.
  change zipRun machine253 (zAt (RegisterMark253.skip pre.length) (h + (n : Int) + 41)
      (true :: (true :: (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))))
      (registerBits (pre ++ 0 :: rest) ++ [false])) (5 * n + 4 * width pre + 257) = _
  rw [show 5 * n + 4 * width pre + 257 = (2 * width pre + 3) + (5 * n + 2 * width pre + 254) by omega, zipRun_add,
    RegisterMark253.mark_zip pre 0 rest (by simp [pre])]
  -- 72: old6 l, norm.
  change zipRun machine253 (zAt (24 : Fin 253) ((h + (n : Int) + 41) - 1)
      (true :: (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))) (5 * n + 2 * width pre + 254) = _
  rw [show ((h + (n : Int) + 41) - 1) = (h + (n : Int) + 40) by omega]
  -- 73: old6 c, stepL.
  change zipRun machine253 (zAt (24 : Fin 253) (h + (n : Int) + 40)
      (true :: (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))) (5 * n + 2 * width pre + 254) = _
  rw [show 5 * n + 2 * width pre + 254 = (5 * n + 2 * width pre + 253) + 1 by omega, zipRun_first,
    step_left machine253 (24 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 74: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h + (n : Int) + 40) - 1)
      (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))) (5 * n + 2 * width pre + 253) = _
  rw [show ((h + (n : Int) + 40) - 1) = (h + (n : Int) + 39) by omega]
  -- 75: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))) (5 * n + 2 * width pre + 253) = _
  rw [show 5 * n + 2 * width pre + 253 = (5 * n + 2 * width pre + 252) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 76: old4 l, scanL.
  change zipRun machine253 (leftAt (22 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (true :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))) (5 * n + 2 * width pre + 252) = _
  rw [show 5 * n + 2 * width pre + 252 = (n + 34) + (4 * n + 2 * width pre + 218) by omega, zipRun_add,
    scan_left_write machine253 (22 : Fin 253) true true (by decide)]
  rw [show ((h + (n : Int) + 39) - (((n + 34) : Nat) : Int)) = (h + 5) by omega]
  -- 77: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h + 5) - 1)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))) (4 * n + 2 * width pre + 218) = _
  rw [show ((h + 5) - 1) = (h + 4) by omega]
  -- 78: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h + 4)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))) (4 * n + 2 * width pre + 218) = _
  rw [show 4 * n + 2 * width pre + 218 = (4 * n + 2 * width pre + 217) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 79: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h + 4) - 1)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))) (4 * n + 2 * width pre + 217) = _
  rw [show ((h + 4) - 1) = (h + 3) by omega]
  -- 80: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))) (4 * n + 2 * width pre + 217) = _
  rw [show 4 * n + 2 * width pre + 217 = (4 * n + 2 * width pre + 216) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 24 false false _ _ _ (by decide)]
  -- 81: old6 l, norm.
  change zipRun machine253 (zAt (24 : Fin 253) ((h + 3) - 1)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))) (4 * n + 2 * width pre + 216) = _
  rw [show ((h + 3) - 1) = (h + 2) by omega]
  -- 82: old6 c, stepL.
  change zipRun machine253 (zAt (24 : Fin 253) (h + 2)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))) (4 * n + 2 * width pre + 216) = _
  rw [show 4 * n + 2 * width pre + 216 = (4 * n + 2 * width pre + 215) + 1 by omega, zipRun_first,
    step_left machine253 (24 : Fin 253) 25 false false _ _ _ (by decide)]
  -- 83: old9 l, norm.
  change zipRun machine253 (zAt (25 : Fin 253) ((h + 2) - 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))) (4 * n + 2 * width pre + 215) = _
  rw [show ((h + 2) - 1) = (h + 1) by omega]
  -- 84: old9 c, stepL.
  change zipRun machine253 (zAt (25 : Fin 253) (h + 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))) (4 * n + 2 * width pre + 215) = _
  rw [show 4 * n + 2 * width pre + 215 = (4 * n + 2 * width pre + 214) + 1 by omega, zipRun_first,
    step_left machine253 (25 : Fin 253) 26 false false _ _ _ (by decide)]
  -- 85: old13 l, norm.
  change zipRun machine253 (zAt (26 : Fin 253) ((h + 1) - 1)
      (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))
      (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))) (4 * n + 2 * width pre + 214) = _
  rw [show ((h + 1) - 1) = h by omega]
  -- 86: old13 c, stepL.
  change zipRun machine253 (zAt (26 : Fin 253) h
      (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))
      (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))) (4 * n + 2 * width pre + 214) = _
  rw [show 4 * n + 2 * width pre + 214 = (4 * n + 2 * width pre + 213) + 1 by omega, zipRun_first,
    step_left machine253 (26 : Fin 253) 27 false false _ _ _ (by decide)]
  -- 87: old19 l, norm.
  change zipRun machine253 (zAt (27 : Fin 253) (h - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))
      (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))) (4 * n + 2 * width pre + 213) = _
  -- 88: old19 c, stepL.
  change zipRun machine253 (zAt (27 : Fin 253) (h - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))
      (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))) (4 * n + 2 * width pre + 213) = _
  rw [show 4 * n + 2 * width pre + 213 = (4 * n + 2 * width pre + 212) + 1 by omega, zipRun_first,
    step_left machine253 (27 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 89: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h - 1) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))
      (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))) (4 * n + 2 * width pre + 212) = _
  rw [show ((h - 1) - 1) = (h - 2) by omega]
  -- 90: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h - 2)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))
      (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))) (4 * n + 2 * width pre + 212) = _
  rw [show 4 * n + 2 * width pre + 212 = (4 * n + 2 * width pre + 211) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 24 false false _ _ _ (by decide)]
  -- 91: old6 l, norm.
  change zipRun machine253 (zAt (24 : Fin 253) ((h - 2) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))) (4 * n + 2 * width pre + 211) = _
  rw [show ((h - 2) - 1) = (h - 3) by omega]
  -- 92: old6 c, stepL.
  change zipRun machine253 (zAt (24 : Fin 253) (h - 3)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))) (4 * n + 2 * width pre + 211) = _
  rw [show 4 * n + 2 * width pre + 211 = (4 * n + 2 * width pre + 210) + 1 by omega, zipRun_first,
    step_left machine253 (24 : Fin 253) 25 false false _ _ _ (by decide)]
  -- 93: old9 l, norm.
  change zipRun machine253 (zAt (25 : Fin 253) ((h - 3) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))) (4 * n + 2 * width pre + 210) = _
  rw [show ((h - 3) - 1) = (h - 4) by omega]
  -- 94: old9 c, stepL.
  change zipRun machine253 (zAt (25 : Fin 253) (h - 4)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))) (4 * n + 2 * width pre + 210) = _
  rw [show 4 * n + 2 * width pre + 210 = (4 * n + 2 * width pre + 209) + 1 by omega, zipRun_first,
    step_left machine253 (25 : Fin 253) 26 false false _ _ _ (by decide)]
  -- 95: old13 l, norm.
  change zipRun machine253 (zAt (26 : Fin 253) ((h - 4) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: L))))))
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))) (4 * n + 2 * width pre + 209) = _
  rw [show ((h - 4) - 1) = (h - 5) by omega]
  -- 96: old13 c, stepL.
  change zipRun machine253 (zAt (26 : Fin 253) (h - 5)
      (false :: (false :: (false :: (false :: (false :: (false :: L))))))
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))) (4 * n + 2 * width pre + 209) = _
  rw [show 4 * n + 2 * width pre + 209 = (4 * n + 2 * width pre + 208) + 1 by omega, zipRun_first,
    step_left machine253 (26 : Fin 253) 27 false false _ _ _ (by decide)]
  -- 97: old19 l, norm.
  change zipRun machine253 (zAt (27 : Fin 253) ((h - 5) - 1)
      (false :: (false :: (false :: (false :: (false :: L)))))
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))) (4 * n + 2 * width pre + 208) = _
  rw [show ((h - 5) - 1) = (h - 6) by omega]
  -- 98: old19 c, stepL.
  change zipRun machine253 (zAt (27 : Fin 253) (h - 6)
      (false :: (false :: (false :: (false :: (false :: L)))))
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))) (4 * n + 2 * width pre + 208) = _
  rw [show 4 * n + 2 * width pre + 208 = (4 * n + 2 * width pre + 207) + 1 by omega, zipRun_first,
    step_left machine253 (27 : Fin 253) 28 false false _ _ _ (by decide)]
  -- 99: old29 l, norm.
  change zipRun machine253 (zAt (28 : Fin 253) ((h - 6) - 1)
      (false :: (false :: (false :: (false :: L))))
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))) (4 * n + 2 * width pre + 207) = _
  rw [show ((h - 6) - 1) = (h - 7) by omega]
  -- 100: old29 c, stepL.
  change zipRun machine253 (zAt (28 : Fin 253) (h - 7)
      (false :: (false :: (false :: (false :: L))))
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))) (4 * n + 2 * width pre + 207) = _
  rw [show 4 * n + 2 * width pre + 207 = (4 * n + 2 * width pre + 206) + 1 by omega, zipRun_first,
    step_left machine253 (28 : Fin 253) 29 false false _ _ _ (by decide)]
  -- 101: old41 l, norm.
  change zipRun machine253 (zAt (29 : Fin 253) ((h - 7) - 1)
      (false :: (false :: (false :: L)))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))))) (4 * n + 2 * width pre + 206) = _
  rw [show ((h - 7) - 1) = (h - 8) by omega]
  -- 102: old41 c, stepL.
  change zipRun machine253 (zAt (29 : Fin 253) (h - 8)
      (false :: (false :: (false :: L)))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))))) (4 * n + 2 * width pre + 206) = _
  rw [show 4 * n + 2 * width pre + 206 = (4 * n + 2 * width pre + 205) + 1 by omega, zipRun_first,
    step_left machine253 (29 : Fin 253) 30 false false _ _ _ (by decide)]
  -- 103: old58 l, norm.
  change zipRun machine253 (zAt (30 : Fin 253) ((h - 8) - 1)
      (false :: (false :: L))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))))) (4 * n + 2 * width pre + 205) = _
  rw [show ((h - 8) - 1) = (h - 9) by omega]
  -- 104: old58 c, stepL.
  change zipRun machine253 (zAt (30 : Fin 253) (h - 9)
      (false :: (false :: L))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))))) (4 * n + 2 * width pre + 205) = _
  rw [show 4 * n + 2 * width pre + 205 = (4 * n + 2 * width pre + 204) + 1 by omega, zipRun_first,
    step_left machine253 (30 : Fin 253) 31 false false _ _ _ (by decide)]
  -- 105: old74 l, norm.
  change zipRun machine253 (zAt (31 : Fin 253) ((h - 9) - 1)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))))))) (4 * n + 2 * width pre + 204) = _
  rw [show ((h - 9) - 1) = (h - 10) by omega]
  -- 106: old74 c, stepL.
  change zipRun machine253 (zAt (31 : Fin 253) (h - 10)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))))))) (4 * n + 2 * width pre + 204) = _
  rw [show 4 * n + 2 * width pre + 204 = (4 * n + 2 * width pre + 203) + 1 by omega, zipRun_first,
    step_left machine253 (31 : Fin 253) 32 false false _ _ _ (by decide)]
  -- 107: old84 l, norm.
  change zipRun machine253 (zAt (32 : Fin 253) ((h - 10) - 1)
      L
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))))))) (4 * n + 2 * width pre + 203) = _
  rw [show ((h - 10) - 1) = (h - 11) by omega]
  -- 108: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 11)
      L
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))))))) (4 * n + 2 * width pre + 203) = _
  rw [show 4 * n + 2 * width pre + 203 = (4 * n + 2 * width pre + 202) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 11) + 1) = (h - 10) by omega]
  -- 109: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 10)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))))))) (4 * n + 2 * width pre + 202) = _
  rw [show 4 * n + 2 * width pre + 202 = (4 * n + 2 * width pre + 201) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 10) + 1) = (h - 9) by omega]
  -- 110: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 9)
      (false :: (false :: L))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))))) (4 * n + 2 * width pre + 201) = _
  rw [show 4 * n + 2 * width pre + 201 = (4 * n + 2 * width pre + 200) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 9) + 1) = (h - 8) by omega]
  -- 111: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 8)
      (false :: (false :: (false :: L)))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))))) (4 * n + 2 * width pre + 200) = _
  rw [show 4 * n + 2 * width pre + 200 = (4 * n + 2 * width pre + 199) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 8) + 1) = (h - 7) by omega]
  -- 112: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 7)
      (false :: (false :: (false :: (false :: L))))
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))))) (4 * n + 2 * width pre + 199) = _
  rw [show 4 * n + 2 * width pre + 199 = (4 * n + 2 * width pre + 198) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 7) + 1) = (h - 6) by omega]
  -- 113: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 6)
      (false :: (false :: (false :: (false :: (false :: L)))))
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))))) (4 * n + 2 * width pre + 198) = _
  rw [show 4 * n + 2 * width pre + 198 = (4 * n + 2 * width pre + 197) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 6) + 1) = (h - 5) by omega]
  -- 114: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 5)
      (false :: (false :: (false :: (false :: (false :: (false :: L))))))
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))))) (4 * n + 2 * width pre + 197) = _
  rw [show 4 * n + 2 * width pre + 197 = (4 * n + 2 * width pre + 196) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 5) + 1) = (h - 4) by omega]
  -- 115: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 4)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))))) (4 * n + 2 * width pre + 196) = _
  rw [show 4 * n + 2 * width pre + 196 = (4 * n + 2 * width pre + 195) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 4) + 1) = (h - 3) by omega]
  -- 116: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 3)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))))) (4 * n + 2 * width pre + 195) = _
  rw [show 4 * n + 2 * width pre + 195 = (4 * n + 2 * width pre + 194) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 3) + 1) = (h - 2) by omega]
  -- 117: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 2)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))
      (false :: (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))))) (4 * n + 2 * width pre + 194) = _
  rw [show 4 * n + 2 * width pre + 194 = (4 * n + 2 * width pre + 193) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 2) + 1) = (h - 1) by omega]
  -- 118: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))
      (true :: (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))))) (4 * n + 2 * width pre + 193) = _
  rw [show 4 * n + 2 * width pre + 193 = (4 * n + 2 * width pre + 192) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 33 true true _ _ _ (by decide)]
  rw [show ((h - 1) + 1) = h by omega]
  -- 119: old96 c, stepR.
  change zipRun machine253 (zAt (33 : Fin 253) h
      (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))
      (false :: (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))))) (4 * n + 2 * width pre + 192) = _
  rw [show 4 * n + 2 * width pre + 192 = (4 * n + 2 * width pre + 191) + 1 by omega, zipRun_first,
    step_right machine253 (33 : Fin 253) 34 false false _ _ _ (by decide)]
  -- 120: old110 c, stepR.
  change zipRun machine253 (zAt (34 : Fin 253) (h + 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))) (4 * n + 2 * width pre + 191) = _
  rw [show 4 * n + 2 * width pre + 191 = (4 * n + 2 * width pre + 190) + 1 by omega, zipRun_first,
    step_right machine253 (34 : Fin 253) 36 false false _ _ _ (by decide)]
  rw [show ((h + 1) + 1) = (h + 2) by omega]
  -- 121: old33 c, stepR.
  change zipRun machine253 (zAt (36 : Fin 253) (h + 2)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))) (4 * n + 2 * width pre + 190) = _
  rw [show 4 * n + 2 * width pre + 190 = (4 * n + 2 * width pre + 189) + 1 by omega, zipRun_first,
    step_right machine253 (36 : Fin 253) 40 false false _ _ _ (by decide)]
  rw [show ((h + 2) + 1) = (h + 3) by omega]
  -- 122: old47 c, stepL.
  change zipRun machine253 (zAt (40 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))) (4 * n + 2 * width pre + 189) = _
  rw [show 4 * n + 2 * width pre + 189 = (4 * n + 2 * width pre + 188) + 1 by omega, zipRun_first,
    step_left machine253 (40 : Fin 253) 47 false false _ _ _ (by decide)]
  -- 123: old27 l, norm.
  change zipRun machine253 (zAt (47 : Fin 253) ((h + 3) - 1)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))) (4 * n + 2 * width pre + 188) = _
  rw [show ((h + 3) - 1) = (h + 2) by omega]
  -- 124: old27 c, stepL.
  change zipRun machine253 (zAt (47 : Fin 253) (h + 2)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))) (4 * n + 2 * width pre + 188) = _
  rw [show 4 * n + 2 * width pre + 188 = (4 * n + 2 * width pre + 187) + 1 by omega, zipRun_first,
    step_left machine253 (47 : Fin 253) 58 false false _ _ _ (by decide)]
  -- 125: old32 l, norm.
  change zipRun machine253 (zAt (58 : Fin 253) ((h + 2) - 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))) (4 * n + 2 * width pre + 187) = _
  rw [show ((h + 2) - 1) = (h + 1) by omega]
  -- 126: old32 c, stepR.
  change zipRun machine253 (zAt (58 : Fin 253) (h + 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))))) (4 * n + 2 * width pre + 187) = _
  rw [show 4 * n + 2 * width pre + 187 = (4 * n + 2 * width pre + 186) + 1 by omega, zipRun_first,
    step_right machine253 (58 : Fin 253) 71 false false _ _ _ (by decide)]
  rw [show ((h + 1) + 1) = (h + 2) by omega]
  -- 127: old45 c, stepR.
  change zipRun machine253 (zAt (71 : Fin 253) (h + 2)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))))) (4 * n + 2 * width pre + 186) = _
  rw [show 4 * n + 2 * width pre + 186 = (4 * n + 2 * width pre + 185) + 1 by omega, zipRun_first,
    step_right machine253 (71 : Fin 253) 67 false false _ _ _ (by decide)]
  rw [show ((h + 2) + 1) = (h + 3) by omega]
  -- 128: old21 c, stepR.
  change zipRun machine253 (zAt (67 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))))) (4 * n + 2 * width pre + 185) = _
  rw [show 4 * n + 2 * width pre + 185 = (4 * n + 2 * width pre + 184) + 1 by omega, zipRun_first,
    step_right machine253 (67 : Fin 253) 64 false false _ _ _ (by decide)]
  rw [show ((h + 3) + 1) = (h + 4) by omega]
  -- 129: old30 c, stepR.
  change zipRun machine253 (zAt (64 : Fin 253) (h + 4)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (true :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))))) (4 * n + 2 * width pre + 184) = _
  rw [show 4 * n + 2 * width pre + 184 = (4 * n + 2 * width pre + 183) + 1 by omega, zipRun_first,
    step_right machine253 (64 : Fin 253) 79 true false _ _ _ (by decide)]
  rw [show ((h + 4) + 1) = (h + 5) by omega]
  -- 130: old43 c, scanR.
  change zipRun machine253 (zAt (79 : Fin 253) (h + 5)
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))
      (List.replicate (n + 34) true ++ (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))))) (4 * n + 2 * width pre + 183) = _
  rw [show 4 * n + 2 * width pre + 183 = (n + 34) + (3 * n + 2 * width pre + 149) by omega, zipRun_add,
    scan_right_write machine253 (79 : Fin 253) true true (by decide)]
  rw [show ((h + 5) + (((n + 34) : Nat) : Int)) = (h + (n : Int) + 39) by omega]
  -- 131: old43 c, stepR.
  change zipRun machine253 (zAt (79 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))))) (3 * n + 2 * width pre + 149) = _
  rw [show 3 * n + 2 * width pre + 149 = (3 * n + 2 * width pre + 148) + 1 by omega, zipRun_first,
    step_right machine253 (79 : Fin 253) 79 true true _ _ _ (by decide)]
  rw [show ((h + (n : Int) + 39) + 1) = (h + (n : Int) + 40) by omega]
  -- 132: old43 c, stepR.
  change zipRun machine253 (zAt (79 : Fin 253) (h + (n : Int) + 40)
      (true :: (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (true :: (registerBits pre ++ false :: false :: (registerBits rest ++ [false])))) (3 * n + 2 * width pre + 148) = _
  rw [show 3 * n + 2 * width pre + 148 = (3 * n + 2 * width pre + 147) + 1 by omega, zipRun_first,
    step_right machine253 (79 : Fin 253) 79 true true _ _ _ (by decide)]
  rw [show ((h + (n : Int) + 40) + 1) = (h + (n : Int) + 41) by omega]
  -- 133: old43 c, decz.
  change zipRun machine253 (zAt seekDec (h + (n : Int) + 41)
      (true :: (true :: (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))))
      (registerBits pre ++ false :: false :: (registerBits rest ++ [false]))) (3 * n + 2 * width pre + 147) = _
  rw [show 3 * n + 2 * width pre + 147 = (2 * width pre + 5) + (3 * n + 142) by omega, zipRun_add,
    zero_decrement_zip pre rest]
  -- 134: old3 l, norm.
  change zipRun machine253 (zAt (23 : Fin 253) ((h + (n : Int) + 41) - 1)
      (true :: (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))) (3 * n + 142) = _
  rw [show ((h + (n : Int) + 41) - 1) = (h + (n : Int) + 40) by omega]
  -- 135: old3 c, stepL.
  change zipRun machine253 (zAt (23 : Fin 253) (h + (n : Int) + 40)
      (true :: (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))) (3 * n + 142) = _
  rw [show 3 * n + 142 = (3 * n + 141) + 1 by omega, zipRun_first,
    step_left machine253 (23 : Fin 253) 21 true true _ _ _ (by decide)]
  -- 136: old1 l, norm.
  change zipRun machine253 (zAt (21 : Fin 253) ((h + (n : Int) + 40) - 1)
      (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (3 * n + 141) = _
  rw [show ((h + (n : Int) + 40) - 1) = (h + (n : Int) + 39) by omega]
  -- 137: old1 c, stepL.
  change zipRun machine253 (zAt (21 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (3 * n + 141) = _
  rw [show 3 * n + 141 = (3 * n + 140) + 1 by omega, zipRun_first,
    step_left machine253 (21 : Fin 253) 21 true true _ _ _ (by decide)]
  -- 138: old1 l, scanL.
  change zipRun machine253 (leftAt (21 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 34) true ++ (false :: (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (3 * n + 140) = _
  rw [show 3 * n + 140 = (n + 34) + (2 * n + 106) by omega, zipRun_add,
    scan_left_write machine253 (21 : Fin 253) true true (by decide)]
  rw [show ((h + (n : Int) + 39) - (((n + 34) : Nat) : Int)) = (h + 5) by omega]
  -- 139: old1 l, norm.
  change zipRun machine253 (zAt (21 : Fin 253) ((h + 5) - 1)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (2 * n + 106) = _
  rw [show ((h + 5) - 1) = (h + 4) by omega]
  -- 140: old1 c, stepL.
  change zipRun machine253 (zAt (21 : Fin 253) (h + 4)
      (false :: (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (2 * n + 106) = _
  rw [show 2 * n + 106 = (2 * n + 105) + 1 by omega, zipRun_first,
    step_left machine253 (21 : Fin 253) 23 false false _ _ _ (by decide)]
  -- 141: old3 l, norm.
  change zipRun machine253 (zAt (23 : Fin 253) ((h + 4) - 1)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (2 * n + 105) = _
  rw [show ((h + 4) - 1) = (h + 3) by omega]
  -- 142: old3 c, stepL.
  change zipRun machine253 (zAt (23 : Fin 253) (h + 3)
      (false :: (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (2 * n + 105) = _
  rw [show 2 * n + 105 = (2 * n + 104) + 1 by omega, zipRun_first,
    step_left machine253 (23 : Fin 253) 10 false false _ _ _ (by decide)]
  -- 143: old48 l, norm.
  change zipRun machine253 (zAt (10 : Fin 253) ((h + 3) - 1)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (2 * n + 104) = _
  rw [show ((h + 3) - 1) = (h + 2) by omega]
  -- 144: old48 c, stepL.
  change zipRun machine253 (zAt (10 : Fin 253) (h + 2)
      (false :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (2 * n + 104) = _
  rw [show 2 * n + 104 = (2 * n + 103) + 1 by omega, zipRun_first,
    step_left machine253 (10 : Fin 253) 12 false false _ _ _ (by decide)]
  -- 145: old7 l, norm.
  change zipRun machine253 (zAt (12 : Fin 253) ((h + 2) - 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))) (2 * n + 103) = _
  rw [show ((h + 2) - 1) = (h + 1) by omega]
  -- 146: old7 c, stepR.
  change zipRun machine253 (zAt (12 : Fin 253) (h + 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (false :: (false :: (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))) (2 * n + 103) = _
  rw [show 2 * n + 103 = (2 * n + 102) + 1 by omega, zipRun_first,
    step_right machine253 (12 : Fin 253) 14 false true _ _ _ (by decide)]
  rw [show ((h + 1) + 1) = (h + 2) by omega]
  -- 147: old10 c, stepR.
  change zipRun machine253 (zAt (14 : Fin 253) (h + 2)
      (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (2 * n + 102) = _
  rw [show 2 * n + 102 = (2 * n + 101) + 1 by omega, zipRun_first,
    step_right machine253 (14 : Fin 253) 14 false false _ _ _ (by decide)]
  rw [show ((h + 2) + 1) = (h + 3) by omega]
  -- 148: old10 c, stepR.
  change zipRun machine253 (zAt (14 : Fin 253) (h + 3)
      (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (2 * n + 101) = _
  rw [show 2 * n + 101 = (2 * n + 100) + 1 by omega, zipRun_first,
    step_right machine253 (14 : Fin 253) 14 false false _ _ _ (by decide)]
  rw [show ((h + 3) + 1) = (h + 4) by omega]
  -- 149: old10 c, stepR.
  change zipRun machine253 (zAt (14 : Fin 253) (h + 4)
      (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (false :: (List.replicate (n + 34) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (2 * n + 100) = _
  rw [show 2 * n + 100 = (2 * n + 99) + 1 by omega, zipRun_first,
    step_right machine253 (14 : Fin 253) 14 false false _ _ _ (by decide)]
  rw [show ((h + 4) + 1) = (h + 5) by omega]
  -- 151: old10 c, stepR.
  change zipRun machine253 (zAt (14 : Fin 253) (h + 5)
      (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))
      (true :: (List.replicate (n + 33) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (2 * n + 99) = _
  rw [show 2 * n + 99 = (2 * n + 98) + 1 by omega, zipRun_first,
    step_right machine253 (14 : Fin 253) 16 true false _ _ _ (by decide)]
  rw [show ((h + 5) + 1) = (h + 6) by omega]
  -- 152: old14 c, scanR.
  change zipRun machine253 (zAt (16 : Fin 253) (h + 6)
      (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))
      (List.replicate (n + 33) true ++ (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))) (2 * n + 98) = _
  rw [show 2 * n + 98 = (n + 33) + (n + 65) by omega, zipRun_add,
    scan_right_write machine253 (16 : Fin 253) true false (by decide)]
  rw [show ((h + 6) + (((n + 33) : Nat) : Int)) = (h + (n : Int) + 39) by omega]
  -- 153: old14 c, stepR.
  change zipRun machine253 (zAt (16 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (true :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (n + 65) = _
  rw [show n + 65 = (n + 64) + 1 by omega, zipRun_first,
    step_right machine253 (16 : Fin 253) 16 true false _ _ _ (by decide)]
  rw [show ((h + (n : Int) + 39) + 1) = (h + (n : Int) + 40) by omega]
  -- 154: old14 c, stepR.
  change zipRun machine253 (zAt (16 : Fin 253) (h + (n : Int) + 40)
      (false :: (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))))
      (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))) (n + 64) = _
  rw [show n + 64 = (n + 63) + 1 by omega, zipRun_first,
    step_right machine253 (16 : Fin 253) 16 true false _ _ _ (by decide)]
  rw [show ((h + (n : Int) + 40) + 1) = (h + (n : Int) + 41) by omega]
  -- 155: old14 c, fileL.
  change zipRun machine253 (zAt (16 : Fin 253) (h + (n : Int) + 41)
      (false :: (false :: (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))))
      (false :: true :: ((List.replicate a true ++ registerBits ([b, c, d, e] ++ 0 :: rest)) ++ [false]))) (n + 63) = _
  rw [show n + 63 = (n + 62) + 1 by omega, zipRun_first,
    step_left machine253 (16 : Fin 253) 18 false false _ _ _ (by decide)]
  -- 156: old20 l, norm.
  change zipRun machine253 (zAt (18 : Fin 253) ((h + (n : Int) + 41) - 1)
      (false :: (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))))
      (false :: (registerBits (pre ++ 0 :: rest) ++ [false]))) (n + 62) = _
  rw [show ((h + (n : Int) + 41) - 1) = (h + (n : Int) + 40) by omega]
  -- 157: old20 c, stepL.
  change zipRun machine253 (zAt (18 : Fin 253) (h + (n : Int) + 40)
      (false :: (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))))))
      (false :: (registerBits (pre ++ 0 :: rest) ++ [false]))) (n + 62) = _
  rw [show n + 62 = (n + 61) + 1 by omega, zipRun_first,
    step_left machine253 (18 : Fin 253) 20 false true _ _ _ (by decide)]
  -- 158: old2 l, norm.
  change zipRun machine253 (zAt (20 : Fin 253) ((h + (n : Int) + 40) - 1)
      (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (n + 61) = _
  rw [show ((h + (n : Int) + 40) - 1) = (h + (n : Int) + 39) by omega]
  -- 159: old2 c, stepL.
  change zipRun machine253 (zAt (20 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (n + 61) = _
  rw [show n + 61 = (n + 60) + 1 by omega, zipRun_first,
    step_left machine253 (20 : Fin 253) 20 false false _ _ _ (by decide)]
  -- 160: old2 l, scanL.
  change zipRun machine253 (leftAt (20 : Fin 253) (h + (n : Int) + 39)
      (List.replicate (n + 33) false ++ (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))))
      (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))) (n + 60) = _
  rw [show n + 60 = (n + 33) + (27) by omega, zipRun_add,
    scan_left_write machine253 (20 : Fin 253) false false (by decide)]
  rw [show ((h + (n : Int) + 39) - (((n + 33) : Nat) : Int)) = (h + 6) by omega]
  -- 161: old2 l, norm.
  change zipRun machine253 (zAt (20 : Fin 253) ((h + 6) - 1)
      (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))
      (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (27) = _
  rw [show ((h + 6) - 1) = (h + 5) by omega]
  -- 162: old2 c, stepL.
  change zipRun machine253 (zAt (20 : Fin 253) (h + 5)
      (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))))
      (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))) (27) = _
  rw [show 27 = (26) + 1 by omega, zipRun_first,
    step_left machine253 (20 : Fin 253) 20 false false _ _ _ (by decide)]
  -- 163: old2 l, norm.
  change zipRun machine253 (zAt (20 : Fin 253) ((h + 5) - 1)
      (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (26) = _
  rw [show ((h + 5) - 1) = (h + 4) by omega]
  -- 164: old2 c, stepL.
  change zipRun machine253 (zAt (20 : Fin 253) (h + 4)
      (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))))
      (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))) (26) = _
  rw [show 26 = (25) + 1 by omega, zipRun_first,
    step_left machine253 (20 : Fin 253) 20 false false _ _ _ (by decide)]
  -- 165: old2 l, norm.
  change zipRun machine253 (zAt (20 : Fin 253) ((h + 4) - 1)
      (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (25) = _
  rw [show ((h + 4) - 1) = (h + 3) by omega]
  -- 166: old2 c, stepL.
  change zipRun machine253 (zAt (20 : Fin 253) (h + 3)
      (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))))
      (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))) (25) = _
  rw [show 25 = (24) + 1 by omega, zipRun_first,
    step_left machine253 (20 : Fin 253) 20 false false _ _ _ (by decide)]
  -- 167: old2 l, norm.
  change zipRun machine253 (zAt (20 : Fin 253) ((h + 3) - 1)
      (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))) (24) = _
  rw [show ((h + 3) - 1) = (h + 2) by omega]
  -- 168: old2 c, stepL.
  change zipRun machine253 (zAt (20 : Fin 253) (h + 2)
      (true :: (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))))
      (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))) (24) = _
  rw [show 24 = (23) + 1 by omega, zipRun_first,
    step_left machine253 (20 : Fin 253) 20 false false _ _ _ (by decide)]
  -- 169: old2 l, norm.
  change zipRun machine253 (zAt (20 : Fin 253) ((h + 2) - 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))) (23) = _
  rw [show ((h + 2) - 1) = (h + 1) by omega]
  -- 170: old2 c, stepL.
  change zipRun machine253 (zAt (20 : Fin 253) (h + 1)
      (false :: (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))))
      (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))) (23) = _
  rw [show 23 = (22) + 1 by omega, zipRun_first,
    step_left machine253 (20 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 171: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h + 1) - 1)
      (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))
      (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))) (22) = _
  rw [show ((h + 1) - 1) = h by omega]
  -- 172: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) h
      (true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))))
      (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))) (22) = _
  rw [show 22 = (21) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 24 false false _ _ _ (by decide)]
  -- 173: old6 l, norm.
  change zipRun machine253 (zAt (24 : Fin 253) (h - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))
      (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))) (21) = _
  -- 174: old6 c, stepL.
  change zipRun machine253 (zAt (24 : Fin 253) (h - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))
      (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))) (21) = _
  rw [show 21 = (20) + 1 by omega, zipRun_first,
    step_left machine253 (24 : Fin 253) 22 true true _ _ _ (by decide)]
  -- 175: old4 l, norm.
  change zipRun machine253 (zAt (22 : Fin 253) ((h - 1) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))
      (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))) (20) = _
  rw [show ((h - 1) - 1) = (h - 2) by omega]
  -- 176: old4 c, stepL.
  change zipRun machine253 (zAt (22 : Fin 253) (h - 2)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))
      (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))) (20) = _
  rw [show 20 = (19) + 1 by omega, zipRun_first,
    step_left machine253 (22 : Fin 253) 24 false false _ _ _ (by decide)]
  -- 177: old6 l, norm.
  change zipRun machine253 (zAt (24 : Fin 253) ((h - 2) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))
      (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))) (19) = _
  rw [show ((h - 2) - 1) = (h - 3) by omega]
  -- 178: old6 c, stepL.
  change zipRun machine253 (zAt (24 : Fin 253) (h - 3)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))
      (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))) (19) = _
  rw [show 19 = (18) + 1 by omega, zipRun_first,
    step_left machine253 (24 : Fin 253) 25 false false _ _ _ (by decide)]
  -- 179: old9 l, norm.
  change zipRun machine253 (zAt (25 : Fin 253) ((h - 3) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))
      (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))) (18) = _
  rw [show ((h - 3) - 1) = (h - 4) by omega]
  -- 180: old9 c, stepL.
  change zipRun machine253 (zAt (25 : Fin 253) (h - 4)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))
      (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))) (18) = _
  rw [show 18 = (17) + 1 by omega, zipRun_first,
    step_left machine253 (25 : Fin 253) 26 false false _ _ _ (by decide)]
  -- 181: old13 l, norm.
  change zipRun machine253 (zAt (26 : Fin 253) ((h - 4) - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: L))))))
      (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))) (17) = _
  rw [show ((h - 4) - 1) = (h - 5) by omega]
  -- 182: old13 c, stepL.
  change zipRun machine253 (zAt (26 : Fin 253) (h - 5)
      (false :: (false :: (false :: (false :: (false :: (false :: L))))))
      (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))) (17) = _
  rw [show 17 = (16) + 1 by omega, zipRun_first,
    step_left machine253 (26 : Fin 253) 27 false false _ _ _ (by decide)]
  -- 183: old19 l, norm.
  change zipRun machine253 (zAt (27 : Fin 253) ((h - 5) - 1)
      (false :: (false :: (false :: (false :: (false :: L)))))
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))) (16) = _
  rw [show ((h - 5) - 1) = (h - 6) by omega]
  -- 184: old19 c, stepL.
  change zipRun machine253 (zAt (27 : Fin 253) (h - 6)
      (false :: (false :: (false :: (false :: (false :: L)))))
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))) (16) = _
  rw [show 16 = (15) + 1 by omega, zipRun_first,
    step_left machine253 (27 : Fin 253) 28 false false _ _ _ (by decide)]
  -- 185: old29 l, norm.
  change zipRun machine253 (zAt (28 : Fin 253) ((h - 6) - 1)
      (false :: (false :: (false :: (false :: L))))
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))) (15) = _
  rw [show ((h - 6) - 1) = (h - 7) by omega]
  -- 186: old29 c, stepL.
  change zipRun machine253 (zAt (28 : Fin 253) (h - 7)
      (false :: (false :: (false :: (false :: L))))
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))) (15) = _
  rw [show 15 = (14) + 1 by omega, zipRun_first,
    step_left machine253 (28 : Fin 253) 29 false false _ _ _ (by decide)]
  -- 187: old41 l, norm.
  change zipRun machine253 (zAt (29 : Fin 253) ((h - 7) - 1)
      (false :: (false :: (false :: L)))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))) (14) = _
  rw [show ((h - 7) - 1) = (h - 8) by omega]
  -- 188: old41 c, stepL.
  change zipRun machine253 (zAt (29 : Fin 253) (h - 8)
      (false :: (false :: (false :: L)))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))) (14) = _
  rw [show 14 = (13) + 1 by omega, zipRun_first,
    step_left machine253 (29 : Fin 253) 30 false false _ _ _ (by decide)]
  -- 189: old58 l, norm.
  change zipRun machine253 (zAt (30 : Fin 253) ((h - 8) - 1)
      (false :: (false :: L))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))) (13) = _
  rw [show ((h - 8) - 1) = (h - 9) by omega]
  -- 190: old58 c, stepL.
  change zipRun machine253 (zAt (30 : Fin 253) (h - 9)
      (false :: (false :: L))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))) (13) = _
  rw [show 13 = (12) + 1 by omega, zipRun_first,
    step_left machine253 (30 : Fin 253) 31 false false _ _ _ (by decide)]
  -- 191: old74 l, norm.
  change zipRun machine253 (zAt (31 : Fin 253) ((h - 9) - 1)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))))) (12) = _
  rw [show ((h - 9) - 1) = (h - 10) by omega]
  -- 192: old74 c, stepL.
  change zipRun machine253 (zAt (31 : Fin 253) (h - 10)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))))) (12) = _
  rw [show 12 = (11) + 1 by omega, zipRun_first,
    step_left machine253 (31 : Fin 253) 32 false false _ _ _ (by decide)]
  -- 193: old84 l, norm.
  change zipRun machine253 (zAt (32 : Fin 253) ((h - 10) - 1)
      L
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))))) (11) = _
  rw [show ((h - 10) - 1) = (h - 11) by omega]
  -- 194: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 11)
      L
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))))) (11) = _
  rw [show 11 = (10) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 11) + 1) = (h - 10) by omega]
  -- 195: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 10)
      (false :: L)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))))) (10) = _
  rw [show 10 = (9) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 10) + 1) = (h - 9) by omega]
  -- 196: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 9)
      (false :: (false :: L))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))))) (9) = _
  rw [show 9 = (8) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 9) + 1) = (h - 8) by omega]
  -- 197: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 8)
      (false :: (false :: (false :: L)))
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))))) (8) = _
  rw [show 8 = (7) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 8) + 1) = (h - 7) by omega]
  -- 198: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 7)
      (false :: (false :: (false :: (false :: L))))
      (false :: (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))))) (7) = _
  rw [show 7 = (6) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 7) + 1) = (h - 6) by omega]
  -- 199: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 6)
      (false :: (false :: (false :: (false :: (false :: L)))))
      (false :: (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))))) (6) = _
  rw [show 6 = (5) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 6) + 1) = (h - 5) by omega]
  -- 200: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 5)
      (false :: (false :: (false :: (false :: (false :: (false :: L))))))
      (false :: (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))))) (5) = _
  rw [show 5 = (4) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 5) + 1) = (h - 4) by omega]
  -- 201: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 4)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))
      (false :: (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))))) (4) = _
  rw [show 4 = (3) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 4) + 1) = (h - 3) by omega]
  -- 202: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 3)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))
      (false :: (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))))) (3) = _
  rw [show 3 = (2) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 3) + 1) = (h - 2) by omega]
  -- 203: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 2)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L)))))))))
      (false :: (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false]))))))))))))) (2) = _
  rw [show 2 = (1) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 32 false false _ _ _ (by decide)]
  rw [show ((h - 2) + 1) = (h - 1) by omega]
  -- 204: old84 c, stepR.
  change zipRun machine253 (zAt (32 : Fin 253) (h - 1)
      (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: L))))))))))
      (true :: (false :: (true :: (false :: (false :: (false :: (false :: (List.replicate (n + 33) false ++ (false :: (true :: (registerBits (pre ++ 0 :: rest) ++ [false])))))))))))) (1) = _
  rw [show 1 = (0) + 1 by omega, zipRun_first,
    step_right machine253 (32 : Fin 253) 33 true true _ _ _ (by decide)]
  rw [show ((h - 1) + 1) = h by omega]
  simp only [zipRun]
  rw [replicate_snoc]
  simp only [List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append]
  congr 1 <;> omega

/-- The universal execution statement uses every represented Core tape cell. -/
theorem zero000_core {binary : Config 253} (n a b c d e : Nat) (rest : List Nat)
    (h : Int) (L : List Bool)
    (hb : ZipRep binary
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (false :: false :: false :: (List.replicate (n + 37) false ++ true ::
          (registerBits (pre a b c d e ++ 0 :: rest) ++ [false]))))) :
    ZipRep (machine253.runFrom binary (8 * n + 4 * width (pre a b c d e) + 406))
      (zAt (33 : Fin 253) h (true :: (List.replicate 10 false ++ L))
        (false :: true :: (List.replicate (n + 38) false ++ true ::
          (registerBits (pre a b c d e ++ 0 :: rest) ++ [false])))) := by
  have hs := zipRun_sound machine253 (8 * n + 4 * width (pre a b c d e) + 406) hb
  rw [zero000_zip] at hs
  exact hs

/-- The literal path program reads logical register8 at site000. -/
theorem register_zero000 (R : RegisterPath.Registers) (hz : R 8 = 0) :
    RegisterPath.step Prog254.program ⟨[false, false, false], R⟩ =
      some ⟨[false, true], R⟩ := by
  change RegisterPath.execute (.decnz 8) [false, false, false] R = _
  simp only [RegisterPath.execute, hz]
  rfl

private theorem getD_zero_padding (padding i : Nat) :
    (List.replicate padding false).getD i false = false := by
  induction padding generalizing i with
  | zero => rfl
  | succ padding ih => cases i with
    | zero => rfl
    | succ i => exact ih i

private theorem getD_append_padding (r : List Bool) (padding i : Nat) :
    (r ++ List.replicate padding false).getD i false = r.getD i false := by
  induction r generalizing i with
  | nil => exact getD_zero_padding padding i
  | cons b r ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- False finite padding can change representation without changing a cell. -/
theorem normalize_right_padding {binary : Config 253} (q : Fin 253) (h : Int)
    (l r : List Bool) (padding : Nat)
    (hb : ZipRep binary (zAt q h l (r ++ List.replicate padding false))) :
    ZipRep binary (zAt q h l (r ++ [false])) := by
  refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩
  intro i
  have hi := hb.2.2.2 i
  change Tape.read binary.tape (h + (i : Int)) =
    (r ++ List.replicate padding false).getD i false at hi
  change Tape.read binary.tape (h + (i : Int)) =
    (r ++ List.replicate 1 false).getD i false
  rw [getD_append_padding] at hi ⊢
  exact hi

private theorem dispatch_state : BootstrapFrame253.dispatch253 = (33 : Fin 253) := by decide

private theorem registerBits_frame (values : List Nat) :
    BootstrapFrame253.registerBits values = registerBits values := by
  rw [registerBits_eq_flatMap]
  rfl

/-- Physical blocks before logical register8, in the published permutation. -/
def prefixWidth (R : RegisterPath.Registers) : Nat :=
  width [R 2, R 4, R 3, R 7, R 6]

/-- The actual site retains every register and spare, changes000 to01, and
increases its zero padding by one. This is not a first-return statement. -/
theorem dispatch_frame_zero000 {binary : Config 253} (logical : RegisterPath.Configuration)
    (gap : Nat) (spares : List Nat) (hp : logical.path = [false, false, false])
    (hz : logical.registers 8 = 0)
    (hb : BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253 binary logical gap spares) :
    BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253
      (machine253.runFrom binary (8 * gap + 4 * prefixWidth logical.registers + 110))
      { logical with path := [false, true] } (gap + 1) spares := by
  rcases hb with ⟨hgap, htail, leftPadding, rightPadding, hrep⟩
  have hmin : 37 ≤ gap := by
    simp only [hp, List.length_cons, List.length_nil] at hgap
    omega
  obtain ⟨n, hn⟩ : ∃ n : Nat, gap = n + 37 := ⟨gap - 37, by omega⟩
  have hfile : BootstrapFrame253.registerBits
      (BootstrapFrame253.primaryValues logical.registers ++ spares) =
      registerBits (pre (logical.registers 2) (logical.registers 4) (logical.registers 3)
        (logical.registers 7) (logical.registers 6) ++
        0 :: (logical.registers 0 :: logical.registers 1 :: logical.registers 5 :: spares)) := by
    rw [registerBits_frame]
    simp only [BootstrapFrame253.primaryValues, Prefix330.physicalOrder, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, pre, hz]
  change ZipRep binary
    (zAt BootstrapFrame253.dispatch253 binary.head (true :: List.replicate leftPadding false)
      (logical.path ++ List.replicate gap false ++ [true] ++
        BootstrapFrame253.registerBits (BootstrapFrame253.primaryValues logical.registers ++ spares) ++
        List.replicate rightPadding false)) at hrep
  have hrep' : ZipRep binary
      (zAt BootstrapFrame253.dispatch253 binary.head (true :: List.replicate leftPadding false)
        ((logical.path ++ List.replicate gap false ++ [true] ++
          BootstrapFrame253.registerBits (BootstrapFrame253.primaryValues logical.registers ++ spares)) ++
          List.replicate rightPadding false)) := by
    simpa only [List.append_assoc] using hrep
  have hl := BreakSite253.normalize_left_margin BootstrapFrame253.dispatch253 binary.head
    leftPadding _ hrep'
  have hr := normalize_right_padding BootstrapFrame253.dispatch253 binary.head
    (true :: List.replicate 10 false) _ rightPadding hl
  have hi : ZipRep binary
      (zAt (33 : Fin 253) binary.head (true :: (List.replicate 10 false ++ []))
        (false :: false :: false :: (List.replicate (n + 37) false ++ true ::
          (registerBits (pre (logical.registers 2) (logical.registers 4) (logical.registers 3)
            (logical.registers 7) (logical.registers 6) ++
            0 :: (logical.registers 0 :: logical.registers 1 :: logical.registers 5 :: spares)) ++
            [false])))) := by
    simpa only [dispatch_state, hp, hn, hfile, List.append_assoc,
      List.cons_append, List.nil_append, List.append_nil] using hr
  have hs := zero000_core n (logical.registers 2) (logical.registers 4) (logical.registers 3)
    (logical.registers 7) (logical.registers 6)
    (logical.registers 0 :: logical.registers 1 :: logical.registers 5 :: spares)
    binary.head [] hi
  have htime : 8 * n + 4 * width (pre (logical.registers 2) (logical.registers 4)
      (logical.registers 3) (logical.registers 7) (logical.registers 6)) + 406 =
      8 * gap + 4 * prefixWidth logical.registers + 110 := by
    simp only [prefixWidth, pre]
    omega
  rw [htime] at hs
  have hh := hs.2.1
  refine ⟨?_, htail, 10, 1, ?_⟩
  · change 40 ≤ 2 + (gap + 1)
    omega
  · rw [hh]
    simpa only [BootstrapFrame253.dispatchZip, dispatch_state,
      zAt, hfile, hn, List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil, List.replicate_succ, List.replicate_zero] using hs

/-- The literal register step and the whole binary dispatch frame agree. -/
theorem paired_zero000 {binary : Config 253} (logical : RegisterPath.Configuration)
    (gap : Nat) (spares : List Nat) (hp : logical.path = [false, false, false])
    (hz : logical.registers 8 = 0)
    (hb : BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253 binary logical gap spares) :
    RegisterPath.step Prog254.program logical =
      some { logical with path := [false, true] } ∧
    BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253
      (machine253.runFrom binary (8 * gap + 4 * prefixWidth logical.registers + 110))
      { logical with path := [false, true] } (gap + 1) spares := by
  refine ⟨?_, dispatch_frame_zero000 logical gap spares hp hz hb⟩
  rcases logical with ⟨P, R⟩
  change P = [false, false, false] at hp
  subst P
  exact register_zero000 R hz

/-- The logical endpoint one register instruction after Prefix330. -/
def logical331 : RegisterPath.Configuration :=
  { RegisterPath.decode Prefix330.finiteTarget with path := [false, true] }

private theorem rm_run_add (p : RegisterPath.Program) (i k : Nat)
    (initial : RegisterPath.Configuration) :
    RegisterPath.run p (i + k) initial =
      (RegisterPath.run p i initial).bind (RegisterPath.run p k) := by
  induction i generalizing initial with
  | zero => simp only [Nat.zero_add, RegisterPath.run, Option.bind_some]
  | succ i ih =>
    simp only [Nat.succ_add, RegisterPath.run]
    cases he : RegisterPath.step p initial with
    | none => rfl
    | some next => exact ih next

theorem prefix331 :
    RegisterPath.run Prog254.program 331 Prog254.initial = some logical331 := by
  rw [show 331 = 330 + 1 from rfl, rm_run_add, Prefix330.prefix330]
  change RegisterPath.run Prog254.program 1 (RegisterPath.decode Prefix330.finiteTarget) = _
  have hs := register_zero000 (RegisterPath.decode Prefix330.finiteTarget).registers (by decide)
  change RegisterPath.step Prog254.program (RegisterPath.decode Prefix330.finiteTarget) = _ at hs
  simp only [RegisterPath.run, hs, logical331]

/-- The concrete post-bootstrap frame retains its absolute head and all158
spares. This applies the arbitrary-length theorem, not a new blank run. -/
theorem boot_continuation_zip :
    ZipRep (machine253.run 313429)
      (BootstrapFrame253.dispatchZip BootstrapFrame253.dispatch253 (-17) 10 1
        logical331 38 BootstrapFrame253.spares158) := by
  have hi : ZipRep (machine253.run 312975)
      (zAt (33 : Fin 253) (-17) (true :: (List.replicate 10 false ++ []))
        (false :: false :: false :: (List.replicate (0 + 37) false ++ true ::
          (registerBits (pre 0 2 0 0 0 ++ 0 :: ([5, 0, 0] ++ BootstrapFrame253.spares158)) ++
            [false])))) := by
    simpa only [BootstrapFrame253.dispatchZip, dispatch_state,
      BootstrapFrame253.target_primary_values, Prefix330.prefix330_path,
      registerBits_frame, zAt, pre, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil, List.replicate_succ, List.replicate_zero] using
      BootstrapFrame253.boot_exact_dispatch_zip
  have hs := zero000_core 0 0 2 0 0 0 ([5, 0, 0] ++ BootstrapFrame253.spares158)
    (-17) [] hi
  change ZipRep (machine253.runFrom (machine253.run 312975) 454) _ at hs
  rw [← Machine.run_add_eq_runFrom] at hs
  simpa only [BootstrapFrame253.dispatchZip, dispatch_state,
    logical331, BootstrapFrame253.target_primary_values, registerBits_frame,
    zAt, pre, List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
    List.replicate_succ, List.replicate_zero] using hs

theorem boot_continuation_state :
    (machine253.run 313429).state = some (33 : Fin 253) :=
  by simpa only [BootstrapFrame253.dispatchZip, dispatch_state] using boot_continuation_zip.1

theorem boot_continuation_head : (machine253.run 313429).head = -17 :=
  boot_continuation_zip.2.1

/-- Compose with the already proved bootstrap; no bootstrap is recomputed. -/
theorem boot_continuation_frame :
    BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253 (machine253.run 313429)
      logical331 38 BootstrapFrame253.spares158 := by
  have hs := dispatch_frame_zero000 (RegisterPath.decode Prefix330.finiteTarget)
    37 BootstrapFrame253.spares158 (by decide) (by decide) BootstrapFrame253.boot_dispatch_frame
  change BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253
    (machine253.runFrom (machine253.run 312975) 454) logical331 38
      BootstrapFrame253.spares158 at hs
  rw [← Machine.run_add_eq_runFrom] at hs
  exact hs

/-- The binary and register endpoints have the complete dispatch relation. -/
theorem bootstrap_matches_rm331 :
    RegisterPath.run Prog254.program 331 Prog254.initial = some logical331 ∧
    BootstrapFrame253.DispatchFrame BootstrapFrame253.dispatch253 (machine253.run 313429)
      logical331 38 BootstrapFrame253.spares158 :=
  ⟨prefix331, boot_continuation_frame⟩

end SetTheory.BusyBeaver.ZFC.ZeroSite253
