/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller
-/

/-!
Dyadic interval arithmetic at scale `2^-56`. A mantissa `m` denotes
`m / 2^56`; each operation rounds outward. Real semantics are in `Sound`.
-/

namespace MoserWorm

/-- The global scale exponent. -/
abbrev dfxS : Nat := 56

/-- `2^56`, the denominator of the dyadic scale. -/
abbrev dfxOne : Int := 72057594037927936

/-- A dyadic fixed-point interval: mantissa bounds at scale `2^-56`. -/
structure DIval where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

namespace DIval

/-- Floor of `x / 2^s`. -/
def fshr (x : Int) (s : Nat) : Int := x.fdiv (2 ^ s)

/-- Ceiling of `x / 2^s`. -/
def cshr (x : Int) (s : Nat) : Int := -(fshr (-x) s)

/-- Point interval. -/
def pt (m : Int) : DIval := ⟨m, m⟩

/-- The exact dyadic embedding of an integer. -/
def ofInt (k : Int) : DIval := pt (k * dfxOne)

def add (a b : DIval) : DIval := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : DIval) : DIval := ⟨a.lo - b.hi, a.hi - b.lo⟩
def neg (a : DIval) : DIval := ⟨-a.hi, -a.lo⟩
def min (a b : DIval) : DIval := ⟨Min.min a.lo b.lo, Min.min a.hi b.hi⟩
def max (a b : DIval) : DIval := ⟨Max.max a.lo b.lo, Max.max a.hi b.hi⟩

def abs (a : DIval) : DIval :=
  if 0 ≤ a.lo then a
  else if a.hi ≤ 0 then neg a
  else ⟨0, Max.max (-a.lo) a.hi⟩

/-- Union hull. -/
def hull (a b : DIval) : DIval := ⟨Min.min a.lo b.lo, Max.max a.hi b.hi⟩

/-- Outward-rounded halving. -/
def half (a : DIval) : DIval := ⟨fshr a.lo 1, cshr a.hi 1⟩

/-- `max(·, 0)` componentwise. -/
def pos (a : DIval) : DIval := ⟨Max.max a.lo 0, Max.max a.hi 0⟩

/-- Outward-rounded product from the four endpoint products. -/
def mul (a b : DIval) : DIval :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  let mn := Min.min (Min.min p1 p2) (Min.min p3 p4)
  let mx := Max.max (Max.max p1 p2) (Max.max p3 p4)
  ⟨mn.fdiv dfxOne, -((-mx).fdiv dfxOne)⟩

/-- Outward-rounded square, tighter than `mul a a`. -/
def sq (a : DIval) : DIval :=
  let t := a.abs
  ⟨(t.lo * t.lo).fdiv dfxOne, -((-(t.hi * t.hi)).fdiv dfxOne)⟩

/-- Floor square root of a natural number: `Nat.sqrt` is exactly that. -/
def isqrt (n : Nat) : Nat := Nat.sqrt n

/-- Outward-rounded square root, clamping negative inputs to zero. -/
def sqrtI (a : DIval) : DIval :=
  let lo := (Max.max a.lo 0).toNat
  let hi := (Max.max a.hi 0).toNat
  let rl := isqrt (lo <<< dfxS)
  let rh := isqrt (hi <<< dfxS)
  let hi2 : Int := if rh * rh = hi <<< dfxS then rh else rh + 1
  ⟨rl, hi2⟩

/-- Euclidean norm `sqrt (x² + y²)`. -/
def norm2 (x y : DIval) : DIval := sqrtI (add (sq x) (sq y))

/-! ### π and trigonometry -/

/-- `⌊π · 2^56⌋`. -/
def piLo : Int := 226375608064910088
/-- `⌊(π/2) · 2^56⌋`. -/
def pi2Lo : Int := 113187804032455044
/-- `⌊(π/4) · 2^56⌋`. -/
def pi4Lo : Int := 56593902016227522

def piI : DIval := ⟨piLo, piLo + 1⟩
def piHalfI : DIval := ⟨pi2Lo, pi2Lo + 1⟩

/-- Clamp into `[-1, 1]` (sound for sin/cos outputs). -/
def clamp1 (a : DIval) : DIval := ⟨Max.max a.lo (-dfxOne), Min.min a.hi dfxOne⟩

/-- `⌊2^56/k!⌋` for `k = 3,5,…,17` (sin series). -/
def sinCoeffs : List Int :=
  [12009599006321322, 600479950316066, 14297141674192, 198571412141,
   1805194655, 11571760, 55103, 202]

/-- `⌊2^56/k!⌋` for `k = 2,4,…,18` (cos series). -/
def cosCoeffs : List Int :=
  [36028797018963968, 3002399751580330, 100079991719344, 1787142709274,
   19857141214, 150432887, 826554, 3443, 11]

/-- Alternating Horner fold shared by the two series:
`acc = c₀ - x²·(c₁ - x²·(… - x²·c_last))`, coefficients enclosed as
`[c, c+1]`. -/
def hornerAlt (x2 : DIval) : List Int → DIval
  | [] => pt 0
  | [c] => ⟨c, c + 1⟩
  | c :: rest => sub ⟨c, c + 1⟩ (mul x2 (hornerAlt x2 rest))

/-- Sine enclosure on mantissa range `±(pi4Lo + 64)`; the degree-17
Taylor remainder is bounded by one unit in the last place. -/
def sinCore (x : DIval) : DIval :=
  let x2 := sq x
  let acc := hornerAlt x2 sinCoeffs
  let s := mul x (sub (ofInt 1) (mul x2 acc))
  ⟨s.lo - 1, s.hi + 1⟩

/-- Cosine enclosure on mantissa range `±(pi4Lo + 64)`; the degree-18
Taylor remainder is bounded by one unit in the last place. -/
def cosCore (x : DIval) : DIval :=
  let x2 := sq x
  let acc := hornerAlt x2 cosCoeffs
  let c := sub (ofInt 1) (mul x2 acc)
  ⟨c.lo - 1, c.hi + 1⟩

/-- Residual `t - k·(π/2)` with π/2 enclosed. -/
def kpi2Residual (t k : Int) : DIval :=
  sub (pt t) (mul (ofInt k) ⟨pi2Lo, pi2Lo + 1⟩)

/-- Adjust the quadrant estimate within the given recursion fuel. -/
def adjustK (t : Int) : Nat → Int → Int
  | 0, k => k
  | fuel + 1, k =>
    let x := kpi2Residual t k
    -- Slack for the π/2 enclosure error on angles in [-64, 64].
    if x.hi > pi4Lo + 64 then adjustK t fuel (k + 1)
    else if x.lo < -(pi4Lo + 64) then adjustK t fuel (k - 1)
    else k

/-- Sine and cosine of a dyadic angle with `|t| ≤ 64 * dfxOne`. -/
def sincos (t : Int) : DIval × DIval :=
  let num := t + pi4Lo
  let k0 := num.fdiv pi2Lo
  let k := adjustK t 8 k0
  let x := kpi2Residual t k
  let sc := sinCore x
  let cc := cosCore x
  let r :=
    match (k % 4).toNat with
    | 0 => (sc, cc)
    | 1 => (cc, neg sc)
    | 2 => (neg sc, neg cc)
    | _ => (neg cc, sc)
  (clamp1 r.1, clamp1 r.2)

/-- Sine and cosine on an interval in `[-64, 64]`, using midpoint
evaluation and the Lipschitz bound. -/
def sincosIv (t : DIval) : DIval × DIval :=
  let m := t.lo + (t.hi - t.lo) / 2
  let rad := Max.max (t.hi - m) (m - t.lo)
  let (sm, cm) := sincos m
  (clamp1 ⟨sm.lo - rad, sm.hi + rad⟩, clamp1 ⟨cm.lo - rad, cm.hi + rad⟩)

end DIval

end MoserWorm
