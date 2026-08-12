import PolynomialFormulas.ComputableDummitCoefficientsCore

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

def table0Block0 : SparsePolynomial := [
  ⟨16, ⟨8, 0, 2, 0, 2⟩⟩,
  ⟨-8, ⟨8, 0, 1, 2, 1⟩⟩,
  ⟨1, ⟨8, 0, 0, 4, 0⟩⟩,
  ⟨-8, ⟨7, 2, 1, 0, 2⟩⟩
]

def table0Block1 : SparsePolynomial := [
  ⟨2, ⟨7, 2, 0, 2, 1⟩⟩,
  ⟨-48, ⟨7, 0, 1, 1, 2⟩⟩,
  ⟨12, ⟨7, 0, 0, 3, 1⟩⟩,
  ⟨1, ⟨6, 4, 0, 0, 2⟩⟩
]

def table0Block2 : SparsePolynomial := [
  ⟨12, ⟨6, 2, 0, 1, 2⟩⟩,
  ⟨-144, ⟨6, 1, 2, 0, 2⟩⟩,
  ⟨88, ⟨6, 1, 1, 2, 1⟩⟩,
  ⟨-13, ⟨6, 1, 0, 4, 0⟩⟩
]

def table0Block3 : SparsePolynomial := [
  ⟨56, ⟨6, 0, 1, 0, 3⟩⟩,
  ⟨86, ⟨6, 0, 0, 2, 2⟩⟩,
  ⟨72, ⟨5, 3, 1, 0, 2⟩⟩,
  ⟨-22, ⟨5, 3, 0, 2, 1⟩⟩
]

def table0Block4 : SparsePolynomial := [
  ⟨-4, ⟨5, 2, 2, 1, 1⟩⟩,
  ⟨1, ⟨5, 2, 1, 3, 0⟩⟩,
  ⟨-14, ⟨5, 2, 0, 0, 3⟩⟩,
  ⟨304, ⟨5, 1, 1, 1, 2⟩⟩
]

def table0Block5 : SparsePolynomial := [
  ⟨-148, ⟨5, 1, 0, 3, 1⟩⟩,
  ⟨152, ⟨5, 0, 3, 0, 2⟩⟩,
  ⟨-54, ⟨5, 0, 2, 2, 1⟩⟩,
  ⟨5, ⟨5, 0, 1, 4, 0⟩⟩
]

def table0Block6 : SparsePolynomial := [
  ⟨-468, ⟨5, 0, 0, 1, 3⟩⟩,
  ⟨-9, ⟨4, 5, 0, 0, 2⟩⟩,
  ⟨1, ⟨4, 4, 1, 1, 1⟩⟩,
  ⟨-76, ⟨4, 3, 0, 1, 2⟩⟩
]

def table0Block7 : SparsePolynomial := [
  ⟨370, ⟨4, 2, 2, 0, 2⟩⟩,
  ⟨-287, ⟨4, 2, 1, 2, 1⟩⟩,
  ⟨65, ⟨4, 2, 0, 4, 0⟩⟩,
  ⟨-28, ⟨4, 1, 3, 1, 1⟩⟩
]

def table0Block8 : SparsePolynomial := [
  ⟨5, ⟨4, 1, 2, 3, 0⟩⟩,
  ⟨-200, ⟨4, 1, 1, 0, 3⟩⟩,
  ⟨-294, ⟨4, 1, 0, 2, 2⟩⟩,
  ⟨8, ⟨4, 0, 5, 0, 1⟩⟩
]

def table0Block9 : SparsePolynomial := [
  ⟨-2, ⟨4, 0, 4, 2, 0⟩⟩,
  ⟨-676, ⟨4, 0, 2, 1, 2⟩⟩,
  ⟨180, ⟨4, 0, 1, 3, 1⟩⟩,
  ⟨17, ⟨4, 0, 0, 5, 0⟩⟩
]

def table0Block10 : SparsePolynomial := [
  ⟨625, ⟨4, 0, 0, 0, 4⟩⟩,
  ⟨-210, ⟨3, 4, 1, 0, 2⟩⟩,
  ⟨76, ⟨3, 4, 0, 2, 1⟩⟩,
  ⟨43, ⟨3, 3, 2, 1, 1⟩⟩
]

def table0Block11 : SparsePolynomial := [
  ⟨-15, ⟨3, 3, 1, 3, 0⟩⟩,
  ⟨50, ⟨3, 3, 0, 0, 3⟩⟩,
  ⟨-6, ⟨3, 2, 4, 0, 1⟩⟩,
  ⟨2, ⟨3, 2, 3, 2, 0⟩⟩
]

def table0Block12 : SparsePolynomial := [
  ⟨-397, ⟨3, 2, 1, 1, 2⟩⟩,
  ⟨514, ⟨3, 2, 0, 3, 1⟩⟩,
  ⟨-700, ⟨3, 1, 3, 0, 2⟩⟩,
  ⟨447, ⟨3, 1, 2, 2, 1⟩⟩
]

def table0Block13 : SparsePolynomial := [
  ⟨-118, ⟨3, 1, 1, 4, 0⟩⟩,
  ⟨2300, ⟨3, 1, 0, 1, 3⟩⟩,
  ⟨-12, ⟨3, 0, 4, 1, 1⟩⟩,
  ⟨6, ⟨3, 0, 3, 3, 0⟩⟩
]

def table0Block14 : SparsePolynomial := [
  ⟨250, ⟨3, 0, 2, 0, 3⟩⟩,
  ⟨1470, ⟨3, 0, 1, 2, 2⟩⟩,
  ⟨-276, ⟨3, 0, 0, 4, 1⟩⟩,
  ⟨27, ⟨2, 6, 0, 0, 2⟩⟩
]

def table0Block15 : SparsePolynomial := [
  ⟨-9, ⟨2, 5, 1, 1, 1⟩⟩,
  ⟨1, ⟨2, 5, 0, 3, 0⟩⟩,
  ⟨1, ⟨2, 4, 3, 0, 1⟩⟩,
  ⟨141, ⟨2, 4, 0, 1, 2⟩⟩
]

def table0Block16 : SparsePolynomial := [
  ⟨-185, ⟨2, 3, 2, 0, 2⟩⟩,
  ⟨168, ⟨2, 3, 1, 2, 1⟩⟩,
  ⟨-128, ⟨2, 3, 0, 4, 0⟩⟩,
  ⟨93, ⟨2, 2, 3, 1, 1⟩⟩
]

def table0Block17 : SparsePolynomial := [
  ⟨19, ⟨2, 2, 2, 3, 0⟩⟩,
  ⟨-125, ⟨2, 2, 1, 0, 3⟩⟩,
  ⟨-610, ⟨2, 2, 0, 2, 2⟩⟩,
  ⟨-36, ⟨2, 1, 5, 0, 1⟩⟩
]

def table0Block18 : SparsePolynomial := [
  ⟨5, ⟨2, 1, 4, 2, 0⟩⟩,
  ⟨1995, ⟨2, 1, 2, 1, 2⟩⟩,
  ⟨-1174, ⟨2, 1, 1, 3, 1⟩⟩,
  ⟨-16, ⟨2, 1, 0, 5, 0⟩⟩
]

def table0Block19 : SparsePolynomial := [
  ⟨-3125, ⟨2, 1, 0, 0, 4⟩⟩,
  ⟨375, ⟨2, 0, 4, 0, 2⟩⟩,
  ⟨-172, ⟨2, 0, 3, 2, 1⟩⟩,
  ⟨82, ⟨2, 0, 2, 4, 0⟩⟩
]

def table0Block20 : SparsePolynomial := [
  ⟨-3500, ⟨2, 0, 1, 1, 3⟩⟩,
  ⟨-1450, ⟨2, 0, 0, 3, 2⟩⟩,
  ⟨198, ⟨1, 5, 1, 0, 2⟩⟩,
  ⟨-78, ⟨1, 5, 0, 2, 1⟩⟩
]

def table0Block21 : SparsePolynomial := [
  ⟨-95, ⟨1, 4, 2, 1, 1⟩⟩,
  ⟨44, ⟨1, 4, 1, 3, 0⟩⟩,
  ⟨25, ⟨1, 3, 4, 0, 1⟩⟩,
  ⟨-15, ⟨1, 3, 3, 2, 0⟩⟩
]

def table0Block22 : SparsePolynomial := [
  ⟨15, ⟨1, 3, 1, 1, 2⟩⟩,
  ⟨-384, ⟨1, 3, 0, 3, 1⟩⟩,
  ⟨1, ⟨1, 2, 5, 1, 0⟩⟩,
  ⟨525, ⟨1, 2, 3, 0, 2⟩⟩
]

def table0Block23 : SparsePolynomial := [
  ⟨-528, ⟨1, 2, 2, 2, 1⟩⟩,
  ⟨384, ⟨1, 2, 1, 4, 0⟩⟩,
  ⟨-1750, ⟨1, 2, 0, 1, 3⟩⟩,
  ⟨-29, ⟨1, 1, 4, 1, 1⟩⟩
]

def table0Block24 : SparsePolynomial := [
  ⟨-118, ⟨1, 1, 3, 3, 0⟩⟩,
  ⟨625, ⟨1, 1, 2, 0, 3⟩⟩,
  ⟨-850, ⟨1, 1, 1, 2, 2⟩⟩,
  ⟨1760, ⟨1, 1, 0, 4, 1⟩⟩
]

def table0Block25 : SparsePolynomial := [
  ⟨38, ⟨1, 0, 6, 0, 1⟩⟩,
  ⟨5, ⟨1, 0, 5, 2, 0⟩⟩,
  ⟨-2050, ⟨1, 0, 3, 1, 2⟩⟩,
  ⟨780, ⟨1, 0, 2, 3, 1⟩⟩
]

def table0Block26 : SparsePolynomial := [
  ⟨-192, ⟨1, 0, 1, 5, 0⟩⟩,
  ⟨3125, ⟨1, 0, 1, 0, 4⟩⟩,
  ⟨7500, ⟨1, 0, 0, 2, 3⟩⟩,
  ⟨-27, ⟨0, 7, 0, 0, 2⟩⟩
]

def table0Block27 : SparsePolynomial := [
  ⟨18, ⟨0, 6, 1, 1, 1⟩⟩,
  ⟨-4, ⟨0, 6, 0, 3, 0⟩⟩,
  ⟨-4, ⟨0, 5, 3, 0, 1⟩⟩,
  ⟨1, ⟨0, 5, 2, 2, 0⟩⟩
]

def table0Block28 : SparsePolynomial := [
  ⟨-99, ⟨0, 5, 0, 1, 2⟩⟩,
  ⟨-150, ⟨0, 4, 2, 0, 2⟩⟩,
  ⟨196, ⟨0, 4, 1, 2, 1⟩⟩,
  ⟨48, ⟨0, 4, 0, 4, 0⟩⟩
]

def table0Block29 : SparsePolynomial := [
  ⟨12, ⟨0, 3, 3, 1, 1⟩⟩,
  ⟨-128, ⟨0, 3, 2, 3, 0⟩⟩,
  ⟨1200, ⟨0, 3, 0, 2, 2⟩⟩,
  ⟨-12, ⟨0, 2, 5, 0, 1⟩⟩
]

def table0Block30 : SparsePolynomial := [
  ⟨65, ⟨0, 2, 4, 2, 0⟩⟩,
  ⟨-725, ⟨0, 2, 2, 1, 2⟩⟩,
  ⟨-160, ⟨0, 2, 1, 3, 1⟩⟩,
  ⟨-192, ⟨0, 2, 0, 5, 0⟩⟩
]

def table0Block31 : SparsePolynomial := [
  ⟨3125, ⟨0, 2, 0, 0, 4⟩⟩,
  ⟨-13, ⟨0, 1, 6, 1, 0⟩⟩,
  ⟨-125, ⟨0, 1, 4, 0, 2⟩⟩,
  ⟨590, ⟨0, 1, 3, 2, 1⟩⟩
]

def table0Block32 : SparsePolynomial := [
  ⟨-16, ⟨0, 1, 2, 4, 0⟩⟩,
  ⟨-1250, ⟨0, 1, 1, 1, 3⟩⟩,
  ⟨-2000, ⟨0, 1, 0, 3, 2⟩⟩,
  ⟨1, ⟨0, 0, 8, 0, 0⟩⟩
]

def table0Block33 : SparsePolynomial := [
  ⟨-124, ⟨0, 0, 5, 1, 1⟩⟩,
  ⟨17, ⟨0, 0, 4, 3, 0⟩⟩,
  ⟨3250, ⟨0, 0, 2, 2, 2⟩⟩,
  ⟨-1600, ⟨0, 0, 1, 4, 1⟩⟩
]

def table0Block34 : SparsePolynomial := [
  ⟨256, ⟨0, 0, 0, 6, 0⟩⟩,
  ⟨-9375, ⟨0, 0, 0, 1, 4⟩⟩
]

def table0Tail35 : SparsePolynomial := []

def table0Tail34 : SparsePolynomial :=
  table0Block34 ++ table0Tail35

def table0Tail33 : SparsePolynomial :=
  table0Block33 ++ table0Tail34

def table0Tail32 : SparsePolynomial :=
  table0Block32 ++ table0Tail33

def table0Tail31 : SparsePolynomial :=
  table0Block31 ++ table0Tail32

def table0Tail30 : SparsePolynomial :=
  table0Block30 ++ table0Tail31

def table0Tail29 : SparsePolynomial :=
  table0Block29 ++ table0Tail30

def table0Tail28 : SparsePolynomial :=
  table0Block28 ++ table0Tail29

def table0Tail27 : SparsePolynomial :=
  table0Block27 ++ table0Tail28

def table0Tail26 : SparsePolynomial :=
  table0Block26 ++ table0Tail27

def table0Tail25 : SparsePolynomial :=
  table0Block25 ++ table0Tail26

def table0Tail24 : SparsePolynomial :=
  table0Block24 ++ table0Tail25

def table0Tail23 : SparsePolynomial :=
  table0Block23 ++ table0Tail24

def table0Tail22 : SparsePolynomial :=
  table0Block22 ++ table0Tail23

def table0Tail21 : SparsePolynomial :=
  table0Block21 ++ table0Tail22

def table0Tail20 : SparsePolynomial :=
  table0Block20 ++ table0Tail21

def table0Tail19 : SparsePolynomial :=
  table0Block19 ++ table0Tail20

def table0Tail18 : SparsePolynomial :=
  table0Block18 ++ table0Tail19

def table0Tail17 : SparsePolynomial :=
  table0Block17 ++ table0Tail18

def table0Tail16 : SparsePolynomial :=
  table0Block16 ++ table0Tail17

def table0Tail15 : SparsePolynomial :=
  table0Block15 ++ table0Tail16

def table0Tail14 : SparsePolynomial :=
  table0Block14 ++ table0Tail15

def table0Tail13 : SparsePolynomial :=
  table0Block13 ++ table0Tail14

def table0Tail12 : SparsePolynomial :=
  table0Block12 ++ table0Tail13

def table0Tail11 : SparsePolynomial :=
  table0Block11 ++ table0Tail12

def table0Tail10 : SparsePolynomial :=
  table0Block10 ++ table0Tail11

def table0Tail9 : SparsePolynomial :=
  table0Block9 ++ table0Tail10

def table0Tail8 : SparsePolynomial :=
  table0Block8 ++ table0Tail9

def table0Tail7 : SparsePolynomial :=
  table0Block7 ++ table0Tail8

def table0Tail6 : SparsePolynomial :=
  table0Block6 ++ table0Tail7

def table0Tail5 : SparsePolynomial :=
  table0Block5 ++ table0Tail6

def table0Tail4 : SparsePolynomial :=
  table0Block4 ++ table0Tail5

def table0Tail3 : SparsePolynomial :=
  table0Block3 ++ table0Tail4

def table0Tail2 : SparsePolynomial :=
  table0Block2 ++ table0Tail3

def table0Tail1 : SparsePolynomial :=
  table0Block1 ++ table0Tail2

def table0Tail0 : SparsePolynomial :=
  table0Block0 ++ table0Tail1

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
