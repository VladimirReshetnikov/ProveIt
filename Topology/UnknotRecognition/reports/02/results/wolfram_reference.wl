(* Reference data retrieved through the Wolfram connector during this work.
   BraidWord uses {generator, exponent} pairs, not the package's expanded list.
   This is a data check, not an independent general unknot recognizer. *)
ExportString[
  Table[
    <|"name" -> ToString[k, InputForm],
      "braid_word" -> KnotData[k, "BraidWord"],
      "determinant" -> KnotData[k, "Determinant"]|>,
    {k, {{3, 1}, {4, 1}, {5, 2}, {6, 1}, {8, 19}, {10, 124}}}
  ],
  "RawJSON"
]
