(* Evaluate this file using Get or wolframscript -file. *)
Module[{base = DirectoryName[$InputFileName], result},
  Get[FileNameJoin[{base, "RationalHahn.wl"}]];
  result = Get[FileNameJoin[{base, "Checks.wl"}]];
  Print[result];
  result
]
