open Codec.ConcretePrefixCredit

let fields = function
| Drop -> [0]
| Nip -> [1]
| Mp x -> [2; x]
| Ax (c, x, y) -> [c + 3; y; x]

let int_list xs =
  "[" ^ String.concat "," (List.map string_of_int xs) ^ "]"

let () =
  let count = int_of_string Sys.argv.(1) in
  for n = 0 to count - 1 do
    let w = word n in
    Printf.printf "[%d,%d,[%s]]\n" n (raw w)
      (String.concat "," (List.map (fun k -> int_list (fields k)) w))
  done
