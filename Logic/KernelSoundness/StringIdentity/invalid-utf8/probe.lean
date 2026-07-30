def sur : String := "í €"
#eval sur.utf8ByteSize          -- 3: the string is now EF BF BD
#eval sur.length                -- 1
#eval sur.toList.map (fun c => c.toNat)   -- [65533] = U+FFFD
