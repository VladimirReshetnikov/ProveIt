import PA194FoldedRuntimeRows

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194FoldedCache
open PA194FoldedRuntimeRows PA194LocalQuotient

abbrev Transition := Option (Bool × Bool × Nat)

/-- The balanced lookup used to evaluate the finite certificates. -/
inductive Tree where
  | empty
  | node (state : Nat) (zero one : Transition) (left right : Tree)

def Tree.keys : Tree → List Nat
  | .empty => []
  | .node q _ _ left right => q :: (left.keys ++ right.keys)

def Tree.read : Tree → Nat → Bool → Transition
  | .empty, _, _ => none
  | .node q zero one left right, p, b =>
    if p < q then left.read p b
    else if q < p then right.read p b
    else if b then one else zero

theorem Tree.outside (t : Tree) (q : Nat) (b : Bool) (h : q ∉ t.keys) :
    t.read q b = none := by
  induction t with
  | empty => rfl
  | node p zero one left right ihl ihr =>
    simp only [Tree.keys,List.mem_cons,List.mem_append,not_or] at h
    simp only [Tree.read]
    split
    · exact ihl h.2.1
    · split
      · exact ihr h.2.2
      · exact False.elim (h.1 (by omega))

def table : Tree :=
  (.node 110 (some (false,true,127)) (some (true,true,8))
    (.node 51 (some (false,true,16)) (some (true,true,51))
      (.node 25 (some (false,true,36)) (some (true,true,25))
        (.node 13 (some (false,false,91)) (some (true,false,31))
          (.node 6 (some (false,true,6)) (some (false,true,10))
            (.node 3 (some (false,false,5)) (some (true,false,2))
              (.node 1 (some (false,false,1)) (some (true,false,2))
                (.node 0 (some (true,true,94)) (some (true,true,0)) .empty .empty)
                (.node 2 (some (false,false,3)) (some (true,false,2)) .empty .empty))
              (.node 5 (some (false,false,9)) (some (true,false,2))
                (.node 4 (some (true,true,6)) (some (false,false,4)) .empty .empty)
                .empty))
            (.node 10 (some (false,false,16)) (some (false,true,10))
              (.node 9 (some (false,false,15)) (some (true,false,2))
                (.node 8 (some (false,true,14)) (some (true,true,13)) .empty .empty)
                .empty)
              (.node 12 (some (false,true,19)) (some (true,true,20))
                (.node 11 (some (false,false,26)) (some (true,true,18)) .empty .empty)
                .empty)))
          (.node 19 (some (false,true,28)) (some (true,true,29))
            (.node 16 (some (true,false,1)) (some (false,false,1))
              (.node 15 (some (false,false,23)) (some (true,false,2))
                (.node 14 (some (false,false,11)) (some (false,true,22)) .empty .empty)
                .empty)
              (.node 18 (some (false,true,96)) (some (false,false,108))
                (.node 17 (some (false,true,24)) (some (false,true,32)) .empty .empty)
                .empty))
            (.node 22 (some (false,true,33)) (some (true,true,22))
              (.node 21 (some (false,true,24)) (some (false,true,60))
                (.node 20 (some (false,true,30)) (some (true,true,31)) .empty .empty)
                .empty)
              (.node 24 (some (false,false,35)) (some (false,true,0))
                (.node 23 (some (false,false,34)) (some (true,false,2)) .empty .empty)
                .empty))))
        (.node 38 (some (false,true,28)) (some (true,true,20))
          (.node 31 (some (false,true,21)) (some (true,true,47))
            (.node 28 (some (false,true,41)) (some (true,true,42))
              (.node 27 (some (false,true,39)) (some (false,false,40))
                (.node 26 (some (false,true,194)) (some (true,true,42)) .empty .empty)
                .empty)
              (.node 30 (some (false,true,45)) (some (true,true,46))
                (.node 29 (some (false,true,43)) (some (true,true,44)) .empty .empty)
                .empty))
            (.node 34 (some (false,false,75)) (some (true,false,2))
              (.node 33 (some (false,true,32)) (some (true,true,33))
                (.node 32 (some (false,true,48)) (some (true,true,32)) .empty .empty)
                .empty)
              (.node 36 (some (false,true,51)) (some (true,true,36))
                (.node 35 (some (true,true,35)) (some (true,false,1)) .empty .empty)
                .empty)))
          (.node 44 (some (false,true,58)) (some (true,true,59))
            (.node 41 (some (false,true,24)) (some (false,true,25))
              (.node 40 (some (false,false,4)) (some (true,false,54))
                (.node 39 (some (false,false,11)) (some (false,true,36)) .empty .empty)
                .empty)
              (.node 43 (some (false,true,56)) (some (true,true,57))
                (.node 42 (some (false,true,13)) (some (false,false,16)) .empty .empty)
                .empty))
            (.node 47 (some (false,true,63)) (some (false,false,16))
              (.node 46 (some (false,true,61)) (some (true,true,62))
                (.node 45 (some (false,true,24)) (some (false,true,55)) .empty .empty)
                .empty)
              (.node 49 (some (false,false,35)) (some (false,true,64))
                (.node 48 (some (false,true,25)) (some (true,true,48)) .empty .empty)
                .empty)))))
      (.node 82 (some (false,true,49)) (some (false,true,33))
        (.node 66 (some (true,true,198)) (some (true,false,54))
          (.node 59 (some (false,true,62)) (some (true,true,72))
            (.node 56 (some (false,false,11)) (some (false,true,51))
              (.node 54 (some (false,false,40)) (some (true,false,54))
                (.node 53 (some (false,true,68)) (some (true,true,69)) .empty .empty)
                (.node 55 (some (false,true,22)) (some (true,true,55)) .empty .empty))
              (.node 58 (some (false,true,70)) (some (true,true,71))
                (.node 57 (some (false,true,61)) (some (false,false,16)) .empty .empty)
                .empty))
            (.node 62 (some (false,false,28)) (some (true,false,73))
              (.node 61 (some (false,true,49)) (some (false,true,25))
                (.node 60 (some (false,true,55)) (some (true,true,60)) .empty .empty)
                .empty)
              (.node 64 (some (false,true,74)) (some (true,true,64))
                (.node 63 (some (false,false,123)) (some (true,false,30)) .empty .empty)
                .empty)))
          (.node 73 (some (false,true,82)) (some (true,true,83))
            (.node 70 (some (false,true,41)) (some (true,true,63))
              (.node 69 (some (false,false,213)) (some (true,true,31))
                (.node 68 (some (false,true,77)) (some (true,true,254)) .empty .empty)
                .empty)
              (.node 72 (some (false,true,56)) (some (true,false,81))
                (.node 71 (some (false,false,91)) (some (true,true,80)) .empty .empty)
                .empty))
            (.node 77 (some (false,true,87)) (some (true,true,88))
              (.node 75 (some (false,true,75)) (some (true,true,84))
                (.node 74 (some (true,true,0)) (some (true,true,64)) .empty .empty)
                .empty)
              (.node 81 (some (false,false,111)) (some (true,true,57))
                (.node 80 (some (false,true,91)) (some (true,false,138)) .empty .empty)
                .empty))))
        (.node 97 (some (true,false,113)) (some (true,false,97))
          (.node 91 (some (false,true,82)) (some (true,true,81))
            (.node 87 (some (false,true,301)) (some (true,true,21))
              (.node 84 (some (false,true,53)) (some (true,true,310))
                (.node 83 (some (false,true,93)) (some (false,false,42)) .empty .empty)
                .empty)
              (.node 90 (some (false,true,105)) (some (true,true,106))
                (.node 88 (some (false,true,122)) (some (true,true,103)) .empty .empty)
                .empty))
            (.node 94 (some (false,true,66)) (some (false,true,0))
              (.node 93 (some (false,true,108)) (some (true,true,109))
                (.node 92 (some (false,true,104)) (some (true,true,185)) .empty .empty)
                .empty)
              (.node 96 (some (false,true,101)) (some (true,true,100))
                (.node 95 (some (false,true,27)) (some (true,true,110)) .empty .empty)
                .empty)))
          (.node 104 (some (false,true,123)) (some (true,true,124))
            (.node 100 (some (false,true,174)) (some (true,true,164))
              (.node 99 (some (false,true,61)) (some (true,true,61))
                (.node 98 (some (false,true,19)) (some (true,true,114)) .empty .empty)
                .empty)
              (.node 103 (some (false,true,108)) (some (false,false,302))
                (.node 101 (some (false,false,26)) (some (true,true,2000)) .empty .empty)
                .empty))
            (.node 107 (some (false,true,21)) (some (true,true,126))
              (.node 106 (some (false,true,58)) (some (true,true,125))
                (.node 105 (some (false,true,72)) (some (true,true,59)) .empty .empty)
                .empty)
              (.node 109 (some (false,true,62)) (some (true,true,42))
                (.node 108 (some (false,true,21)) (some (false,false,10)) .empty .empty)
                .empty))))))
    (.node 2011 (some (false,true,213)) (some (true,true,2012))
      (.node 194 (some (false,true,17)) (some (true,false,137))
        (.node 138 (some (false,true,39)) (some (true,false,130))
          (.node 125 (some (false,true,62)) (some (true,true,139))
            (.node 122 (some (false,false,137)) (some (false,false,1))
              (.node 113 (some (false,false,302)) (some (false,false,97))
                (.node 111 (some (false,true,104)) (some (true,true,128)) .empty .empty)
                (.node 114 (some (false,true,130)) (some (true,true,107)) .empty .empty))
              (.node 124 (some (false,true,62)) (some (true,true,138))
                (.node 123 (some (false,true,39)) (some (true,true,73)) .empty .empty)
                .empty))
            (.node 128 (some (false,true,21)) (some (true,true,141))
              (.node 127 (some (false,true,14)) (some (true,true,138))
                (.node 126 (some (false,true,71)) (some (false,false,16)) .empty .empty)
                .empty)
              (.node 137 (some (false,true,30)) (some (true,true,70))
                (.node 130 (some (false,true,144)) (some (true,false,20)) .empty .empty)
                .empty)))
          (.node 166 (some (false,true,19)) (some (true,true,179))
            (.node 144 (some (false,true,24)) (some (false,true,48))
              (.node 141 (some (false,true,161)) (some (false,false,16))
                (.node 139 (some (false,true,190)) (some (false,false,16)) .empty .empty)
                .empty)
              (.node 164 (some (false,true,77)) (some (true,true,98))
                (.node 161 (some (false,true,49)) (some (false,true,32)) .empty .empty)
                .empty))
            (.node 185 (some (false,true,107)) (some (true,true,98))
              (.node 179 (some (false,true,194)) (some (true,true,128))
                (.node 174 (some (false,true,213)) (some (true,true,28)) .empty .empty)
                .empty)
              (.node 190 (some (false,true,99)) (some (true,true,99))
                (.node 188 (some (false,true,95)) (some (true,true,111)) .empty .empty)
                .empty))))
        (.node 312 (some (false,true,11)) (some (true,true,38))
          (.node 217 (some (false,true,197)) (some (true,true,196))
            (.node 198 (some (true,false,40)) (some (true,false,113))
              (.node 197 (some (false,true,109)) (some (true,true,130))
                (.node 196 (some (false,true,77)) (some (true,true,122)) .empty .empty)
                .empty)
              (.node 214 (some (false,true,188)) (some (true,true,312))
                (.node 213 (some (false,true,92)) (some (true,true,90)) .empty .empty)
                .empty))
            (.node 301 (some (false,true,45)) (some (true,true,103))
              (.node 254 (none) (none)
                (.node 221 (some (false,true,196)) (some (true,true,217)) .empty .empty)
                .empty)
              (.node 310 (some (false,true,214)) (some (true,true,62))
                (.node 302 (some (false,false,4)) (some (false,false,302)) .empty .empty)
                .empty)))
          (.node 2005 (some (false,true,2006)) (some (true,true,2023))
            (.node 2002 (some (false,true,12)) (some (true,true,2003))
              (.node 2001 (some (false,true,2002)) (some (true,true,2005))
                (.node 2000 (some (false,true,2001)) (some (true,true,2033)) .empty .empty)
                .empty)
              (.node 2004 (some (false,true,98)) (some (true,true,90))
                (.node 2003 (some (false,true,2004)) (some (true,true,99)) .empty .empty)
                .empty))
            (.node 2008 (some (false,true,2009)) (some (true,true,2019))
              (.node 2007 (some (false,true,69)) (some (true,true,2008))
                (.node 2006 (some (false,true,2007)) (some (true,true,2014)) .empty .empty)
                .empty)
              (.node 2010 (some (false,true,12)) (some (true,true,2004))
                (.node 2009 (some (false,true,2010)) (some (true,true,2011)) .empty .empty)
                .empty)))))
      (.node 2041 (some (false,true,2042)) (some (true,true,2047))
        (.node 2028 (some (false,true,2003)) (some (true,true,2002))
          (.node 2020 (some (false,true,2021)) (some (true,true,2003))
            (.node 2015 (some (false,false,2044)) (some (true,true,2017))
              (.node 2013 (some (false,true,98)) (some (true,true,2014))
                (.node 2012 (some (false,true,2013)) (some (true,true,2015)) .empty .empty)
                (.node 2014 (some (false,false,2050)) (some (true,false,2064)) .empty .empty))
              (.node 2019 (some (false,false,2059)) (some (true,false,2056))
                (.node 2017 (some (false,true,2027)) (some (true,true,2002)) .empty .empty)
                .empty))
            (.node 2025 (some (false,true,12)) (some (true,true,2026))
              (.node 2023 (some (false,true,2046)) (some (true,true,2029))
                (.node 2021 (some (false,true,2032)) (some (true,true,90)) .empty .empty)
                .empty)
              (.node 2027 (some (false,true,90)) (some (true,false,2020))
                (.node 2026 (some (false,true,166)) (some (true,true,2027)) .empty .empty)
                .empty)))
          (.node 2034 (some (false,true,2025)) (some (true,true,2035))
            (.node 2031 (some (false,true,12)) (some (true,true,2032))
              (.node 2030 (some (false,true,2026)) (some (true,true,90))
                (.node 2029 (some (false,true,2030)) (some (true,true,2031)) .empty .empty)
                .empty)
              (.node 2033 (some (false,true,2034)) (some (true,true,2039))
                (.node 2032 (some (false,false,2002)) (some (true,true,61)) .empty .empty)
                .empty))
            (.node 2038 (some (false,true,166)) (some (true,true,2032))
              (.node 2036 (some (false,true,2015)) (some (true,true,61))
                (.node 2035 (some (false,true,61)) (some (true,true,2036)) .empty .empty)
                .empty)
              (.node 2040 (some (false,true,2041)) (some (true,true,2066))
                (.node 2039 (some (false,true,2052)) (some (true,true,2040)) .empty .empty)
                .empty))))
        (.node 2053 (some (false,true,2054)) (some (true,true,194))
          (.node 2047 (some (false,true,2048)) (some (true,true,2053))
            (.node 2044 (some (false,true,2045)) (some (true,true,2046))
              (.node 2043 (some (false,true,2035)) (some (true,true,2019))
                (.node 2042 (some (false,true,2043)) (some (true,true,2044)) .empty .empty)
                .empty)
              (.node 2046 (some (false,false,2033)) (some (true,true,2028))
                (.node 2045 (some (false,true,2038)) (some (true,true,61)) .empty .empty)
                .empty))
            (.node 2050 (some (false,true,2051)) (some (true,true,2031))
              (.node 2049 (some (false,true,2050)) (some (true,true,2029))
                (.node 2048 (some (false,true,2027)) (some (true,true,2049)) .empty .empty)
                .empty)
              (.node 2052 (some (false,true,166)) (some (true,false,2005))
                (.node 2051 (some (false,true,166)) (some (true,true,2052)) .empty .empty)
                .empty)))
          (.node 2061 (some (false,true,90)) (some (true,true,2062))
            (.node 2057 (some (false,true,2027)) (some (true,true,2038))
              (.node 2056 (some (false,true,2057)) (some (true,true,2058))
                (.node 2054 (some (false,true,2019)) (some (true,true,2056)) .empty .empty)
                .empty)
              (.node 2059 (some (false,true,2014)) (some (true,true,2063))
                (.node 2058 (some (false,true,2059)) (some (true,true,2021)) .empty .empty)
                .empty))
            (.node 2064 (some (false,true,2065)) (some (true,true,2030))
              (.node 2063 (some (false,true,2020)) (some (true,true,2064))
                (.node 2062 (some (false,true,2021)) (some (true,true,90)) .empty .empty)
                .empty)
              (.node 2066 (some (false,true,221)) (some (false,false,302))
                (.node 2065 (some (false,true,2019)) (some (true,true,2061)) .empty .empty)
                .empty)))))))

def cachedMachine : M6.Zip.TMN := table.read

theorem keys_match : table.keys.all labels.contains = true := by decide +kernel

theorem outside (q : Nat) (b : Bool) (h : q ∉ labels) :
    cachedMachine q b = none := by
  apply table.outside
  intro hq
  exact h (List.contains_iff_mem.mp (List.all_eq_true.mp keys_match q hq))

def agreesAt (q : Nat) : Bool := (cachedMachine q false == machine q false) &&
  (cachedMachine q true == machine q true)

def checkRows (base count : Nat) : Bool :=
  ((labels.drop base).take count).all agreesAt

theorem checkRows_sound (base count j : Nat) (hb : checkRows base count = true)
    (hlo : base ≤ j) (hhi : j < base+count) (hj : j < labels.length) :
    agreesAt labels[j] = true := by
  let part := (labels.drop base).take count
  have h : j-base < part.length := by simp [part]; omega
  have he : part[j-base] = labels[j] := by
    simp only [part,List.getElem_take,List.getElem_drop]
    congr 1
    omega
  rw [←he]
  exact List.all_eq_true.mp hb _ (List.mem_of_getElem (i := j-base) (h := h) rfl)

#print axioms keys_match
#print axioms checkRows_sound
end PA194FoldedCache
