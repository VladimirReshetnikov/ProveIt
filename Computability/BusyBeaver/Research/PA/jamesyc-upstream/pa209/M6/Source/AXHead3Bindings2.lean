module
public import M6.Source.AXMacroPlan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXHead3
private theorem row1946_c0 : resolveAt exactSites 1946 = some (CopyToT.expected 3 1946 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1946_c1 : resolveAt exactSites 1947 = some (CopyToT.expected 3 1946 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1946_c2 : resolveAt exactSites 1948 = some (CopyToT.expected 3 1946 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1946_c3 : resolveAt exactSites 1949 = some (CopyToT.expected 3 1946 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1946_c4 : resolveAt exactSites 1950 = some (CopyToT.expected 3 1946 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1946_c5 : resolveAt exactSites 1951 = some (CopyToT.expected 3 1946 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1946_c6 : resolveAt exactSites 1952 = some (CopyToT.expected 3 1946 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1946_c : CopyToT.Bound exactSites 3 1946 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1946_c0
  · exact row1946_c1
  · exact row1946_c2
  · exact row1946_c3
  · exact row1946_c4
  · exact row1946_c5
  · exact row1946_c6
theorem block1946 : AXMacro.Realizes exactSites .copyA 1946 1953 :=
  AXMacro.copyA_realizes bound1946_c
private theorem row1953_p0 : resolveAt exactSites 1953 = some (AXPushParam.relocate 1928 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p1 : resolveAt exactSites 1954 = some (AXPushParam.relocate 1928 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p2 : resolveAt exactSites 1955 = some (AXPushParam.relocate 1928 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p3 : resolveAt exactSites 1956 = some (AXPushParam.relocate 1928 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p4 : resolveAt exactSites 1957 = some (AXPushParam.relocate 1928 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p5 : resolveAt exactSites 1958 = some (AXPushParam.relocate 1928 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p6 : resolveAt exactSites 1959 = some (AXPushParam.relocate 1928 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p7 : resolveAt exactSites 1960 = some (AXPushParam.relocate 1928 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p8 : resolveAt exactSites 1961 = some (AXPushParam.relocate 1928 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p9 : resolveAt exactSites 1962 = some (AXPushParam.relocate 1928 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p10 : resolveAt exactSites 1963 = some (AXPushParam.relocate 1928 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p11 : resolveAt exactSites 1964 = some (AXPushParam.relocate 1928 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p12 : resolveAt exactSites 1965 = some (AXPushParam.relocate 1928 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p13 : resolveAt exactSites 1966 = some (AXPushParam.relocate 1928 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p14 : resolveAt exactSites 1967 = some (AXPushParam.relocate 1928 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p15 : resolveAt exactSites 1968 = some (AXPushParam.relocate 1928 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p16 : resolveAt exactSites 1969 = some (AXPushParam.relocate 1928 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p17 : resolveAt exactSites 1970 = some (AXPushParam.relocate 1928 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1953_p18 : resolveAt exactSites 1971 = some (AXPushParam.relocate 1928 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1953_p : AXPushParam.Bound exactSites 1928 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1953_p0
  · exact row1953_p1
  · exact row1953_p2
  · exact row1953_p3
  · exact row1953_p4
  · exact row1953_p5
  · exact row1953_p6
  · exact row1953_p7
  · exact row1953_p8
  · exact row1953_p9
  · exact row1953_p10
  · exact row1953_p11
  · exact row1953_p12
  · exact row1953_p13
  · exact row1953_p14
  · exact row1953_p15
  · exact row1953_p16
  · exact row1953_p17
  · exact row1953_p18
theorem block1953 : AXMacro.Realizes exactSites .push 1953 1972 :=
  AXMacro.push_realizes bound1953_p
private theorem row1972_c0 : resolveAt exactSites 1972 = some (CopyToT.expected 5 1972 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1972_c1 : resolveAt exactSites 1973 = some (CopyToT.expected 5 1972 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1972_c2 : resolveAt exactSites 1974 = some (CopyToT.expected 5 1972 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1972_c3 : resolveAt exactSites 1975 = some (CopyToT.expected 5 1972 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1972_c4 : resolveAt exactSites 1976 = some (CopyToT.expected 5 1972 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1972_c5 : resolveAt exactSites 1977 = some (CopyToT.expected 5 1972 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1972_c6 : resolveAt exactSites 1978 = some (CopyToT.expected 5 1972 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1972_c : CopyToT.Bound exactSites 5 1972 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1972_c0
  · exact row1972_c1
  · exact row1972_c2
  · exact row1972_c3
  · exact row1972_c4
  · exact row1972_c5
  · exact row1972_c6
theorem block1972 : AXMacro.Realizes exactSites .copyH 1972 1979 :=
  AXMacro.copyH_realizes bound1972_c
private theorem row1979_u0 : resolveAt exactSites 1979 = some (UnpairPartial.expected 1979 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u1 : resolveAt exactSites 1980 = some (UnpairPartial.expected 1979 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u2 : resolveAt exactSites 1981 = some (UnpairPartial.expected 1979 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u3 : resolveAt exactSites 1982 = some (UnpairPartial.expected 1979 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u4 : resolveAt exactSites 1983 = some (UnpairPartial.expected 1979 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u5 : resolveAt exactSites 1984 = some (UnpairPartial.expected 1979 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u6 : resolveAt exactSites 1985 = some (UnpairPartial.expected 1979 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u7 : resolveAt exactSites 1986 = some (UnpairPartial.expected 1979 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u8 : resolveAt exactSites 1987 = some (UnpairPartial.expected 1979 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u9 : resolveAt exactSites 1988 = some (UnpairPartial.expected 1979 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_u10 : resolveAt exactSites 1989 = some (UnpairPartial.expected 1979 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1979_u : UnpairPartial.Bound exactSites 1979 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1979_u0
  · exact row1979_u1
  · exact row1979_u2
  · exact row1979_u3
  · exact row1979_u4
  · exact row1979_u5
  · exact row1979_u6
  · exact row1979_u7
  · exact row1979_u8
  · exact row1979_u9
  · exact row1979_u10
private theorem row1979_q0 : resolveAt exactSites 1990 = some (AXPair.relocate 1959 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q1 : resolveAt exactSites 1991 = some (AXPair.relocate 1959 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q2 : resolveAt exactSites 1992 = some (AXPair.relocate 1959 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q3 : resolveAt exactSites 1993 = some (AXPair.relocate 1959 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q4 : resolveAt exactSites 1994 = some (AXPair.relocate 1959 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q5 : resolveAt exactSites 1995 = some (AXPair.relocate 1959 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q6 : resolveAt exactSites 1996 = some (AXPair.relocate 1959 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q7 : resolveAt exactSites 1997 = some (AXPair.relocate 1959 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q8 : resolveAt exactSites 1998 = some (AXPair.relocate 1959 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_q9 : resolveAt exactSites 1999 = some (AXPair.relocate 1959 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1979_q : AXPair.Bound exactSites 1959 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1979_q0
  · exact row1979_q1
  · exact row1979_q2
  · exact row1979_q3
  · exact row1979_q4
  · exact row1979_q5
  · exact row1979_q6
  · exact row1979_q7
  · exact row1979_q8
  · exact row1979_q9
private theorem row1979_m0 : resolveAt exactSites 2000 = some (AXTimes4.expected 2000 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_m1 : resolveAt exactSites 2001 = some (AXTimes4.expected 2000 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_m2 : resolveAt exactSites 2002 = some (AXTimes4.expected 2000 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_m3 : resolveAt exactSites 2003 = some (AXTimes4.expected 2000 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_m4 : resolveAt exactSites 2004 = some (AXTimes4.expected 2000 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1979_m5 : resolveAt exactSites 2005 = some (AXTimes4.expected 2000 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1979_m : AXTimes4.Bound exactSites 2000 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1979_m0
  · exact row1979_m1
  · exact row1979_m2
  · exact row1979_m3
  · exact row1979_m4
  · exact row1979_m5
theorem block1979 : AXMacro.Realizes exactSites .cons 1979 2006 :=
  AXMacro.cons_realizes bound1979_u bound1979_q bound1979_m
private theorem row2006_i0 : resolveAt exactSites 2006 = some (Instruction.inc 1 (some 2007)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block2006 : AXMacro.Realizes exactSites .incT 2006 2007 :=
  AXMacro.inc_realizes row2006_i0
private theorem row2007_u0 : resolveAt exactSites 2007 = some (UnpairPartial.expected 2007 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u1 : resolveAt exactSites 2008 = some (UnpairPartial.expected 2007 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u2 : resolveAt exactSites 2009 = some (UnpairPartial.expected 2007 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u3 : resolveAt exactSites 2010 = some (UnpairPartial.expected 2007 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u4 : resolveAt exactSites 2011 = some (UnpairPartial.expected 2007 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u5 : resolveAt exactSites 2012 = some (UnpairPartial.expected 2007 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u6 : resolveAt exactSites 2013 = some (UnpairPartial.expected 2007 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u7 : resolveAt exactSites 2014 = some (UnpairPartial.expected 2007 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u8 : resolveAt exactSites 2015 = some (UnpairPartial.expected 2007 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u9 : resolveAt exactSites 2016 = some (UnpairPartial.expected 2007 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_u10 : resolveAt exactSites 2017 = some (UnpairPartial.expected 2007 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound2007_u : UnpairPartial.Bound exactSites 2007 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2007_u0
  · exact row2007_u1
  · exact row2007_u2
  · exact row2007_u3
  · exact row2007_u4
  · exact row2007_u5
  · exact row2007_u6
  · exact row2007_u7
  · exact row2007_u8
  · exact row2007_u9
  · exact row2007_u10
private theorem row2007_q0 : resolveAt exactSites 2018 = some (AXPair.relocate 1987 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q1 : resolveAt exactSites 2019 = some (AXPair.relocate 1987 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q2 : resolveAt exactSites 2020 = some (AXPair.relocate 1987 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q3 : resolveAt exactSites 2021 = some (AXPair.relocate 1987 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q4 : resolveAt exactSites 2022 = some (AXPair.relocate 1987 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q5 : resolveAt exactSites 2023 = some (AXPair.relocate 1987 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q6 : resolveAt exactSites 2024 = some (AXPair.relocate 1987 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q7 : resolveAt exactSites 2025 = some (AXPair.relocate 1987 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q8 : resolveAt exactSites 2026 = some (AXPair.relocate 1987 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_q9 : resolveAt exactSites 2027 = some (AXPair.relocate 1987 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound2007_q : AXPair.Bound exactSites 1987 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2007_q0
  · exact row2007_q1
  · exact row2007_q2
  · exact row2007_q3
  · exact row2007_q4
  · exact row2007_q5
  · exact row2007_q6
  · exact row2007_q7
  · exact row2007_q8
  · exact row2007_q9
private theorem row2007_m0 : resolveAt exactSites 2028 = some (AXTimes4.expected 2028 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_m1 : resolveAt exactSites 2029 = some (AXTimes4.expected 2028 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_m2 : resolveAt exactSites 2030 = some (AXTimes4.expected 2028 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_m3 : resolveAt exactSites 2031 = some (AXTimes4.expected 2028 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_m4 : resolveAt exactSites 2032 = some (AXTimes4.expected 2028 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2007_m5 : resolveAt exactSites 2033 = some (AXTimes4.expected 2028 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound2007_m : AXTimes4.Bound exactSites 2028 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2007_m0
  · exact row2007_m1
  · exact row2007_m2
  · exact row2007_m3
  · exact row2007_m4
  · exact row2007_m5
theorem block2007 : AXMacro.Realizes exactSites .cons 2007 2034 :=
  AXMacro.cons_realizes bound2007_u bound2007_q bound2007_m
private theorem row2034_u0 : resolveAt exactSites 2034 = some (UnpairPartial.expected 2034 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u1 : resolveAt exactSites 2035 = some (UnpairPartial.expected 2034 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u2 : resolveAt exactSites 2036 = some (UnpairPartial.expected 2034 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u3 : resolveAt exactSites 2037 = some (UnpairPartial.expected 2034 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u4 : resolveAt exactSites 2038 = some (UnpairPartial.expected 2034 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u5 : resolveAt exactSites 2039 = some (UnpairPartial.expected 2034 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u6 : resolveAt exactSites 2040 = some (UnpairPartial.expected 2034 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u7 : resolveAt exactSites 2041 = some (UnpairPartial.expected 2034 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u8 : resolveAt exactSites 2042 = some (UnpairPartial.expected 2034 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u9 : resolveAt exactSites 2043 = some (UnpairPartial.expected 2034 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_u10 : resolveAt exactSites 2044 = some (UnpairPartial.expected 2034 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound2034_u : UnpairPartial.Bound exactSites 2034 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2034_u0
  · exact row2034_u1
  · exact row2034_u2
  · exact row2034_u3
  · exact row2034_u4
  · exact row2034_u5
  · exact row2034_u6
  · exact row2034_u7
  · exact row2034_u8
  · exact row2034_u9
  · exact row2034_u10
private theorem row2034_q0 : resolveAt exactSites 2045 = some (AXPair.relocate 2014 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q1 : resolveAt exactSites 2046 = some (AXPair.relocate 2014 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q2 : resolveAt exactSites 2047 = some (AXPair.relocate 2014 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q3 : resolveAt exactSites 2048 = some (AXPair.relocate 2014 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q4 : resolveAt exactSites 2049 = some (AXPair.relocate 2014 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q5 : resolveAt exactSites 2050 = some (AXPair.relocate 2014 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q6 : resolveAt exactSites 2051 = some (AXPair.relocate 2014 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q7 : resolveAt exactSites 2052 = some (AXPair.relocate 2014 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q8 : resolveAt exactSites 2053 = some (AXPair.relocate 2014 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_q9 : resolveAt exactSites 2054 = some (AXPair.relocate 2014 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound2034_q : AXPair.Bound exactSites 2014 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2034_q0
  · exact row2034_q1
  · exact row2034_q2
  · exact row2034_q3
  · exact row2034_q4
  · exact row2034_q5
  · exact row2034_q6
  · exact row2034_q7
  · exact row2034_q8
  · exact row2034_q9
private theorem row2034_m0 : resolveAt exactSites 2055 = some (AXTimes4.expected 2055 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_m1 : resolveAt exactSites 2056 = some (AXTimes4.expected 2055 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_m2 : resolveAt exactSites 2057 = some (AXTimes4.expected 2055 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_m3 : resolveAt exactSites 2058 = some (AXTimes4.expected 2055 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_m4 : resolveAt exactSites 2059 = some (AXTimes4.expected 2055 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2034_m5 : resolveAt exactSites 2060 = some (AXTimes4.expected 2055 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound2034_m : AXTimes4.Bound exactSites 2055 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row2034_m0
  · exact row2034_m1
  · exact row2034_m2
  · exact row2034_m3
  · exact row2034_m4
  · exact row2034_m5
theorem block2034 : AXMacro.Realizes exactSites .cons 2034 2061 :=
  AXMacro.cons_realizes bound2034_u bound2034_q bound2034_m
end M6.Source.AXHead3

