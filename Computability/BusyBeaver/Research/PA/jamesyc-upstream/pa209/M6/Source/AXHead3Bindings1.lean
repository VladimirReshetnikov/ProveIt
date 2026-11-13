module
public import M6.Source.AXMacroPlan
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXHead3
private theorem row1847_p0 : resolveAt exactSites 1847 = some (AXPushParam.relocate 1822 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p1 : resolveAt exactSites 1848 = some (AXPushParam.relocate 1822 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p2 : resolveAt exactSites 1849 = some (AXPushParam.relocate 1822 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p3 : resolveAt exactSites 1850 = some (AXPushParam.relocate 1822 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p4 : resolveAt exactSites 1851 = some (AXPushParam.relocate 1822 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p5 : resolveAt exactSites 1852 = some (AXPushParam.relocate 1822 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p6 : resolveAt exactSites 1853 = some (AXPushParam.relocate 1822 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p7 : resolveAt exactSites 1854 = some (AXPushParam.relocate 1822 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p8 : resolveAt exactSites 1855 = some (AXPushParam.relocate 1822 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p9 : resolveAt exactSites 1856 = some (AXPushParam.relocate 1822 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p10 : resolveAt exactSites 1857 = some (AXPushParam.relocate 1822 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p11 : resolveAt exactSites 1858 = some (AXPushParam.relocate 1822 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p12 : resolveAt exactSites 1859 = some (AXPushParam.relocate 1822 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p13 : resolveAt exactSites 1860 = some (AXPushParam.relocate 1822 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p14 : resolveAt exactSites 1861 = some (AXPushParam.relocate 1822 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p15 : resolveAt exactSites 1862 = some (AXPushParam.relocate 1822 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p16 : resolveAt exactSites 1863 = some (AXPushParam.relocate 1822 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p17 : resolveAt exactSites 1864 = some (AXPushParam.relocate 1822 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1847_p18 : resolveAt exactSites 1865 = some (AXPushParam.relocate 1822 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1847_p : AXPushParam.Bound exactSites 1822 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1847_p0
  · exact row1847_p1
  · exact row1847_p2
  · exact row1847_p3
  · exact row1847_p4
  · exact row1847_p5
  · exact row1847_p6
  · exact row1847_p7
  · exact row1847_p8
  · exact row1847_p9
  · exact row1847_p10
  · exact row1847_p11
  · exact row1847_p12
  · exact row1847_p13
  · exact row1847_p14
  · exact row1847_p15
  · exact row1847_p16
  · exact row1847_p17
  · exact row1847_p18
theorem block1847 : AXMacro.Realizes exactSites .push 1847 1866 :=
  AXMacro.push_realizes bound1847_p
private theorem row1866_c0 : resolveAt exactSites 1866 = some (CopyToT.expected 3 1866 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1866_c1 : resolveAt exactSites 1867 = some (CopyToT.expected 3 1866 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1866_c2 : resolveAt exactSites 1868 = some (CopyToT.expected 3 1866 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1866_c3 : resolveAt exactSites 1869 = some (CopyToT.expected 3 1866 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1866_c4 : resolveAt exactSites 1870 = some (CopyToT.expected 3 1866 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1866_c5 : resolveAt exactSites 1871 = some (CopyToT.expected 3 1866 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1866_c6 : resolveAt exactSites 1872 = some (CopyToT.expected 3 1866 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1866_c : CopyToT.Bound exactSites 3 1866 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1866_c0
  · exact row1866_c1
  · exact row1866_c2
  · exact row1866_c3
  · exact row1866_c4
  · exact row1866_c5
  · exact row1866_c6
theorem block1866 : AXMacro.Realizes exactSites .copyA 1866 1873 :=
  AXMacro.copyA_realizes bound1866_c
private theorem row1873_p0 : resolveAt exactSites 1873 = some (AXPushParam.relocate 1848 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p1 : resolveAt exactSites 1874 = some (AXPushParam.relocate 1848 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p2 : resolveAt exactSites 1875 = some (AXPushParam.relocate 1848 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p3 : resolveAt exactSites 1876 = some (AXPushParam.relocate 1848 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p4 : resolveAt exactSites 1877 = some (AXPushParam.relocate 1848 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p5 : resolveAt exactSites 1878 = some (AXPushParam.relocate 1848 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p6 : resolveAt exactSites 1879 = some (AXPushParam.relocate 1848 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p7 : resolveAt exactSites 1880 = some (AXPushParam.relocate 1848 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p8 : resolveAt exactSites 1881 = some (AXPushParam.relocate 1848 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p9 : resolveAt exactSites 1882 = some (AXPushParam.relocate 1848 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p10 : resolveAt exactSites 1883 = some (AXPushParam.relocate 1848 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p11 : resolveAt exactSites 1884 = some (AXPushParam.relocate 1848 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p12 : resolveAt exactSites 1885 = some (AXPushParam.relocate 1848 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p13 : resolveAt exactSites 1886 = some (AXPushParam.relocate 1848 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p14 : resolveAt exactSites 1887 = some (AXPushParam.relocate 1848 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p15 : resolveAt exactSites 1888 = some (AXPushParam.relocate 1848 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p16 : resolveAt exactSites 1889 = some (AXPushParam.relocate 1848 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p17 : resolveAt exactSites 1890 = some (AXPushParam.relocate 1848 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1873_p18 : resolveAt exactSites 1891 = some (AXPushParam.relocate 1848 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1873_p : AXPushParam.Bound exactSites 1848 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1873_p0
  · exact row1873_p1
  · exact row1873_p2
  · exact row1873_p3
  · exact row1873_p4
  · exact row1873_p5
  · exact row1873_p6
  · exact row1873_p7
  · exact row1873_p8
  · exact row1873_p9
  · exact row1873_p10
  · exact row1873_p11
  · exact row1873_p12
  · exact row1873_p13
  · exact row1873_p14
  · exact row1873_p15
  · exact row1873_p16
  · exact row1873_p17
  · exact row1873_p18
theorem block1873 : AXMacro.Realizes exactSites .push 1873 1892 :=
  AXMacro.push_realizes bound1873_p
private theorem row1892_c0 : resolveAt exactSites 1892 = some (CopyToT.expected 4 1892 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1892_c1 : resolveAt exactSites 1893 = some (CopyToT.expected 4 1892 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1892_c2 : resolveAt exactSites 1894 = some (CopyToT.expected 4 1892 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1892_c3 : resolveAt exactSites 1895 = some (CopyToT.expected 4 1892 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1892_c4 : resolveAt exactSites 1896 = some (CopyToT.expected 4 1892 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1892_c5 : resolveAt exactSites 1897 = some (CopyToT.expected 4 1892 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1892_c6 : resolveAt exactSites 1898 = some (CopyToT.expected 4 1892 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1892_c : CopyToT.Bound exactSites 4 1892 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1892_c0
  · exact row1892_c1
  · exact row1892_c2
  · exact row1892_c3
  · exact row1892_c4
  · exact row1892_c5
  · exact row1892_c6
theorem block1892 : AXMacro.Realizes exactSites .copyD 1892 1899 :=
  AXMacro.copyD_realizes bound1892_c
private theorem row1899_u0 : resolveAt exactSites 1899 = some (UnpairPartial.expected 1899 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u1 : resolveAt exactSites 1900 = some (UnpairPartial.expected 1899 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u2 : resolveAt exactSites 1901 = some (UnpairPartial.expected 1899 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u3 : resolveAt exactSites 1902 = some (UnpairPartial.expected 1899 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u4 : resolveAt exactSites 1903 = some (UnpairPartial.expected 1899 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u5 : resolveAt exactSites 1904 = some (UnpairPartial.expected 1899 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u6 : resolveAt exactSites 1905 = some (UnpairPartial.expected 1899 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u7 : resolveAt exactSites 1906 = some (UnpairPartial.expected 1899 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u8 : resolveAt exactSites 1907 = some (UnpairPartial.expected 1899 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u9 : resolveAt exactSites 1908 = some (UnpairPartial.expected 1899 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_u10 : resolveAt exactSites 1909 = some (UnpairPartial.expected 1899 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1899_u : UnpairPartial.Bound exactSites 1899 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1899_u0
  · exact row1899_u1
  · exact row1899_u2
  · exact row1899_u3
  · exact row1899_u4
  · exact row1899_u5
  · exact row1899_u6
  · exact row1899_u7
  · exact row1899_u8
  · exact row1899_u9
  · exact row1899_u10
private theorem row1899_q0 : resolveAt exactSites 1910 = some (AXPair.relocate 1879 (AXPair.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q1 : resolveAt exactSites 1911 = some (AXPair.relocate 1879 (AXPair.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q2 : resolveAt exactSites 1912 = some (AXPair.relocate 1879 (AXPair.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q3 : resolveAt exactSites 1913 = some (AXPair.relocate 1879 (AXPair.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q4 : resolveAt exactSites 1914 = some (AXPair.relocate 1879 (AXPair.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q5 : resolveAt exactSites 1915 = some (AXPair.relocate 1879 (AXPair.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q6 : resolveAt exactSites 1916 = some (AXPair.relocate 1879 (AXPair.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q7 : resolveAt exactSites 1917 = some (AXPair.relocate 1879 (AXPair.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q8 : resolveAt exactSites 1918 = some (AXPair.relocate 1879 (AXPair.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_q9 : resolveAt exactSites 1919 = some (AXPair.relocate 1879 (AXPair.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1899_q : AXPair.Bound exactSites 1879 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1899_q0
  · exact row1899_q1
  · exact row1899_q2
  · exact row1899_q3
  · exact row1899_q4
  · exact row1899_q5
  · exact row1899_q6
  · exact row1899_q7
  · exact row1899_q8
  · exact row1899_q9
private theorem row1899_m0 : resolveAt exactSites 1920 = some (AXTimes4.expected 1920 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_m1 : resolveAt exactSites 1921 = some (AXTimes4.expected 1920 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_m2 : resolveAt exactSites 1922 = some (AXTimes4.expected 1920 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_m3 : resolveAt exactSites 1923 = some (AXTimes4.expected 1920 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_m4 : resolveAt exactSites 1924 = some (AXTimes4.expected 1920 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1899_m5 : resolveAt exactSites 1925 = some (AXTimes4.expected 1920 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1899_m : AXTimes4.Bound exactSites 1920 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1899_m0
  · exact row1899_m1
  · exact row1899_m2
  · exact row1899_m3
  · exact row1899_m4
  · exact row1899_m5
theorem block1899 : AXMacro.Realizes exactSites .cons 1899 1926 :=
  AXMacro.cons_realizes bound1899_u bound1899_q bound1899_m
private theorem row1926_i0 : resolveAt exactSites 1926 = some (Instruction.inc 1 (some 1927)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem block1926 : AXMacro.Realizes exactSites .incT 1926 1927 :=
  AXMacro.inc_realizes row1926_i0
private theorem row1927_p0 : resolveAt exactSites 1927 = some (AXPushParam.relocate 1902 (AXPushParam.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p1 : resolveAt exactSites 1928 = some (AXPushParam.relocate 1902 (AXPushParam.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p2 : resolveAt exactSites 1929 = some (AXPushParam.relocate 1902 (AXPushParam.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p3 : resolveAt exactSites 1930 = some (AXPushParam.relocate 1902 (AXPushParam.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p4 : resolveAt exactSites 1931 = some (AXPushParam.relocate 1902 (AXPushParam.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p5 : resolveAt exactSites 1932 = some (AXPushParam.relocate 1902 (AXPushParam.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p6 : resolveAt exactSites 1933 = some (AXPushParam.relocate 1902 (AXPushParam.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p7 : resolveAt exactSites 1934 = some (AXPushParam.relocate 1902 (AXPushParam.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p8 : resolveAt exactSites 1935 = some (AXPushParam.relocate 1902 (AXPushParam.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p9 : resolveAt exactSites 1936 = some (AXPushParam.relocate 1902 (AXPushParam.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p10 : resolveAt exactSites 1937 = some (AXPushParam.relocate 1902 (AXPushParam.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p11 : resolveAt exactSites 1938 = some (AXPushParam.relocate 1902 (AXPushParam.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p12 : resolveAt exactSites 1939 = some (AXPushParam.relocate 1902 (AXPushParam.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p13 : resolveAt exactSites 1940 = some (AXPushParam.relocate 1902 (AXPushParam.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p14 : resolveAt exactSites 1941 = some (AXPushParam.relocate 1902 (AXPushParam.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p15 : resolveAt exactSites 1942 = some (AXPushParam.relocate 1902 (AXPushParam.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p16 : resolveAt exactSites 1943 = some (AXPushParam.relocate 1902 (AXPushParam.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p17 : resolveAt exactSites 1944 = some (AXPushParam.relocate 1902 (AXPushParam.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1927_p18 : resolveAt exactSites 1945 = some (AXPushParam.relocate 1902 (AXPushParam.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem bound1927_p : AXPushParam.Bound exactSites 1902 := by
  intro ⟨j,hj⟩
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1927_p0
  · exact row1927_p1
  · exact row1927_p2
  · exact row1927_p3
  · exact row1927_p4
  · exact row1927_p5
  · exact row1927_p6
  · exact row1927_p7
  · exact row1927_p8
  · exact row1927_p9
  · exact row1927_p10
  · exact row1927_p11
  · exact row1927_p12
  · exact row1927_p13
  · exact row1927_p14
  · exact row1927_p15
  · exact row1927_p16
  · exact row1927_p17
  · exact row1927_p18
theorem block1927 : AXMacro.Realizes exactSites .push 1927 1946 :=
  AXMacro.push_realizes bound1927_p
end M6.Source.AXHead3

