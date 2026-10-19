import BusyBeaver.ZFC.ControlCatalogue
import BusyBeaver.ZFC.TreeRotation240

set_option autoImplicit false

/-! Cached leaf counts for the exact Rotation240 decoder tree.
The finite mirror is structurally bound to the canonical tree by rfl.
Each annotation/count equation uses only the two proved child equations.
No packed-table acceptance or machine simulation is asserted here.
Attribution follows TreeRotation240 and ControlCatalogue. -/

namespace SetTheory.BusyBeaver.ZFC.CountedTreeRotation240
open RMBisim (Tree)
open ControlCatalogue

private theorem count_node {l r : Tree} {a b : Nat}
    (hl : SiteCoverage.leafCount l = a) (hr : SiteCoverage.leafCount r = b) :
    SiteCoverage.leafCount (.node l r) = a+b := by
  change SiteCoverage.leafCount l + SiteCoverage.leafCount r = a+b
  rw [hl, hr]

private theorem ann_node {l r : Tree} {cl cr : CTree} {a : Nat}
    (hn : SiteCoverage.leafCount l = a)
    (hl : annotate l = cl) (hr : annotate r = cr) :
    annotate (.node l r) = .node a cl cr := by
  simp only [annotate, hn, hl, hr]

private def p000 : Tree := .node (.leaf (.decnz 8)) (.leaf (.brk 1))
private def c000 : CTree := .node 1 (.leaf (.decnz 8)) (.leaf (.brk 1))
private theorem count000 : SiteCoverage.leafCount p000 = 2 := by
  exact count_node (l := (.leaf (.decnz 8))) (r := (.leaf (.brk 1))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann000 : annotate p000 = c000 := by
  exact ann_node (l := (.leaf (.decnz 8))) (r := (.leaf (.brk 1))) (cl := (.leaf (.decnz 8))) (cr := (.leaf (.brk 1))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p001 : Tree := .node (.leaf (.inc 6)) (.leaf (.cont 3))
private def c001 : CTree := .node 1 (.leaf (.inc 6)) (.leaf (.cont 3))
private theorem count001 : SiteCoverage.leafCount p001 = 2 := by
  exact count_node (l := (.leaf (.inc 6))) (r := (.leaf (.cont 3))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann001 : annotate p001 = c001 := by
  exact ann_node (l := (.leaf (.inc 6))) (r := (.leaf (.cont 3))) (cl := (.leaf (.inc 6))) (cr := (.leaf (.cont 3))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p002 : Tree := .node (.leaf (.inc 8)) p001
private def c002 : CTree := .node 1 (.leaf (.inc 8)) c001
private theorem count002 : SiteCoverage.leafCount p002 = 3 := by
  exact count_node (l := (.leaf (.inc 8))) (r := p001) (a := 1) (b := 2) (by rfl) count001
private theorem ann002 : annotate p002 = c002 := by
  exact ann_node (l := (.leaf (.inc 8))) (r := p001) (cl := (.leaf (.inc 8))) (cr := c001) (a := 1) (by rfl) (by rfl) ann001

private def p003 : Tree := .node (.leaf (.decnz 0)) p002
private def c003 : CTree := .node 1 (.leaf (.decnz 0)) c002
private theorem count003 : SiteCoverage.leafCount p003 = 4 := by
  exact count_node (l := (.leaf (.decnz 0))) (r := p002) (a := 1) (b := 3) (by rfl) count002
private theorem ann003 : annotate p003 = c003 := by
  exact ann_node (l := (.leaf (.decnz 0))) (r := p002) (cl := (.leaf (.decnz 0))) (cr := c002) (a := 1) (by rfl) (by rfl) ann002

private def p004 : Tree := .node (.leaf (.inc 0)) (.leaf (.cont 2))
private def c004 : CTree := .node 1 (.leaf (.inc 0)) (.leaf (.cont 2))
private theorem count004 : SiteCoverage.leafCount p004 = 2 := by
  exact count_node (l := (.leaf (.inc 0))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann004 : annotate p004 = c004 := by
  exact ann_node (l := (.leaf (.inc 0))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 0))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p005 : Tree := .node (.leaf (.decnz 6)) (.leaf (.cont 2))
private def c005 : CTree := .node 1 (.leaf (.decnz 6)) (.leaf (.cont 2))
private theorem count005 : SiteCoverage.leafCount p005 = 2 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann005 : annotate p005 = c005 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := (.leaf (.cont 2))) (cl := (.leaf (.decnz 6))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p006 : Tree := .node (.leaf (.inc 0)) p005
private def c006 : CTree := .node 1 (.leaf (.inc 0)) c005
private theorem count006 : SiteCoverage.leafCount p006 = 3 := by
  exact count_node (l := (.leaf (.inc 0))) (r := p005) (a := 1) (b := 2) (by rfl) count005
private theorem ann006 : annotate p006 = c006 := by
  exact ann_node (l := (.leaf (.inc 0))) (r := p005) (cl := (.leaf (.inc 0))) (cr := c005) (a := 1) (by rfl) (by rfl) ann005

private def p007 : Tree := .node p003 p006
private def c007 : CTree := .node 4 c003 c006
private theorem count007 : SiteCoverage.leafCount p007 = 7 := by
  exact count_node (l := p003) (r := p006) (a := 4) (b := 3) count003 count006
private theorem ann007 : annotate p007 = c007 := by
  exact ann_node (l := p003) (r := p006) (cl := c003) (cr := c006) (a := 4) count003 ann003 ann006

private def p008 : Tree := .node p000 p007
private def c008 : CTree := .node 2 c000 c007
private theorem count008 : SiteCoverage.leafCount p008 = 9 := by
  exact count_node (l := p000) (r := p007) (a := 2) (b := 7) count000 count007
private theorem ann008 : annotate p008 = c008 := by
  exact ann_node (l := p000) (r := p007) (cl := c000) (cr := c007) (a := 2) count000 ann000 ann007

private def p009 : Tree := .node (.leaf (.decnz 6)) (.leaf (.brk 1))
private def c009 : CTree := .node 1 (.leaf (.decnz 6)) (.leaf (.brk 1))
private theorem count009 : SiteCoverage.leafCount p009 = 2 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := (.leaf (.brk 1))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann009 : annotate p009 = c009 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := (.leaf (.brk 1))) (cl := (.leaf (.decnz 6))) (cr := (.leaf (.brk 1))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p010 : Tree := .node (.leaf (.inc 6)) (.leaf (.cont 2))
private def c010 : CTree := .node 1 (.leaf (.inc 6)) (.leaf (.cont 2))
private theorem count010 : SiteCoverage.leafCount p010 = 2 := by
  exact count_node (l := (.leaf (.inc 6))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann010 : annotate p010 = c010 := by
  exact ann_node (l := (.leaf (.inc 6))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 6))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p011 : Tree := .node (.leaf (.decnz 7)) p010
private def c011 : CTree := .node 1 (.leaf (.decnz 7)) c010
private theorem count011 : SiteCoverage.leafCount p011 = 3 := by
  exact count_node (l := (.leaf (.decnz 7))) (r := p010) (a := 1) (b := 2) (by rfl) count010
private theorem ann011 : annotate p011 = c011 := by
  exact ann_node (l := (.leaf (.decnz 7))) (r := p010) (cl := (.leaf (.decnz 7))) (cr := c010) (a := 1) (by rfl) (by rfl) ann010

private def p012 : Tree := .node p009 p011
private def c012 : CTree := .node 2 c009 c011
private theorem count012 : SiteCoverage.leafCount p012 = 5 := by
  exact count_node (l := p009) (r := p011) (a := 2) (b := 3) count009 count011
private theorem ann012 : annotate p012 = c012 := by
  exact ann_node (l := p009) (r := p011) (cl := c009) (cr := c011) (a := 2) count009 ann009 ann011

private def p013 : Tree := .node p012 (.leaf (.cont 3))
private def c013 : CTree := .node 5 c012 (.leaf (.cont 3))
private theorem count013 : SiteCoverage.leafCount p013 = 6 := by
  exact count_node (l := p012) (r := (.leaf (.cont 3))) (a := 5) (b := 1) count012 (by rfl)
private theorem ann013 : annotate p013 = c013 := by
  exact ann_node (l := p012) (r := (.leaf (.cont 3))) (cl := c012) (cr := (.leaf (.cont 3))) (a := 5) count012 ann012 (by rfl)

private def p014 : Tree := .node (.leaf (.inc 7)) p013
private def c014 : CTree := .node 1 (.leaf (.inc 7)) c013
private theorem count014 : SiteCoverage.leafCount p014 = 7 := by
  exact count_node (l := (.leaf (.inc 7))) (r := p013) (a := 1) (b := 6) (by rfl) count013
private theorem ann014 : annotate p014 = c014 := by
  exact ann_node (l := (.leaf (.inc 7))) (r := p013) (cl := (.leaf (.inc 7))) (cr := c013) (a := 1) (by rfl) (by rfl) ann013

private def p015 : Tree := .node (.leaf (.decnz 8)) p014
private def c015 : CTree := .node 1 (.leaf (.decnz 8)) c014
private theorem count015 : SiteCoverage.leafCount p015 = 8 := by
  exact count_node (l := (.leaf (.decnz 8))) (r := p014) (a := 1) (b := 7) (by rfl) count014
private theorem ann015 : annotate p015 = c015 := by
  exact ann_node (l := (.leaf (.decnz 8))) (r := p014) (cl := (.leaf (.decnz 8))) (cr := c014) (a := 1) (by rfl) (by rfl) ann014

private def p016 : Tree := .node (.leaf (.inc 8)) (.leaf (.cont 2))
private def c016 : CTree := .node 1 (.leaf (.inc 8)) (.leaf (.cont 2))
private theorem count016 : SiteCoverage.leafCount p016 = 2 := by
  exact count_node (l := (.leaf (.inc 8))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann016 : annotate p016 = c016 := by
  exact ann_node (l := (.leaf (.inc 8))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 8))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p017 : Tree := .node (.leaf (.decnz 7)) p016
private def c017 : CTree := .node 1 (.leaf (.decnz 7)) c016
private theorem count017 : SiteCoverage.leafCount p017 = 3 := by
  exact count_node (l := (.leaf (.decnz 7))) (r := p016) (a := 1) (b := 2) (by rfl) count016
private theorem ann017 : annotate p017 = c017 := by
  exact ann_node (l := (.leaf (.decnz 7))) (r := p016) (cl := (.leaf (.decnz 7))) (cr := c016) (a := 1) (by rfl) (by rfl) ann016

private def p018 : Tree := .node p015 p017
private def c018 : CTree := .node 8 c015 c017
private theorem count018 : SiteCoverage.leafCount p018 = 11 := by
  exact count_node (l := p015) (r := p017) (a := 8) (b := 3) count015 count017
private theorem ann018 : annotate p018 = c018 := by
  exact ann_node (l := p015) (r := p017) (cl := c015) (cr := c017) (a := 8) count015 ann015 ann017

private def p019 : Tree := .node (.leaf (.inc 3)) (.leaf (.cont 2))
private def c019 : CTree := .node 1 (.leaf (.inc 3)) (.leaf (.cont 2))
private theorem count019 : SiteCoverage.leafCount p019 = 2 := by
  exact count_node (l := (.leaf (.inc 3))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann019 : annotate p019 = c019 := by
  exact ann_node (l := (.leaf (.inc 3))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 3))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p020 : Tree := .node (.leaf (.decnz 6)) p019
private def c020 : CTree := .node 1 (.leaf (.decnz 6)) c019
private theorem count020 : SiteCoverage.leafCount p020 = 3 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := p019) (a := 1) (b := 2) (by rfl) count019
private theorem ann020 : annotate p020 = c020 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := p019) (cl := (.leaf (.decnz 6))) (cr := c019) (a := 1) (by rfl) (by rfl) ann019

private def p021 : Tree := .node p018 p020
private def c021 : CTree := .node 11 c018 c020
private theorem count021 : SiteCoverage.leafCount p021 = 14 := by
  exact count_node (l := p018) (r := p020) (a := 11) (b := 3) count018 count020
private theorem ann021 : annotate p021 = c021 := by
  exact ann_node (l := p018) (r := p020) (cl := c018) (cr := c020) (a := 11) count018 ann018 ann020

private def p022 : Tree := .node (.leaf (.inc 4)) (.leaf (.cont 2))
private def c022 : CTree := .node 1 (.leaf (.inc 4)) (.leaf (.cont 2))
private theorem count022 : SiteCoverage.leafCount p022 = 2 := by
  exact count_node (l := (.leaf (.inc 4))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann022 : annotate p022 = c022 := by
  exact ann_node (l := (.leaf (.inc 4))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 4))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p023 : Tree := .node (.leaf (.decnz 6)) p022
private def c023 : CTree := .node 1 (.leaf (.decnz 6)) c022
private theorem count023 : SiteCoverage.leafCount p023 = 3 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := p022) (a := 1) (b := 2) (by rfl) count022
private theorem ann023 : annotate p023 = c023 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := p022) (cl := (.leaf (.decnz 6))) (cr := c022) (a := 1) (by rfl) (by rfl) ann022

private def p024 : Tree := .node p018 p023
private def c024 : CTree := .node 11 c018 c023
private theorem count024 : SiteCoverage.leafCount p024 = 14 := by
  exact count_node (l := p018) (r := p023) (a := 11) (b := 3) count018 count023
private theorem ann024 : annotate p024 = c024 := by
  exact ann_node (l := p018) (r := p023) (cl := c018) (cr := c023) (a := 11) count018 ann018 ann023

private def p025 : Tree := .node (.leaf (.decnz 1)) p010
private def c025 : CTree := .node 1 (.leaf (.decnz 1)) c010
private theorem count025 : SiteCoverage.leafCount p025 = 3 := by
  exact count_node (l := (.leaf (.decnz 1))) (r := p010) (a := 1) (b := 2) (by rfl) count010
private theorem ann025 : annotate p025 = c025 := by
  exact ann_node (l := (.leaf (.decnz 1))) (r := p010) (cl := (.leaf (.decnz 1))) (cr := c010) (a := 1) (by rfl) (by rfl) ann010

private def p026 : Tree := .node (.leaf (.inc 1)) (.leaf (.cont 2))
private def c026 : CTree := .node 1 (.leaf (.inc 1)) (.leaf (.cont 2))
private theorem count026 : SiteCoverage.leafCount p026 = 2 := by
  exact count_node (l := (.leaf (.inc 1))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann026 : annotate p026 = c026 := by
  exact ann_node (l := (.leaf (.inc 1))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 1))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p027 : Tree := .node (.leaf (.decnz 2)) p026
private def c027 : CTree := .node 1 (.leaf (.decnz 2)) c026
private theorem count027 : SiteCoverage.leafCount p027 = 3 := by
  exact count_node (l := (.leaf (.decnz 2))) (r := p026) (a := 1) (b := 2) (by rfl) count026
private theorem ann027 : annotate p027 = c027 := by
  exact ann_node (l := (.leaf (.decnz 2))) (r := p026) (cl := (.leaf (.decnz 2))) (cr := c026) (a := 1) (by rfl) (by rfl) ann026

private def p028 : Tree := .node (.leaf (.inc 7)) p001
private def c028 : CTree := .node 1 (.leaf (.inc 7)) c001
private theorem count028 : SiteCoverage.leafCount p028 = 3 := by
  exact count_node (l := (.leaf (.inc 7))) (r := p001) (a := 1) (b := 2) (by rfl) count001
private theorem ann028 : annotate p028 = c028 := by
  exact ann_node (l := (.leaf (.inc 7))) (r := p001) (cl := (.leaf (.inc 7))) (cr := c001) (a := 1) (by rfl) (by rfl) ann001

private def p029 : Tree := .node (.leaf (.decnz 1)) p028
private def c029 : CTree := .node 1 (.leaf (.decnz 1)) c028
private theorem count029 : SiteCoverage.leafCount p029 = 4 := by
  exact count_node (l := (.leaf (.decnz 1))) (r := p028) (a := 1) (b := 3) (by rfl) count028
private theorem ann029 : annotate p029 = c029 := by
  exact ann_node (l := (.leaf (.decnz 1))) (r := p028) (cl := (.leaf (.decnz 1))) (cr := c028) (a := 1) (by rfl) (by rfl) ann028

private def p030 : Tree := .node (.leaf (.decnz 6)) p026
private def c030 : CTree := .node 1 (.leaf (.decnz 6)) c026
private theorem count030 : SiteCoverage.leafCount p030 = 3 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := p026) (a := 1) (b := 2) (by rfl) count026
private theorem ann030 : annotate p030 = c030 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := p026) (cl := (.leaf (.decnz 6))) (cr := c026) (a := 1) (by rfl) (by rfl) ann026

private def p031 : Tree := .node (.leaf (.inc 7)) p030
private def c031 : CTree := .node 1 (.leaf (.inc 7)) c030
private theorem count031 : SiteCoverage.leafCount p031 = 4 := by
  exact count_node (l := (.leaf (.inc 7))) (r := p030) (a := 1) (b := 3) (by rfl) count030
private theorem ann031 : annotate p031 = c031 := by
  exact ann_node (l := (.leaf (.inc 7))) (r := p030) (cl := (.leaf (.inc 7))) (cr := c030) (a := 1) (by rfl) (by rfl) ann030

private def p032 : Tree := .node p031 (.leaf (.cont 3))
private def c032 : CTree := .node 4 c031 (.leaf (.cont 3))
private theorem count032 : SiteCoverage.leafCount p032 = 5 := by
  exact count_node (l := p031) (r := (.leaf (.cont 3))) (a := 4) (b := 1) count031 (by rfl)
private theorem ann032 : annotate p032 = c032 := by
  exact ann_node (l := p031) (r := (.leaf (.cont 3))) (cl := c031) (cr := (.leaf (.cont 3))) (a := 4) count031 ann031 (by rfl)

private def p033 : Tree := .node (.leaf (.decnz 6)) p032
private def c033 : CTree := .node 1 (.leaf (.decnz 6)) c032
private theorem count033 : SiteCoverage.leafCount p033 = 6 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := p032) (a := 1) (b := 5) (by rfl) count032
private theorem ann033 : annotate p033 = c033 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := p032) (cl := (.leaf (.decnz 6))) (cr := c032) (a := 1) (by rfl) (by rfl) ann032

private def p034 : Tree := .node p029 p033
private def c034 : CTree := .node 4 c029 c033
private theorem count034 : SiteCoverage.leafCount p034 = 10 := by
  exact count_node (l := p029) (r := p033) (a := 4) (b := 6) count029 count033
private theorem ann034 : annotate p034 = c034 := by
  exact ann_node (l := p029) (r := p033) (cl := c029) (cr := c033) (a := 4) count029 ann029 ann033

private def p035 : Tree := .node (.leaf (.inc 2)) (.leaf (.cont 2))
private def c035 : CTree := .node 1 (.leaf (.inc 2)) (.leaf (.cont 2))
private theorem count035 : SiteCoverage.leafCount p035 = 2 := by
  exact count_node (l := (.leaf (.inc 2))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann035 : annotate p035 = c035 := by
  exact ann_node (l := (.leaf (.inc 2))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 2))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p036 : Tree := .node (.leaf (.decnz 7)) p035
private def c036 : CTree := .node 1 (.leaf (.decnz 7)) c035
private theorem count036 : SiteCoverage.leafCount p036 = 3 := by
  exact count_node (l := (.leaf (.decnz 7))) (r := p035) (a := 1) (b := 2) (by rfl) count035
private theorem ann036 : annotate p036 = c036 := by
  exact ann_node (l := (.leaf (.decnz 7))) (r := p035) (cl := (.leaf (.decnz 7))) (cr := c035) (a := 1) (by rfl) (by rfl) ann035

private def p037 : Tree := .node p034 p036
private def c037 : CTree := .node 10 c034 c036
private theorem count037 : SiteCoverage.leafCount p037 = 13 := by
  exact count_node (l := p034) (r := p036) (a := 10) (b := 3) count034 count036
private theorem ann037 : annotate p037 = c037 := by
  exact ann_node (l := p034) (r := p036) (cl := c034) (cr := c036) (a := 10) count034 ann034 ann036

private def p038 : Tree := .node p027 p037
private def c038 : CTree := .node 3 c027 c037
private theorem count038 : SiteCoverage.leafCount p038 = 16 := by
  exact count_node (l := p027) (r := p037) (a := 3) (b := 13) count027 count037
private theorem ann038 : annotate p038 = c038 := by
  exact ann_node (l := p027) (r := p037) (cl := c027) (cr := c037) (a := 3) count027 ann027 ann037

private def p039 : Tree := .node p025 p038
private def c039 : CTree := .node 3 c025 c038
private theorem count039 : SiteCoverage.leafCount p039 = 19 := by
  exact count_node (l := p025) (r := p038) (a := 3) (b := 16) count025 count038
private theorem ann039 : annotate p039 = c039 := by
  exact ann_node (l := p025) (r := p038) (cl := c025) (cr := c038) (a := 3) count025 ann025 ann038

private def p040 : Tree := .node (.leaf (.inc 1)) p001
private def c040 : CTree := .node 1 (.leaf (.inc 1)) c001
private theorem count040 : SiteCoverage.leafCount p040 = 3 := by
  exact count_node (l := (.leaf (.inc 1))) (r := p001) (a := 1) (b := 2) (by rfl) count001
private theorem ann040 : annotate p040 = c040 := by
  exact ann_node (l := (.leaf (.inc 1))) (r := p001) (cl := (.leaf (.inc 1))) (cr := c001) (a := 1) (by rfl) (by rfl) ann001

private def p041 : Tree := .node (.leaf (.decnz 4)) p040
private def c041 : CTree := .node 1 (.leaf (.decnz 4)) c040
private theorem count041 : SiteCoverage.leafCount p041 = 4 := by
  exact count_node (l := (.leaf (.decnz 4))) (r := p040) (a := 1) (b := 3) (by rfl) count040
private theorem ann041 : annotate p041 = c041 := by
  exact ann_node (l := (.leaf (.decnz 4))) (r := p040) (cl := (.leaf (.decnz 4))) (cr := c040) (a := 1) (by rfl) (by rfl) ann040

private def p042 : Tree := .node p041 p023
private def c042 : CTree := .node 4 c041 c023
private theorem count042 : SiteCoverage.leafCount p042 = 7 := by
  exact count_node (l := p041) (r := p023) (a := 4) (b := 3) count041 count023
private theorem ann042 : annotate p042 = c042 := by
  exact ann_node (l := p041) (r := p023) (cl := c041) (cr := c023) (a := 4) count041 ann041 ann023

private def p043 : Tree := .node (.leaf (.decnz 5)) p040
private def c043 : CTree := .node 1 (.leaf (.decnz 5)) c040
private theorem count043 : SiteCoverage.leafCount p043 = 4 := by
  exact count_node (l := (.leaf (.decnz 5))) (r := p040) (a := 1) (b := 3) (by rfl) count040
private theorem ann043 : annotate p043 = c043 := by
  exact ann_node (l := (.leaf (.decnz 5))) (r := p040) (cl := (.leaf (.decnz 5))) (cr := c040) (a := 1) (by rfl) (by rfl) ann040

private def p044 : Tree := .node (.leaf (.inc 5)) (.leaf (.cont 2))
private def c044 : CTree := .node 1 (.leaf (.inc 5)) (.leaf (.cont 2))
private theorem count044 : SiteCoverage.leafCount p044 = 2 := by
  exact count_node (l := (.leaf (.inc 5))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann044 : annotate p044 = c044 := by
  exact ann_node (l := (.leaf (.inc 5))) (r := (.leaf (.cont 2))) (cl := (.leaf (.inc 5))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p045 : Tree := .node (.leaf (.decnz 6)) p044
private def c045 : CTree := .node 1 (.leaf (.decnz 6)) c044
private theorem count045 : SiteCoverage.leafCount p045 = 3 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := p044) (a := 1) (b := 2) (by rfl) count044
private theorem ann045 : annotate p045 = c045 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := p044) (cl := (.leaf (.decnz 6))) (cr := c044) (a := 1) (by rfl) (by rfl) ann044

private def p046 : Tree := .node p043 p045
private def c046 : CTree := .node 4 c043 c045
private theorem count046 : SiteCoverage.leafCount p046 = 7 := by
  exact count_node (l := p043) (r := p045) (a := 4) (b := 3) count043 count045
private theorem ann046 : annotate p046 = c046 := by
  exact ann_node (l := p043) (r := p045) (cl := c043) (cr := c045) (a := 4) count043 ann043 ann045

private def p047 : Tree := .node p039 p046
private def c047 : CTree := .node 19 c039 c046
private theorem count047 : SiteCoverage.leafCount p047 = 26 := by
  exact count_node (l := p039) (r := p046) (a := 19) (b := 7) count039 count046
private theorem ann047 : annotate p047 = c047 := by
  exact ann_node (l := p039) (r := p046) (cl := c039) (cr := c046) (a := 19) count039 ann039 ann046

private def p048 : Tree := .node p042 p047
private def c048 : CTree := .node 7 c042 c047
private theorem count048 : SiteCoverage.leafCount p048 = 33 := by
  exact count_node (l := p042) (r := p047) (a := 7) (b := 26) count042 count047
private theorem ann048 : annotate p048 = c048 := by
  exact ann_node (l := p042) (r := p047) (cl := c042) (cr := c047) (a := 7) count042 ann042 ann047

private def p049 : Tree := .node p039 p048
private def c049 : CTree := .node 19 c039 c048
private theorem count049 : SiteCoverage.leafCount p049 = 52 := by
  exact count_node (l := p039) (r := p048) (a := 19) (b := 33) count039 count048
private theorem ann049 : annotate p049 = c049 := by
  exact ann_node (l := p039) (r := p048) (cl := c039) (cr := c048) (a := 19) count039 ann039 ann048

private def p050 : Tree := .node (.leaf (.decnz 2)) p014
private def c050 : CTree := .node 1 (.leaf (.decnz 2)) c014
private theorem count050 : SiteCoverage.leafCount p050 = 8 := by
  exact count_node (l := (.leaf (.decnz 2))) (r := p014) (a := 1) (b := 7) (by rfl) count014
private theorem ann050 : annotate p050 = c050 := by
  exact ann_node (l := (.leaf (.decnz 2))) (r := p014) (cl := (.leaf (.decnz 2))) (cr := c014) (a := 1) (by rfl) (by rfl) ann014

private def p051 : Tree := .node p050 p036
private def c051 : CTree := .node 8 c050 c036
private theorem count051 : SiteCoverage.leafCount p051 = 11 := by
  exact count_node (l := p050) (r := p036) (a := 8) (b := 3) count050 count036
private theorem ann051 : annotate p051 = c051 := by
  exact ann_node (l := p050) (r := p036) (cl := c050) (cr := c036) (a := 8) count050 ann050 ann036

private def p052 : Tree := .node (.leaf (.inc 1)) (.leaf (.inc 1))
private def c052 : CTree := .node 1 (.leaf (.inc 1)) (.leaf (.inc 1))
private theorem count052 : SiteCoverage.leafCount p052 = 2 := by
  exact count_node (l := (.leaf (.inc 1))) (r := (.leaf (.inc 1))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann052 : annotate p052 = c052 := by
  exact ann_node (l := (.leaf (.inc 1))) (r := (.leaf (.inc 1))) (cl := (.leaf (.inc 1))) (cr := (.leaf (.inc 1))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p053 : Tree := .node p052 p052
private def c053 : CTree := .node 2 c052 c052
private theorem count053 : SiteCoverage.leafCount p053 = 4 := by
  exact count_node (l := p052) (r := p052) (a := 2) (b := 2) count052 count052
private theorem ann053 : annotate p053 = c053 := by
  exact ann_node (l := p052) (r := p052) (cl := c052) (cr := c052) (a := 2) count052 ann052 ann052

private def p054 : Tree := .node p053 (.leaf (.cont 2))
private def c054 : CTree := .node 4 c053 (.leaf (.cont 2))
private theorem count054 : SiteCoverage.leafCount p054 = 5 := by
  exact count_node (l := p053) (r := (.leaf (.cont 2))) (a := 4) (b := 1) count053 (by rfl)
private theorem ann054 : annotate p054 = c054 := by
  exact ann_node (l := p053) (r := (.leaf (.cont 2))) (cl := c053) (cr := (.leaf (.cont 2))) (a := 4) count053 ann053 (by rfl)

private def p055 : Tree := .node (.leaf (.decnz 7)) p054
private def c055 : CTree := .node 1 (.leaf (.decnz 7)) c054
private theorem count055 : SiteCoverage.leafCount p055 = 6 := by
  exact count_node (l := (.leaf (.decnz 7))) (r := p054) (a := 1) (b := 5) (by rfl) count054
private theorem ann055 : annotate p055 = c055 := by
  exact ann_node (l := (.leaf (.decnz 7))) (r := p054) (cl := (.leaf (.decnz 7))) (cr := c054) (a := 1) (by rfl) (by rfl) ann054

private def p056 : Tree := .node p034 p055
private def c056 : CTree := .node 10 c034 c055
private theorem count056 : SiteCoverage.leafCount p056 = 16 := by
  exact count_node (l := p034) (r := p055) (a := 10) (b := 6) count034 count055
private theorem ann056 : annotate p056 = c056 := by
  exact ann_node (l := p034) (r := p055) (cl := c034) (cr := c055) (a := 10) count034 ann034 ann055

private def p057 : Tree := .node p051 p056
private def c057 : CTree := .node 11 c051 c056
private theorem count057 : SiteCoverage.leafCount p057 = 27 := by
  exact count_node (l := p051) (r := p056) (a := 11) (b := 16) count051 count056
private theorem ann057 : annotate p057 = c057 := by
  exact ann_node (l := p051) (r := p056) (cl := c051) (cr := c056) (a := 11) count051 ann051 ann056

private def p058 : Tree := .node p057 p052
private def c058 : CTree := .node 27 c057 c052
private theorem count058 : SiteCoverage.leafCount p058 = 29 := by
  exact count_node (l := p057) (r := p052) (a := 27) (b := 2) count057 count052
private theorem ann058 : annotate p058 = c058 := by
  exact ann_node (l := p057) (r := p052) (cl := c057) (cr := c052) (a := 27) count057 ann057 ann052

private def p059 : Tree := .node p049 p058
private def c059 : CTree := .node 52 c049 c058
private theorem count059 : SiteCoverage.leafCount p059 = 81 := by
  exact count_node (l := p049) (r := p058) (a := 52) (b := 29) count049 count058
private theorem ann059 : annotate p059 = c059 := by
  exact ann_node (l := p049) (r := p058) (cl := c049) (cr := c058) (a := 52) count049 ann049 ann058

private def p060 : Tree := .node p018 p045
private def c060 : CTree := .node 11 c018 c045
private theorem count060 : SiteCoverage.leafCount p060 = 14 := by
  exact count_node (l := p018) (r := p045) (a := 11) (b := 3) count018 count045
private theorem ann060 : annotate p060 = c060 := by
  exact ann_node (l := p018) (r := p045) (cl := c018) (cr := c045) (a := 11) count018 ann018 ann045

private def p061 : Tree := .node (.leaf (.decnz 3)) p040
private def c061 : CTree := .node 1 (.leaf (.decnz 3)) c040
private theorem count061 : SiteCoverage.leafCount p061 = 4 := by
  exact count_node (l := (.leaf (.decnz 3))) (r := p040) (a := 1) (b := 3) (by rfl) count040
private theorem ann061 : annotate p061 = c061 := by
  exact ann_node (l := (.leaf (.decnz 3))) (r := p040) (cl := (.leaf (.decnz 3))) (cr := c040) (a := 1) (by rfl) (by rfl) ann040

private def p062 : Tree := .node p061 p020
private def c062 : CTree := .node 4 c061 c020
private theorem count062 : SiteCoverage.leafCount p062 = 7 := by
  exact count_node (l := p061) (r := p020) (a := 4) (b := 3) count061 count020
private theorem ann062 : annotate p062 = c062 := by
  exact ann_node (l := p061) (r := p020) (cl := c061) (cr := c020) (a := 4) count061 ann061 ann020

private def p063 : Tree := .node p039 p062
private def c063 : CTree := .node 19 c039 c062
private theorem count063 : SiteCoverage.leafCount p063 = 26 := by
  exact count_node (l := p039) (r := p062) (a := 19) (b := 7) count039 count062
private theorem ann063 : annotate p063 = c063 := by
  exact ann_node (l := p039) (r := p062) (cl := c039) (cr := c062) (a := 19) count039 ann039 ann062

private def p064 : Tree := .node p063 p039
private def c064 : CTree := .node 26 c063 c039
private theorem count064 : SiteCoverage.leafCount p064 = 45 := by
  exact count_node (l := p063) (r := p039) (a := 26) (b := 19) count063 count039
private theorem ann064 : annotate p064 = c064 := by
  exact ann_node (l := p063) (r := p039) (cl := c063) (cr := c039) (a := 26) count063 ann063 ann039

private def p065 : Tree := .node p018 p030
private def c065 : CTree := .node 11 c018 c030
private theorem count065 : SiteCoverage.leafCount p065 = 14 := by
  exact count_node (l := p018) (r := p030) (a := 11) (b := 3) count018 count030
private theorem ann065 : annotate p065 = c065 := by
  exact ann_node (l := p018) (r := p030) (cl := c018) (cr := c030) (a := 11) count018 ann018 ann030

private def p066 : Tree := .node p065 p057
private def c066 : CTree := .node 14 c065 c057
private theorem count066 : SiteCoverage.leafCount p066 = 41 := by
  exact count_node (l := p065) (r := p057) (a := 14) (b := 27) count065 count057
private theorem ann066 : annotate p066 = c066 := by
  exact ann_node (l := p065) (r := p057) (cl := c065) (cr := c057) (a := 14) count065 ann065 ann057

private def p067 : Tree := .node p064 p066
private def c067 : CTree := .node 45 c064 c066
private theorem count067 : SiteCoverage.leafCount p067 = 86 := by
  exact count_node (l := p064) (r := p066) (a := 45) (b := 41) count064 count066
private theorem ann067 : annotate p067 = c067 := by
  exact ann_node (l := p064) (r := p066) (cl := c064) (cr := c066) (a := 45) count064 ann064 ann066

private def p068 : Tree := .node p039 p042
private def c068 : CTree := .node 19 c039 c042
private theorem count068 : SiteCoverage.leafCount p068 = 26 := by
  exact count_node (l := p039) (r := p042) (a := 19) (b := 7) count039 count042
private theorem ann068 : annotate p068 = c068 := by
  exact ann_node (l := p039) (r := p042) (cl := c039) (cr := c042) (a := 19) count039 ann039 ann042

private def p069 : Tree := .node p068 p057
private def c069 : CTree := .node 26 c068 c057
private theorem count069 : SiteCoverage.leafCount p069 = 53 := by
  exact count_node (l := p068) (r := p057) (a := 26) (b := 27) count068 count057
private theorem ann069 : annotate p069 = c069 := by
  exact ann_node (l := p068) (r := p057) (cl := c068) (cr := c057) (a := 26) count068 ann068 ann057

private def p070 : Tree := .node p067 p069
private def c070 : CTree := .node 86 c067 c069
private theorem count070 : SiteCoverage.leafCount p070 = 139 := by
  exact count_node (l := p067) (r := p069) (a := 86) (b := 53) count067 count069
private theorem ann070 : annotate p070 = c070 := by
  exact ann_node (l := p067) (r := p069) (cl := c067) (cr := c069) (a := 86) count067 ann067 ann069

private def p071 : Tree := .node p060 p070
private def c071 : CTree := .node 14 c060 c070
private theorem count071 : SiteCoverage.leafCount p071 = 153 := by
  exact count_node (l := p060) (r := p070) (a := 14) (b := 139) count060 count070
private theorem ann071 : annotate p071 = c071 := by
  exact ann_node (l := p060) (r := p070) (cl := c060) (cr := c070) (a := 14) count060 ann060 ann070

private def p072 : Tree := .node p068 p063
private def c072 : CTree := .node 26 c068 c063
private theorem count072 : SiteCoverage.leafCount p072 = 52 := by
  exact count_node (l := p068) (r := p063) (a := 26) (b := 26) count068 count063
private theorem ann072 : annotate p072 = c072 := by
  exact ann_node (l := p068) (r := p063) (cl := c068) (cr := c063) (a := 26) count068 ann068 ann063

private def p073 : Tree := .node p072 p057
private def c073 : CTree := .node 52 c072 c057
private theorem count073 : SiteCoverage.leafCount p073 = 79 := by
  exact count_node (l := p072) (r := p057) (a := 52) (b := 27) count072 count057
private theorem ann073 : annotate p073 = c073 := by
  exact ann_node (l := p072) (r := p057) (cl := c072) (cr := c057) (a := 52) count072 ann072 ann057

private def p074 : Tree := .node p047 p063
private def c074 : CTree := .node 26 c047 c063
private theorem count074 : SiteCoverage.leafCount p074 = 52 := by
  exact count_node (l := p047) (r := p063) (a := 26) (b := 26) count047 count063
private theorem ann074 : annotate p074 = c074 := by
  exact ann_node (l := p047) (r := p063) (cl := c047) (cr := c063) (a := 26) count047 ann047 ann063

private def p075 : Tree := .node p057 p057
private def c075 : CTree := .node 27 c057 c057
private theorem count075 : SiteCoverage.leafCount p075 = 54 := by
  exact count_node (l := p057) (r := p057) (a := 27) (b := 27) count057 count057
private theorem ann075 : annotate p075 = c075 := by
  exact ann_node (l := p057) (r := p057) (cl := c057) (cr := c057) (a := 27) count057 ann057 ann057

private def p076 : Tree := .node p057 (.leaf (.inc 1))
private def c076 : CTree := .node 27 c057 (.leaf (.inc 1))
private theorem count076 : SiteCoverage.leafCount p076 = 28 := by
  exact count_node (l := p057) (r := (.leaf (.inc 1))) (a := 27) (b := 1) count057 (by rfl)
private theorem ann076 : annotate p076 = c076 := by
  exact ann_node (l := p057) (r := (.leaf (.inc 1))) (cl := c057) (cr := (.leaf (.inc 1))) (a := 27) count057 ann057 (by rfl)

private def p077 : Tree := .node p068 p076
private def c077 : CTree := .node 26 c068 c076
private theorem count077 : SiteCoverage.leafCount p077 = 54 := by
  exact count_node (l := p068) (r := p076) (a := 26) (b := 28) count068 count076
private theorem ann077 : annotate p077 = c077 := by
  exact ann_node (l := p068) (r := p076) (cl := c068) (cr := c076) (a := 26) count068 ann068 ann076

private def p078 : Tree := .node p063 p077
private def c078 : CTree := .node 26 c063 c077
private theorem count078 : SiteCoverage.leafCount p078 = 80 := by
  exact count_node (l := p063) (r := p077) (a := 26) (b := 54) count063 count077
private theorem ann078 : annotate p078 = c078 := by
  exact ann_node (l := p063) (r := p077) (cl := c063) (cr := c077) (a := 26) count063 ann063 ann077

private def p079 : Tree := .node p064 p046
private def c079 : CTree := .node 45 c064 c046
private theorem count079 : SiteCoverage.leafCount p079 = 52 := by
  exact count_node (l := p064) (r := p046) (a := 45) (b := 7) count064 count046
private theorem ann079 : annotate p079 = c079 := by
  exact ann_node (l := p064) (r := p046) (cl := c064) (cr := c046) (a := 45) count064 ann064 ann046

private def p080 : Tree := .node p079 p076
private def c080 : CTree := .node 52 c079 c076
private theorem count080 : SiteCoverage.leafCount p080 = 80 := by
  exact count_node (l := p079) (r := p076) (a := 52) (b := 28) count079 count076
private theorem ann080 : annotate p080 = c080 := by
  exact ann_node (l := p079) (r := p076) (cl := c079) (cr := c076) (a := 52) count079 ann079 ann076

private def p081 : Tree := .node p052 p080
private def c081 : CTree := .node 2 c052 c080
private theorem count081 : SiteCoverage.leafCount p081 = 82 := by
  exact count_node (l := p052) (r := p080) (a := 2) (b := 80) count052 count080
private theorem ann081 : annotate p081 = c081 := by
  exact ann_node (l := p052) (r := p080) (cl := c052) (cr := c080) (a := 2) count052 ann052 ann080

private def p082 : Tree := .node p078 p081
private def c082 : CTree := .node 80 c078 c081
private theorem count082 : SiteCoverage.leafCount p082 = 162 := by
  exact count_node (l := p078) (r := p081) (a := 80) (b := 82) count078 count081
private theorem ann082 : annotate p082 = c082 := by
  exact ann_node (l := p078) (r := p081) (cl := c078) (cr := c081) (a := 80) count078 ann078 ann081

private def p083 : Tree := .node p057 p082
private def c083 : CTree := .node 27 c057 c082
private theorem count083 : SiteCoverage.leafCount p083 = 189 := by
  exact count_node (l := p057) (r := p082) (a := 27) (b := 162) count057 count082
private theorem ann083 : annotate p083 = c083 := by
  exact ann_node (l := p057) (r := p082) (cl := c057) (cr := c082) (a := 27) count057 ann057 ann082

private def p084 : Tree := .node p059 (.leaf (.inc 1))
private def c084 : CTree := .node 81 c059 (.leaf (.inc 1))
private theorem count084 : SiteCoverage.leafCount p084 = 82 := by
  exact count_node (l := p059) (r := (.leaf (.inc 1))) (a := 81) (b := 1) count059 (by rfl)
private theorem ann084 : annotate p084 = c084 := by
  exact ann_node (l := p059) (r := (.leaf (.inc 1))) (cl := c059) (cr := (.leaf (.inc 1))) (a := 81) count059 ann059 (by rfl)

private def p085 : Tree := .node p075 p068
private def c085 : CTree := .node 54 c075 c068
private theorem count085 : SiteCoverage.leafCount p085 = 80 := by
  exact count_node (l := p075) (r := p068) (a := 54) (b := 26) count075 count068
private theorem ann085 : annotate p085 = c085 := by
  exact ann_node (l := p075) (r := p068) (cl := c075) (cr := c068) (a := 54) count075 ann075 ann068

private def p086 : Tree := .node p084 p085
private def c086 : CTree := .node 82 c084 c085
private theorem count086 : SiteCoverage.leafCount p086 = 162 := by
  exact count_node (l := p084) (r := p085) (a := 82) (b := 80) count084 count085
private theorem ann086 : annotate p086 = c086 := by
  exact ann_node (l := p084) (r := p085) (cl := c084) (cr := c085) (a := 82) count084 ann084 ann085

private def p087 : Tree := .node p052 p086
private def c087 : CTree := .node 2 c052 c086
private theorem count087 : SiteCoverage.leafCount p087 = 164 := by
  exact count_node (l := p052) (r := p086) (a := 2) (b := 162) count052 count086
private theorem ann087 : annotate p087 = c087 := by
  exact ann_node (l := p052) (r := p086) (cl := c052) (cr := c086) (a := 2) count052 ann052 ann086

private def p088 : Tree := .node p039 (.leaf (.inc 1))
private def c088 : CTree := .node 19 c039 (.leaf (.inc 1))
private theorem count088 : SiteCoverage.leafCount p088 = 20 := by
  exact count_node (l := p039) (r := (.leaf (.inc 1))) (a := 19) (b := 1) count039 (by rfl)
private theorem ann088 : annotate p088 = c088 := by
  exact ann_node (l := p039) (r := (.leaf (.inc 1))) (cl := c039) (cr := (.leaf (.inc 1))) (a := 19) count039 ann039 (by rfl)

private def p089 : Tree := .node p088 p057
private def c089 : CTree := .node 20 c088 c057
private theorem count089 : SiteCoverage.leafCount p089 = 47 := by
  exact count_node (l := p088) (r := p057) (a := 20) (b := 27) count088 count057
private theorem ann089 : annotate p089 = c089 := by
  exact ann_node (l := p088) (r := p057) (cl := c088) (cr := c057) (a := 20) count088 ann088 ann057

private def p090 : Tree := .node p058 p089
private def c090 : CTree := .node 29 c058 c089
private theorem count090 : SiteCoverage.leafCount p090 = 76 := by
  exact count_node (l := p058) (r := p089) (a := 29) (b := 47) count058 count089
private theorem ann090 : annotate p090 = c090 := by
  exact ann_node (l := p058) (r := p089) (cl := c058) (cr := c089) (a := 29) count058 ann058 ann089

private def p091 : Tree := .node p089 p090
private def c091 : CTree := .node 47 c089 c090
private theorem count091 : SiteCoverage.leafCount p091 = 123 := by
  exact count_node (l := p089) (r := p090) (a := 47) (b := 76) count089 count090
private theorem ann091 : annotate p091 = c091 := by
  exact ann_node (l := p089) (r := p090) (cl := c089) (cr := c090) (a := 47) count089 ann089 ann090

private def p092 : Tree := .node p091 p047
private def c092 : CTree := .node 123 c091 c047
private theorem count092 : SiteCoverage.leafCount p092 = 149 := by
  exact count_node (l := p091) (r := p047) (a := 123) (b := 26) count091 count047
private theorem ann092 : annotate p092 = c092 := by
  exact ann_node (l := p091) (r := p047) (cl := c091) (cr := c047) (a := 123) count091 ann091 ann047

private def p093 : Tree := .node p059 p092
private def c093 : CTree := .node 81 c059 c092
private theorem count093 : SiteCoverage.leafCount p093 = 230 := by
  exact count_node (l := p059) (r := p092) (a := 81) (b := 149) count059 count092
private theorem ann093 : annotate p093 = c093 := by
  exact ann_node (l := p059) (r := p092) (cl := c059) (cr := c092) (a := 81) count059 ann059 ann092

private def p094 : Tree := .node p049 p076
private def c094 : CTree := .node 52 c049 c076
private theorem count094 : SiteCoverage.leafCount p094 = 80 := by
  exact count_node (l := p049) (r := p076) (a := 52) (b := 28) count049 count076
private theorem ann094 : annotate p094 = c094 := by
  exact ann_node (l := p049) (r := p076) (cl := c049) (cr := c076) (a := 52) count049 ann049 ann076

private def p095 : Tree := .node p085 p074
private def c095 : CTree := .node 80 c085 c074
private theorem count095 : SiteCoverage.leafCount p095 = 132 := by
  exact count_node (l := p085) (r := p074) (a := 80) (b := 52) count085 count074
private theorem ann095 : annotate p095 = c095 := by
  exact ann_node (l := p085) (r := p074) (cl := c085) (cr := c074) (a := 80) count085 ann085 ann074

private def p096 : Tree := .node p094 p095
private def c096 : CTree := .node 80 c094 c095
private theorem count096 : SiteCoverage.leafCount p096 = 212 := by
  exact count_node (l := p094) (r := p095) (a := 80) (b := 132) count094 count095
private theorem ann096 : annotate p096 = c096 := by
  exact ann_node (l := p094) (r := p095) (cl := c094) (cr := c095) (a := 80) count094 ann094 ann095

private def p097 : Tree := .node p058 p057
private def c097 : CTree := .node 29 c058 c057
private theorem count097 : SiteCoverage.leafCount p097 = 56 := by
  exact count_node (l := p058) (r := p057) (a := 29) (b := 27) count058 count057
private theorem ann097 : annotate p097 = c097 := by
  exact ann_node (l := p058) (r := p057) (cl := c058) (cr := c057) (a := 29) count058 ann058 ann057

private def p098 : Tree := .node p072 p058
private def c098 : CTree := .node 52 c072 c058
private theorem count098 : SiteCoverage.leafCount p098 = 81 := by
  exact count_node (l := p072) (r := p058) (a := 52) (b := 29) count072 count058
private theorem ann098 : annotate p098 = c098 := by
  exact ann_node (l := p072) (r := p058) (cl := c072) (cr := c058) (a := 52) count072 ann072 ann058

private def p099 : Tree := .node p097 p084
private def c099 : CTree := .node 56 c097 c084
private theorem count099 : SiteCoverage.leafCount p099 = 138 := by
  exact count_node (l := p097) (r := p084) (a := 56) (b := 82) count097 count084
private theorem ann099 : annotate p099 = c099 := by
  exact ann_node (l := p097) (r := p084) (cl := c097) (cr := c084) (a := 56) count097 ann097 ann084

private def p100 : Tree := .node p098 p099
private def c100 : CTree := .node 81 c098 c099
private theorem count100 : SiteCoverage.leafCount p100 = 219 := by
  exact count_node (l := p098) (r := p099) (a := 81) (b := 138) count098 count099
private theorem ann100 : annotate p100 = c100 := by
  exact ann_node (l := p098) (r := p099) (cl := c098) (cr := c099) (a := 81) count098 ann098 ann099

private def p101 : Tree := .node p047 p100
private def c101 : CTree := .node 26 c047 c100
private theorem count101 : SiteCoverage.leafCount p101 = 245 := by
  exact count_node (l := p047) (r := p100) (a := 26) (b := 219) count047 count100
private theorem ann101 : annotate p101 = c101 := by
  exact ann_node (l := p047) (r := p100) (cl := c047) (cr := c100) (a := 26) count047 ann047 ann100

private def p102 : Tree := .node p078 p080
private def c102 : CTree := .node 80 c078 c080
private theorem count102 : SiteCoverage.leafCount p102 = 160 := by
  exact count_node (l := p078) (r := p080) (a := 80) (b := 80) count078 count080
private theorem ann102 : annotate p102 = c102 := by
  exact ann_node (l := p078) (r := p080) (cl := c078) (cr := c080) (a := 80) count078 ann078 ann080

private def p103 : Tree := .node p102 p095
private def c103 : CTree := .node 160 c102 c095
private theorem count103 : SiteCoverage.leafCount p103 = 292 := by
  exact count_node (l := p102) (r := p095) (a := 160) (b := 132) count102 count095
private theorem ann103 : annotate p103 = c103 := by
  exact ann_node (l := p102) (r := p095) (cl := c102) (cr := c095) (a := 160) count102 ann102 ann095

private def p104 : Tree := .node p101 p103
private def c104 : CTree := .node 245 c101 c103
private theorem count104 : SiteCoverage.leafCount p104 = 537 := by
  exact count_node (l := p101) (r := p103) (a := 245) (b := 292) count101 count103
private theorem ann104 : annotate p104 = c104 := by
  exact ann_node (l := p101) (r := p103) (cl := c101) (cr := c103) (a := 245) count101 ann101 ann103

private def p105 : Tree := .node p052 p104
private def c105 : CTree := .node 2 c052 c104
private theorem count105 : SiteCoverage.leafCount p105 = 539 := by
  exact count_node (l := p052) (r := p104) (a := 2) (b := 537) count052 count104
private theorem ann105 : annotate p105 = c105 := by
  exact ann_node (l := p052) (r := p104) (cl := c052) (cr := c104) (a := 2) count052 ann052 ann104

private def p106 : Tree := .node p057 p058
private def c106 : CTree := .node 27 c057 c058
private theorem count106 : SiteCoverage.leafCount p106 = 56 := by
  exact count_node (l := p057) (r := p058) (a := 27) (b := 29) count057 count058
private theorem ann106 : annotate p106 = c106 := by
  exact ann_node (l := p057) (r := p058) (cl := c057) (cr := c058) (a := 27) count057 ann057 ann058

private def p107 : Tree := .node p105 p106
private def c107 : CTree := .node 539 c105 c106
private theorem count107 : SiteCoverage.leafCount p107 = 595 := by
  exact count_node (l := p105) (r := p106) (a := 539) (b := 56) count105 count106
private theorem ann107 : annotate p107 = c107 := by
  exact ann_node (l := p105) (r := p106) (cl := c105) (cr := c106) (a := 539) count105 ann105 ann106

private def p108 : Tree := .node p097 p107
private def c108 : CTree := .node 56 c097 c107
private theorem count108 : SiteCoverage.leafCount p108 = 651 := by
  exact count_node (l := p097) (r := p107) (a := 56) (b := 595) count097 count107
private theorem ann108 : annotate p108 = c108 := by
  exact ann_node (l := p097) (r := p107) (cl := c097) (cr := c107) (a := 56) count097 ann097 ann107

private def p109 : Tree := .node p096 p108
private def c109 : CTree := .node 212 c096 c108
private theorem count109 : SiteCoverage.leafCount p109 = 863 := by
  exact count_node (l := p096) (r := p108) (a := 212) (b := 651) count096 count108
private theorem ann109 : annotate p109 = c109 := by
  exact ann_node (l := p096) (r := p108) (cl := c096) (cr := c108) (a := 212) count096 ann096 ann108

private def p110 : Tree := .node p083 p109
private def c110 : CTree := .node 189 c083 c109
private theorem count110 : SiteCoverage.leafCount p110 = 1052 := by
  exact count_node (l := p083) (r := p109) (a := 189) (b := 863) count083 count109
private theorem ann110 : annotate p110 = c110 := by
  exact ann_node (l := p083) (r := p109) (cl := c083) (cr := c109) (a := 189) count083 ann083 ann109

private def p111 : Tree := .node p098 p085
private def c111 : CTree := .node 81 c098 c085
private theorem count111 : SiteCoverage.leafCount p111 = 161 := by
  exact count_node (l := p098) (r := p085) (a := 81) (b := 80) count098 count085
private theorem ann111 : annotate p111 = c111 := by
  exact ann_node (l := p098) (r := p085) (cl := c098) (cr := c085) (a := 81) count098 ann098 ann085

private def p112 : Tree := .node p059 p111
private def c112 : CTree := .node 81 c059 c111
private theorem count112 : SiteCoverage.leafCount p112 = 242 := by
  exact count_node (l := p059) (r := p111) (a := 81) (b := 161) count059 count111
private theorem ann112 : annotate p112 = c112 := by
  exact ann_node (l := p059) (r := p111) (cl := c059) (cr := c111) (a := 81) count059 ann059 ann111

private def p113 : Tree := .node p084 p092
private def c113 : CTree := .node 82 c084 c092
private theorem count113 : SiteCoverage.leafCount p113 = 231 := by
  exact count_node (l := p084) (r := p092) (a := 82) (b := 149) count084 count092
private theorem ann113 : annotate p113 = c113 := by
  exact ann_node (l := p084) (r := p092) (cl := c084) (cr := c092) (a := 82) count084 ann084 ann092

private def p114 : Tree := .node p112 p113
private def c114 : CTree := .node 242 c112 c113
private theorem count114 : SiteCoverage.leafCount p114 = 473 := by
  exact count_node (l := p112) (r := p113) (a := 242) (b := 231) count112 count113
private theorem ann114 : annotate p114 = c114 := by
  exact ann_node (l := p112) (r := p113) (cl := c112) (cr := c113) (a := 242) count112 ann112 ann113

private def p115 : Tree := .node p110 p114
private def c115 : CTree := .node 1052 c110 c114
private theorem count115 : SiteCoverage.leafCount p115 = 1525 := by
  exact count_node (l := p110) (r := p114) (a := 1052) (b := 473) count110 count114
private theorem ann115 : annotate p115 = c115 := by
  exact ann_node (l := p110) (r := p114) (cl := c110) (cr := c114) (a := 1052) count110 ann110 ann114

private def p116 : Tree := .node p093 p115
private def c116 : CTree := .node 230 c093 c115
private theorem count116 : SiteCoverage.leafCount p116 = 1755 := by
  exact count_node (l := p093) (r := p115) (a := 230) (b := 1525) count093 count115
private theorem ann116 : annotate p116 = c116 := by
  exact ann_node (l := p093) (r := p115) (cl := c093) (cr := c115) (a := 230) count093 ann093 ann115

private def p117 : Tree := .node p087 p116
private def c117 : CTree := .node 164 c087 c116
private theorem count117 : SiteCoverage.leafCount p117 = 1919 := by
  exact count_node (l := p087) (r := p116) (a := 164) (b := 1755) count087 count116
private theorem ann117 : annotate p117 = c117 := by
  exact ann_node (l := p087) (r := p116) (cl := c087) (cr := c116) (a := 164) count087 ann087 ann116

private def p118 : Tree := .node p068 p094
private def c118 : CTree := .node 26 c068 c094
private theorem count118 : SiteCoverage.leafCount p118 = 106 := by
  exact count_node (l := p068) (r := p094) (a := 26) (b := 80) count068 count094
private theorem ann118 : annotate p118 = c118 := by
  exact ann_node (l := p068) (r := p094) (cl := c068) (cr := c094) (a := 26) count068 ann068 ann094

private def p119 : Tree := .node p063 p074
private def c119 : CTree := .node 26 c063 c074
private theorem count119 : SiteCoverage.leafCount p119 = 78 := by
  exact count_node (l := p063) (r := p074) (a := 26) (b := 52) count063 count074
private theorem ann119 : annotate p119 = c119 := by
  exact ann_node (l := p063) (r := p074) (cl := c063) (cr := c074) (a := 26) count063 ann063 ann074

private def p120 : Tree := .node p119 p080
private def c120 : CTree := .node 78 c119 c080
private theorem count120 : SiteCoverage.leafCount p120 = 158 := by
  exact count_node (l := p119) (r := p080) (a := 78) (b := 80) count119 count080
private theorem ann120 : annotate p120 = c120 := by
  exact ann_node (l := p119) (r := p080) (cl := c119) (cr := c080) (a := 78) count119 ann119 ann080

private def p121 : Tree := .node p078 p106
private def c121 : CTree := .node 80 c078 c106
private theorem count121 : SiteCoverage.leafCount p121 = 136 := by
  exact count_node (l := p078) (r := p106) (a := 80) (b := 56) count078 count106
private theorem ann121 : annotate p121 = c121 := by
  exact ann_node (l := p078) (r := p106) (cl := c078) (cr := c106) (a := 80) count078 ann078 ann106

private def p122 : Tree := .node p074 p076
private def c122 : CTree := .node 52 c074 c076
private theorem count122 : SiteCoverage.leafCount p122 = 80 := by
  exact count_node (l := p074) (r := p076) (a := 52) (b := 28) count074 count076
private theorem ann122 : annotate p122 = c122 := by
  exact ann_node (l := p074) (r := p076) (cl := c074) (cr := c076) (a := 52) count074 ann074 ann076

private def p123 : Tree := .node p121 p122
private def c123 : CTree := .node 136 c121 c122
private theorem count123 : SiteCoverage.leafCount p123 = 216 := by
  exact count_node (l := p121) (r := p122) (a := 136) (b := 80) count121 count122
private theorem ann123 : annotate p123 = c123 := by
  exact ann_node (l := p121) (r := p122) (cl := c121) (cr := c122) (a := 136) count121 ann121 ann122

private def p124 : Tree := .node p120 p123
private def c124 : CTree := .node 158 c120 c123
private theorem count124 : SiteCoverage.leafCount p124 = 374 := by
  exact count_node (l := p120) (r := p123) (a := 158) (b := 216) count120 count123
private theorem ann124 : annotate p124 = c124 := by
  exact ann_node (l := p120) (r := p123) (cl := c120) (cr := c123) (a := 158) count120 ann120 ann123

private def p125 : Tree := .node p118 p124
private def c125 : CTree := .node 106 c118 c124
private theorem count125 : SiteCoverage.leafCount p125 = 480 := by
  exact count_node (l := p118) (r := p124) (a := 106) (b := 374) count118 count124
private theorem ann125 : annotate p125 = c125 := by
  exact ann_node (l := p118) (r := p124) (cl := c118) (cr := c124) (a := 106) count118 ann118 ann124

private def p126 : Tree := .node p057 p089
private def c126 : CTree := .node 27 c057 c089
private theorem count126 : SiteCoverage.leafCount p126 = 74 := by
  exact count_node (l := p057) (r := p089) (a := 27) (b := 47) count057 count089
private theorem ann126 : annotate p126 = c126 := by
  exact ann_node (l := p057) (r := p089) (cl := c057) (cr := c089) (a := 27) count057 ann057 ann089

private def p127 : Tree := .node p089 p126
private def c127 : CTree := .node 47 c089 c126
private theorem count127 : SiteCoverage.leafCount p127 = 121 := by
  exact count_node (l := p089) (r := p126) (a := 47) (b := 74) count089 count126
private theorem ann127 : annotate p127 = c127 := by
  exact ann_node (l := p089) (r := p126) (cl := c089) (cr := c126) (a := 47) count089 ann089 ann126

private def p128 : Tree := .node p127 p091
private def c128 : CTree := .node 121 c127 c091
private theorem count128 : SiteCoverage.leafCount p128 = 244 := by
  exact count_node (l := p127) (r := p091) (a := 121) (b := 123) count127 count091
private theorem ann128 : annotate p128 = c128 := by
  exact ann_node (l := p127) (r := p091) (cl := c127) (cr := c091) (a := 121) count127 ann127 ann091

private def p129 : Tree := .node p081 p128
private def c129 : CTree := .node 82 c081 c128
private theorem count129 : SiteCoverage.leafCount p129 = 326 := by
  exact count_node (l := p081) (r := p128) (a := 82) (b := 244) count081 count128
private theorem ann129 : annotate p129 = c129 := by
  exact ann_node (l := p081) (r := p128) (cl := c081) (cr := c128) (a := 82) count081 ann081 ann128

private def p130 : Tree := .node p129 p063
private def c130 : CTree := .node 326 c129 c063
private theorem count130 : SiteCoverage.leafCount p130 = 352 := by
  exact count_node (l := p129) (r := p063) (a := 326) (b := 26) count129 count063
private theorem ann130 : annotate p130 = c130 := by
  exact ann_node (l := p129) (r := p063) (cl := c129) (cr := c063) (a := 326) count129 ann129 ann063

private def p131 : Tree := .node p075 p130
private def c131 : CTree := .node 54 c075 c130
private theorem count131 : SiteCoverage.leafCount p131 = 406 := by
  exact count_node (l := p075) (r := p130) (a := 54) (b := 352) count075 count130
private theorem ann131 : annotate p131 = c131 := by
  exact ann_node (l := p075) (r := p130) (cl := c075) (cr := c130) (a := 54) count075 ann075 ann130

private def p132 : Tree := .node p131 p102
private def c132 : CTree := .node 406 c131 c102
private theorem count132 : SiteCoverage.leafCount p132 = 566 := by
  exact count_node (l := p131) (r := p102) (a := 406) (b := 160) count131 count102
private theorem ann132 : annotate p132 = c132 := by
  exact ann_node (l := p131) (r := p102) (cl := c131) (cr := c102) (a := 406) count131 ann131 ann102

private def p133 : Tree := .node p125 p132
private def c133 : CTree := .node 480 c125 c132
private theorem count133 : SiteCoverage.leafCount p133 = 1046 := by
  exact count_node (l := p125) (r := p132) (a := 480) (b := 566) count125 count132
private theorem ann133 : annotate p133 = c133 := by
  exact ann_node (l := p125) (r := p132) (cl := c125) (cr := c132) (a := 480) count125 ann125 ann132

private def p134 : Tree := .node p117 p133
private def c134 : CTree := .node 1919 c117 c133
private theorem count134 : SiteCoverage.leafCount p134 = 2965 := by
  exact count_node (l := p117) (r := p133) (a := 1919) (b := 1046) count117 count133
private theorem ann134 : annotate p134 = c134 := by
  exact ann_node (l := p117) (r := p133) (cl := c117) (cr := c133) (a := 1919) count117 ann117 ann133

private def p135 : Tree := .node p106 p127
private def c135 : CTree := .node 56 c106 c127
private theorem count135 : SiteCoverage.leafCount p135 = 177 := by
  exact count_node (l := p106) (r := p127) (a := 56) (b := 121) count106 count127
private theorem ann135 : annotate p135 = c135 := by
  exact ann_node (l := p106) (r := p127) (cl := c106) (cr := c127) (a := 56) count106 ann106 ann127

private def p136 : Tree := .node p074 p074
private def c136 : CTree := .node 52 c074 c074
private theorem count136 : SiteCoverage.leafCount p136 = 104 := by
  exact count_node (l := p074) (r := p074) (a := 52) (b := 52) count074 count074
private theorem ann136 : annotate p136 = c136 := by
  exact ann_node (l := p074) (r := p074) (cl := c074) (cr := c074) (a := 52) count074 ann074 ann074

private def p137 : Tree := .node p136 p122
private def c137 : CTree := .node 104 c136 c122
private theorem count137 : SiteCoverage.leafCount p137 = 184 := by
  exact count_node (l := p136) (r := p122) (a := 104) (b := 80) count136 count122
private theorem ann137 : annotate p137 = c137 := by
  exact ann_node (l := p136) (r := p122) (cl := c136) (cr := c122) (a := 104) count136 ann136 ann122

private def p138 : Tree := .node p118 p137
private def c138 : CTree := .node 106 c118 c137
private theorem count138 : SiteCoverage.leafCount p138 = 290 := by
  exact count_node (l := p118) (r := p137) (a := 106) (b := 184) count118 count137
private theorem ann138 : annotate p138 = c138 := by
  exact ann_node (l := p118) (r := p137) (cl := c118) (cr := c137) (a := 106) count118 ann118 ann137

private def p139 : Tree := .node p138 p128
private def c139 : CTree := .node 290 c138 c128
private theorem count139 : SiteCoverage.leafCount p139 = 534 := by
  exact count_node (l := p138) (r := p128) (a := 290) (b := 244) count138 count128
private theorem ann139 : annotate p139 = c139 := by
  exact ann_node (l := p138) (r := p128) (cl := c138) (cr := c128) (a := 290) count138 ann138 ann128

private def p140 : Tree := .node p131 p139
private def c140 : CTree := .node 406 c131 c139
private theorem count140 : SiteCoverage.leafCount p140 = 940 := by
  exact count_node (l := p131) (r := p139) (a := 406) (b := 534) count131 count139
private theorem ann140 : annotate p140 = c140 := by
  exact ann_node (l := p131) (r := p139) (cl := c131) (cr := c139) (a := 406) count131 ann131 ann139

private def p141 : Tree := .node p135 p140
private def c141 : CTree := .node 177 c135 c140
private theorem count141 : SiteCoverage.leafCount p141 = 1117 := by
  exact count_node (l := p135) (r := p140) (a := 177) (b := 940) count135 count140
private theorem ann141 : annotate p141 = c141 := by
  exact ann_node (l := p135) (r := p140) (cl := c135) (cr := c140) (a := 177) count135 ann135 ann140

private def p142 : Tree := .node p134 p141
private def c142 : CTree := .node 2965 c134 c141
private theorem count142 : SiteCoverage.leafCount p142 = 4082 := by
  exact count_node (l := p134) (r := p141) (a := 2965) (b := 1117) count134 count141
private theorem ann142 : annotate p142 = c142 := by
  exact ann_node (l := p134) (r := p141) (cl := c134) (cr := c141) (a := 2965) count134 ann134 ann141

private def p143 : Tree := .node p142 p106
private def c143 : CTree := .node 4082 c142 c106
private theorem count143 : SiteCoverage.leafCount p143 = 4138 := by
  exact count_node (l := p142) (r := p106) (a := 4082) (b := 56) count142 count106
private theorem ann143 : annotate p143 = c143 := by
  exact ann_node (l := p142) (r := p106) (cl := c142) (cr := c106) (a := 4082) count142 ann142 ann106

private def p144 : Tree := .node p083 p143
private def c144 : CTree := .node 189 c083 c143
private theorem count144 : SiteCoverage.leafCount p144 = 4327 := by
  exact count_node (l := p083) (r := p143) (a := 189) (b := 4138) count083 count143
private theorem ann144 : annotate p144 = c144 := by
  exact ann_node (l := p083) (r := p143) (cl := c083) (cr := c143) (a := 189) count083 ann083 ann143

private def p145 : Tree := .node p047 p122
private def c145 : CTree := .node 26 c047 c122
private theorem count145 : SiteCoverage.leafCount p145 = 106 := by
  exact count_node (l := p047) (r := p122) (a := 26) (b := 80) count047 count122
private theorem ann145 : annotate p145 = c145 := by
  exact ann_node (l := p047) (r := p122) (cl := c047) (cr := c122) (a := 26) count047 ann047 ann122

private def p146 : Tree := .node p072 p091
private def c146 : CTree := .node 52 c072 c091
private theorem count146 : SiteCoverage.leafCount p146 = 175 := by
  exact count_node (l := p072) (r := p091) (a := 52) (b := 123) count072 count091
private theorem ann146 : annotate p146 = c146 := by
  exact ann_node (l := p072) (r := p091) (cl := c072) (cr := c091) (a := 52) count072 ann072 ann091

private def p147 : Tree := .node p145 p146
private def c147 : CTree := .node 106 c145 c146
private theorem count147 : SiteCoverage.leafCount p147 = 281 := by
  exact count_node (l := p145) (r := p146) (a := 106) (b := 175) count145 count146
private theorem ann147 : annotate p147 = c147 := by
  exact ann_node (l := p145) (r := p146) (cl := c145) (cr := c146) (a := 106) count145 ann145 ann146

private def p148 : Tree := .node p147 p135
private def c148 : CTree := .node 281 c147 c135
private theorem count148 : SiteCoverage.leafCount p148 = 458 := by
  exact count_node (l := p147) (r := p135) (a := 281) (b := 177) count147 count135
private theorem ann148 : annotate p148 = c148 := by
  exact ann_node (l := p147) (r := p135) (cl := c147) (cr := c135) (a := 281) count147 ann147 ann135

private def p149 : Tree := .node p106 p148
private def c149 : CTree := .node 56 c106 c148
private theorem count149 : SiteCoverage.leafCount p149 = 514 := by
  exact count_node (l := p106) (r := p148) (a := 56) (b := 458) count106 count148
private theorem ann149 : annotate p149 = c149 := by
  exact ann_node (l := p106) (r := p148) (cl := c106) (cr := c148) (a := 56) count106 ann106 ann148

private def p150 : Tree := .node p127 p094
private def c150 : CTree := .node 121 c127 c094
private theorem count150 : SiteCoverage.leafCount p150 = 201 := by
  exact count_node (l := p127) (r := p094) (a := 121) (b := 80) count127 count094
private theorem ann150 : annotate p150 = c150 := by
  exact ann_node (l := p127) (r := p094) (cl := c127) (cr := c094) (a := 121) count127 ann127 ann094

private def p151 : Tree := .node p091 p150
private def c151 : CTree := .node 123 c091 c150
private theorem count151 : SiteCoverage.leafCount p151 = 324 := by
  exact count_node (l := p091) (r := p150) (a := 123) (b := 201) count091 count150
private theorem ann151 : annotate p151 = c151 := by
  exact ann_node (l := p091) (r := p150) (cl := c091) (cr := c150) (a := 123) count091 ann091 ann150

private def p152 : Tree := .node p149 p151
private def c152 : CTree := .node 514 c149 c151
private theorem count152 : SiteCoverage.leafCount p152 = 838 := by
  exact count_node (l := p149) (r := p151) (a := 514) (b := 324) count149 count151
private theorem ann152 : annotate p152 = c152 := by
  exact ann_node (l := p149) (r := p151) (cl := c149) (cr := c151) (a := 514) count149 ann149 ann151

private def p153 : Tree := .node p144 p152
private def c153 : CTree := .node 4327 c144 c152
private theorem count153 : SiteCoverage.leafCount p153 = 5165 := by
  exact count_node (l := p144) (r := p152) (a := 4327) (b := 838) count144 count152
private theorem ann153 : annotate p153 = c153 := by
  exact ann_node (l := p144) (r := p152) (cl := c144) (cr := c152) (a := 4327) count144 ann144 ann152

private def p154 : Tree := .node p075 p153
private def c154 : CTree := .node 54 c075 c153
private theorem count154 : SiteCoverage.leafCount p154 = 5219 := by
  exact count_node (l := p075) (r := p153) (a := 54) (b := 5165) count075 count153
private theorem ann154 : annotate p154 = c154 := by
  exact ann_node (l := p075) (r := p153) (cl := c075) (cr := c153) (a := 54) count075 ann075 ann153

private def p155 : Tree := .node p094 p099
private def c155 : CTree := .node 80 c094 c099
private theorem count155 : SiteCoverage.leafCount p155 = 218 := by
  exact count_node (l := p094) (r := p099) (a := 80) (b := 138) count094 count099
private theorem ann155 : annotate p155 = c155 := by
  exact ann_node (l := p094) (r := p099) (cl := c094) (cr := c099) (a := 80) count094 ann094 ann099

private def p156 : Tree := .node p063 p155
private def c156 : CTree := .node 26 c063 c155
private theorem count156 : SiteCoverage.leafCount p156 = 244 := by
  exact count_node (l := p063) (r := p155) (a := 26) (b := 218) count063 count155
private theorem ann156 : annotate p156 = c156 := by
  exact ann_node (l := p063) (r := p155) (cl := c063) (cr := c155) (a := 26) count063 ann063 ann155

private def p157 : Tree := .node p154 p156
private def c157 : CTree := .node 5219 c154 c156
private theorem count157 : SiteCoverage.leafCount p157 = 5463 := by
  exact count_node (l := p154) (r := p156) (a := 5219) (b := 244) count154 count156
private theorem ann157 : annotate p157 = c157 := by
  exact ann_node (l := p154) (r := p156) (cl := c154) (cr := c156) (a := 5219) count154 ann154 ann156

private def p158 : Tree := .node p074 p157
private def c158 : CTree := .node 52 c074 c157
private theorem count158 : SiteCoverage.leafCount p158 = 5515 := by
  exact count_node (l := p074) (r := p157) (a := 52) (b := 5463) count074 count157
private theorem ann158 : annotate p158 = c158 := by
  exact ann_node (l := p074) (r := p157) (cl := c074) (cr := c157) (a := 52) count074 ann074 ann157

private def p159 : Tree := .node p063 p084
private def c159 : CTree := .node 26 c063 c084
private theorem count159 : SiteCoverage.leafCount p159 = 108 := by
  exact count_node (l := p063) (r := p084) (a := 26) (b := 82) count063 count084
private theorem ann159 : annotate p159 = c159 := by
  exact ann_node (l := p063) (r := p084) (cl := c063) (cr := c084) (a := 26) count063 ann063 ann084

private def p160 : Tree := .node (.leaf (.decnz 3)) p028
private def c160 : CTree := .node 1 (.leaf (.decnz 3)) c028
private theorem count160 : SiteCoverage.leafCount p160 = 4 := by
  exact count_node (l := (.leaf (.decnz 3))) (r := p028) (a := 1) (b := 3) (by rfl) count028
private theorem ann160 : annotate p160 = c160 := by
  exact ann_node (l := (.leaf (.decnz 3))) (r := p028) (cl := (.leaf (.decnz 3))) (cr := c028) (a := 1) (by rfl) (by rfl) ann028

private def p161 : Tree := .node p127 p160
private def c161 : CTree := .node 121 c127 c160
private theorem count161 : SiteCoverage.leafCount p161 = 125 := by
  exact count_node (l := p127) (r := p160) (a := 121) (b := 4) count127 count160
private theorem ann161 : annotate p161 = c161 := by
  exact ann_node (l := p127) (r := p160) (cl := c127) (cr := c160) (a := 121) count127 ann127 ann160

private def p162 : Tree := .node p127 p161
private def c162 : CTree := .node 121 c127 c161
private theorem count162 : SiteCoverage.leafCount p162 = 246 := by
  exact count_node (l := p127) (r := p161) (a := 121) (b := 125) count127 count161
private theorem ann162 : annotate p162 = c162 := by
  exact ann_node (l := p127) (r := p161) (cl := c127) (cr := c161) (a := 121) count127 ann127 ann161

private def p163 : Tree := .node p097 p162
private def c163 : CTree := .node 56 c097 c162
private theorem count163 : SiteCoverage.leafCount p163 = 302 := by
  exact count_node (l := p097) (r := p162) (a := 56) (b := 246) count097 count162
private theorem ann163 : annotate p163 = c163 := by
  exact ann_node (l := p097) (r := p162) (cl := c097) (cr := c162) (a := 56) count097 ann097 ann162

private def p164 : Tree := .node p159 p163
private def c164 : CTree := .node 108 c159 c163
private theorem count164 : SiteCoverage.leafCount p164 = 410 := by
  exact count_node (l := p159) (r := p163) (a := 108) (b := 302) count159 count163
private theorem ann164 : annotate p164 = c164 := by
  exact ann_node (l := p159) (r := p163) (cl := c159) (cr := c163) (a := 108) count159 ann159 ann163

private def p165 : Tree := .node p158 p164
private def c165 : CTree := .node 5515 c158 c164
private theorem count165 : SiteCoverage.leafCount p165 = 5925 := by
  exact count_node (l := p158) (r := p164) (a := 5515) (b := 410) count158 count164
private theorem ann165 : annotate p165 = c165 := by
  exact ann_node (l := p158) (r := p164) (cl := c158) (cr := c164) (a := 5515) count158 ann158 ann164

private def p166 : Tree := .node p073 p165
private def c166 : CTree := .node 79 c073 c165
private theorem count166 : SiteCoverage.leafCount p166 = 6004 := by
  exact count_node (l := p073) (r := p165) (a := 79) (b := 5925) count073 count165
private theorem ann166 : annotate p166 = c166 := by
  exact ann_node (l := p073) (r := p165) (cl := c073) (cr := c165) (a := 79) count073 ann073 ann165

private def p167 : Tree := .node p071 p166
private def c167 : CTree := .node 153 c071 c166
private theorem count167 : SiteCoverage.leafCount p167 = 6157 := by
  exact count_node (l := p071) (r := p166) (a := 153) (b := 6004) count071 count166
private theorem ann167 : annotate p167 = c167 := by
  exact ann_node (l := p071) (r := p166) (cl := c071) (cr := c166) (a := 153) count071 ann071 ann166

private def p168 : Tree := .node (.leaf (.decnz 5)) (.leaf (.cont 2))
private def c168 : CTree := .node 1 (.leaf (.decnz 5)) (.leaf (.cont 2))
private theorem count168 : SiteCoverage.leafCount p168 = 2 := by
  exact count_node (l := (.leaf (.decnz 5))) (r := (.leaf (.cont 2))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann168 : annotate p168 = c168 := by
  exact ann_node (l := (.leaf (.decnz 5))) (r := (.leaf (.cont 2))) (cl := (.leaf (.decnz 5))) (cr := (.leaf (.cont 2))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p169 : Tree := .node (.leaf (.inc 5)) p005
private def c169 : CTree := .node 1 (.leaf (.inc 5)) c005
private theorem count169 : SiteCoverage.leafCount p169 = 3 := by
  exact count_node (l := (.leaf (.inc 5))) (r := p005) (a := 1) (b := 2) (by rfl) count005
private theorem ann169 : annotate p169 = c169 := by
  exact ann_node (l := (.leaf (.inc 5))) (r := p005) (cl := (.leaf (.inc 5))) (cr := c005) (a := 1) (by rfl) (by rfl) ann005

private def p170 : Tree := .node p168 p169
private def c170 : CTree := .node 2 c168 c169
private theorem count170 : SiteCoverage.leafCount p170 = 5 := by
  exact count_node (l := p168) (r := p169) (a := 2) (b := 3) count168 count169
private theorem ann170 : annotate p170 = c170 := by
  exact ann_node (l := p168) (r := p169) (cl := c168) (cr := c169) (a := 2) count168 ann168 ann169

private def p171 : Tree := .node (.leaf (.decnz 6)) p170
private def c171 : CTree := .node 1 (.leaf (.decnz 6)) c170
private theorem count171 : SiteCoverage.leafCount p171 = 6 := by
  exact count_node (l := (.leaf (.decnz 6))) (r := p170) (a := 1) (b := 5) (by rfl) count170
private theorem ann171 : annotate p171 = c171 := by
  exact ann_node (l := (.leaf (.decnz 6))) (r := p170) (cl := (.leaf (.decnz 6))) (cr := c170) (a := 1) (by rfl) (by rfl) ann170

private def p172 : Tree := .node (.leaf (.decnz 5)) (.leaf (.cont 1))
private def c172 : CTree := .node 1 (.leaf (.decnz 5)) (.leaf (.cont 1))
private theorem count172 : SiteCoverage.leafCount p172 = 2 := by
  exact count_node (l := (.leaf (.decnz 5))) (r := (.leaf (.cont 1))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann172 : annotate p172 = c172 := by
  exact ann_node (l := (.leaf (.decnz 5))) (r := (.leaf (.cont 1))) (cl := (.leaf (.decnz 5))) (cr := (.leaf (.cont 1))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p173 : Tree := .node p172 (.leaf (.brk 1))
private def c173 : CTree := .node 2 c172 (.leaf (.brk 1))
private theorem count173 : SiteCoverage.leafCount p173 = 3 := by
  exact count_node (l := p172) (r := (.leaf (.brk 1))) (a := 2) (b := 1) count172 (by rfl)
private theorem ann173 : annotate p173 = c173 := by
  exact ann_node (l := p172) (r := (.leaf (.brk 1))) (cl := c172) (cr := (.leaf (.brk 1))) (a := 2) count172 ann172 (by rfl)

private def p174 : Tree := .node (.leaf (.decnz 5)) p173
private def c174 : CTree := .node 1 (.leaf (.decnz 5)) c173
private theorem count174 : SiteCoverage.leafCount p174 = 4 := by
  exact count_node (l := (.leaf (.decnz 5))) (r := p173) (a := 1) (b := 3) (by rfl) count173
private theorem ann174 : annotate p174 = c174 := by
  exact ann_node (l := (.leaf (.decnz 5))) (r := p173) (cl := (.leaf (.decnz 5))) (cr := c173) (a := 1) (by rfl) (by rfl) ann173

private def p175 : Tree := .node p171 p174
private def c175 : CTree := .node 6 c171 c174
private theorem count175 : SiteCoverage.leafCount p175 = 10 := by
  exact count_node (l := p171) (r := p174) (a := 6) (b := 4) count171 count174
private theorem ann175 : annotate p175 = c175 := by
  exact ann_node (l := p171) (r := p174) (cl := c171) (cr := c174) (a := 6) count171 ann171 ann174

private def p176 : Tree := .node (.leaf (.decnz 1)) (.leaf (.cont 1))
private def c176 : CTree := .node 1 (.leaf (.decnz 1)) (.leaf (.cont 1))
private theorem count176 : SiteCoverage.leafCount p176 = 2 := by
  exact count_node (l := (.leaf (.decnz 1))) (r := (.leaf (.cont 1))) (a := 1) (b := 1) (by rfl) (by rfl)
private theorem ann176 : annotate p176 = c176 := by
  exact ann_node (l := (.leaf (.decnz 1))) (r := (.leaf (.cont 1))) (cl := (.leaf (.decnz 1))) (cr := (.leaf (.cont 1))) (a := 1) (by rfl) (by rfl) (by rfl)

private def p177 : Tree := .node p175 p176
private def c177 : CTree := .node 10 c175 c176
private theorem count177 : SiteCoverage.leafCount p177 = 12 := by
  exact count_node (l := p175) (r := p176) (a := 10) (b := 2) count175 count176
private theorem ann177 : annotate p177 = c177 := by
  exact ann_node (l := p175) (r := p176) (cl := c175) (cr := c176) (a := 10) count175 ann175 ann176

private def p178 : Tree := .node (.leaf (.decnz 4)) p044
private def c178 : CTree := .node 1 (.leaf (.decnz 4)) c044
private theorem count178 : SiteCoverage.leafCount p178 = 3 := by
  exact count_node (l := (.leaf (.decnz 4))) (r := p044) (a := 1) (b := 2) (by rfl) count044
private theorem ann178 : annotate p178 = c178 := by
  exact ann_node (l := (.leaf (.decnz 4))) (r := p044) (cl := (.leaf (.decnz 4))) (cr := c044) (a := 1) (by rfl) (by rfl) ann044

private def p179 : Tree := .node p011 p178
private def c179 : CTree := .node 3 c011 c178
private theorem count179 : SiteCoverage.leafCount p179 = 6 := by
  exact count_node (l := p011) (r := p178) (a := 3) (b := 3) count011 count178
private theorem ann179 : annotate p179 = c179 := by
  exact ann_node (l := p011) (r := p178) (cl := c011) (cr := c178) (a := 3) count011 ann011 ann178

private def p180 : Tree := .node p177 p179
private def c180 : CTree := .node 12 c177 c179
private theorem count180 : SiteCoverage.leafCount p180 = 18 := by
  exact count_node (l := p177) (r := p179) (a := 12) (b := 6) count177 count179
private theorem ann180 : annotate p180 = c180 := by
  exact ann_node (l := p177) (r := p179) (cl := c177) (cr := c179) (a := 12) count177 ann177 ann179

private def p181 : Tree := .node p180 p177
private def c181 : CTree := .node 18 c180 c177
private theorem count181 : SiteCoverage.leafCount p181 = 30 := by
  exact count_node (l := p180) (r := p177) (a := 18) (b := 12) count180 count177
private theorem ann181 : annotate p181 = c181 := by
  exact ann_node (l := p180) (r := p177) (cl := c180) (cr := c177) (a := 18) count180 ann180 ann177

private def p182 : Tree := .node p167 p181
private def c182 : CTree := .node 6157 c167 c181
private theorem count182 : SiteCoverage.leafCount p182 = 6187 := by
  exact count_node (l := p167) (r := p181) (a := 6157) (b := 30) count167 count181
private theorem ann182 : annotate p182 = c182 := by
  exact ann_node (l := p167) (r := p181) (cl := c167) (cr := c181) (a := 6157) count167 ann167 ann181

private def p183 : Tree := .node p059 p182
private def c183 : CTree := .node 81 c059 c182
private theorem count183 : SiteCoverage.leafCount p183 = 6268 := by
  exact count_node (l := p059) (r := p182) (a := 81) (b := 6187) count059 count182
private theorem ann183 : annotate p183 = c183 := by
  exact ann_node (l := p059) (r := p182) (cl := c059) (cr := c182) (a := 81) count059 ann059 ann182

private def p184 : Tree := .node p183 (.leaf (.brk 1))
private def c184 : CTree := .node 6268 c183 (.leaf (.brk 1))
private theorem count184 : SiteCoverage.leafCount p184 = 6269 := by
  exact count_node (l := p183) (r := (.leaf (.brk 1))) (a := 6268) (b := 1) count183 (by rfl)
private theorem ann184 : annotate p184 = c184 := by
  exact ann_node (l := p183) (r := (.leaf (.brk 1))) (cl := c183) (cr := (.leaf (.brk 1))) (a := 6268) count183 ann183 (by rfl)

private def p185 : Tree := .node (.leaf (.decnz 3)) p184
private def c185 : CTree := .node 1 (.leaf (.decnz 3)) c184
private theorem count185 : SiteCoverage.leafCount p185 = 6270 := by
  exact count_node (l := (.leaf (.decnz 3))) (r := p184) (a := 1) (b := 6269) (by rfl) count184
private theorem ann185 : annotate p185 = c185 := by
  exact ann_node (l := (.leaf (.decnz 3))) (r := p184) (cl := (.leaf (.decnz 3))) (cr := c184) (a := 1) (by rfl) (by rfl) ann184

private def p186 : Tree := .node p175 (.leaf .halt)
private def c186 : CTree := .node 10 c175 (.leaf .halt)
private theorem count186 : SiteCoverage.leafCount p186 = 11 := by
  exact count_node (l := p175) (r := (.leaf .halt)) (a := 10) (b := 1) count175 (by rfl)
private theorem ann186 : annotate p186 = c186 := by
  exact ann_node (l := p175) (r := (.leaf .halt)) (cl := c175) (cr := (.leaf .halt)) (a := 10) count175 ann175 (by rfl)

private def p187 : Tree := .node p051 p045
private def c187 : CTree := .node 11 c051 c045
private theorem count187 : SiteCoverage.leafCount p187 = 14 := by
  exact count_node (l := p051) (r := p045) (a := 11) (b := 3) count051 count045
private theorem ann187 : annotate p187 = c187 := by
  exact ann_node (l := p051) (r := p045) (cl := c051) (cr := c045) (a := 11) count051 ann051 ann045

private def p188 : Tree := .node p186 p187
private def c188 : CTree := .node 11 c186 c187
private theorem count188 : SiteCoverage.leafCount p188 = 25 := by
  exact count_node (l := p186) (r := p187) (a := 11) (b := 14) count186 count187
private theorem ann188 : annotate p188 = c188 := by
  exact ann_node (l := p186) (r := p187) (cl := c186) (cr := c187) (a := 11) count186 ann186 ann187

private def p189 : Tree := .node (.leaf (.inc 6)) p188
private def c189 : CTree := .node 1 (.leaf (.inc 6)) c188
private theorem count189 : SiteCoverage.leafCount p189 = 26 := by
  exact count_node (l := (.leaf (.inc 6))) (r := p188) (a := 1) (b := 25) (by rfl) count188
private theorem ann189 : annotate p189 = c189 := by
  exact ann_node (l := (.leaf (.inc 6))) (r := p188) (cl := (.leaf (.inc 6))) (cr := c188) (a := 1) (by rfl) (by rfl) ann188

private def p190 : Tree := .node p185 p189
private def c190 : CTree := .node 6270 c185 c189
private theorem count190 : SiteCoverage.leafCount p190 = 6296 := by
  exact count_node (l := p185) (r := p189) (a := 6270) (b := 26) count185 count189
private theorem ann190 : annotate p190 = c190 := by
  exact ann_node (l := p185) (r := p189) (cl := c185) (cr := c189) (a := 6270) count185 ann185 ann189

private def p191 : Tree := .node p190 (.leaf (.brk 1))
private def c191 : CTree := .node 6296 c190 (.leaf (.brk 1))
private theorem count191 : SiteCoverage.leafCount p191 = 6297 := by
  exact count_node (l := p190) (r := (.leaf (.brk 1))) (a := 6296) (b := 1) count190 (by rfl)
private theorem ann191 : annotate p191 = c191 := by
  exact ann_node (l := p190) (r := (.leaf (.brk 1))) (cl := c190) (cr := (.leaf (.brk 1))) (a := 6296) count190 ann190 (by rfl)

private def p192 : Tree := .node (.leaf (.decnz 3)) p191
private def c192 : CTree := .node 1 (.leaf (.decnz 3)) c191
private theorem count192 : SiteCoverage.leafCount p192 = 6298 := by
  exact count_node (l := (.leaf (.decnz 3))) (r := p191) (a := 1) (b := 6297) (by rfl) count191
private theorem ann192 : annotate p192 = c192 := by
  exact ann_node (l := (.leaf (.decnz 3))) (r := p191) (cl := (.leaf (.decnz 3))) (cr := c191) (a := 1) (by rfl) (by rfl) ann191

private def p193 : Tree := .node p192 p047
private def c193 : CTree := .node 6298 c192 c047
private theorem count193 : SiteCoverage.leafCount p193 = 6324 := by
  exact count_node (l := p192) (r := p047) (a := 6298) (b := 26) count192 count047
private theorem ann193 : annotate p193 = c193 := by
  exact ann_node (l := p192) (r := p047) (cl := c192) (cr := c047) (a := 6298) count192 ann192 ann047

private def p194 : Tree := .node p193 (.leaf (.brk 1))
private def c194 : CTree := .node 6324 c193 (.leaf (.brk 1))
private theorem count194 : SiteCoverage.leafCount p194 = 6325 := by
  exact count_node (l := p193) (r := (.leaf (.brk 1))) (a := 6324) (b := 1) count193 (by rfl)
private theorem ann194 : annotate p194 = c194 := by
  exact ann_node (l := p193) (r := (.leaf (.brk 1))) (cl := c193) (cr := (.leaf (.brk 1))) (a := 6324) count193 ann193 (by rfl)

private def p195 : Tree := .node (.leaf (.decnz 3)) p194
private def c195 : CTree := .node 1 (.leaf (.decnz 3)) c194
private theorem count195 : SiteCoverage.leafCount p195 = 6326 := by
  exact count_node (l := (.leaf (.decnz 3))) (r := p194) (a := 1) (b := 6325) (by rfl) count194
private theorem ann195 : annotate p195 = c195 := by
  exact ann_node (l := (.leaf (.decnz 3))) (r := p194) (cl := (.leaf (.decnz 3))) (cr := c194) (a := 1) (by rfl) (by rfl) ann194

private def p196 : Tree := .node p069 p025
private def c196 : CTree := .node 53 c069 c025
private theorem count196 : SiteCoverage.leafCount p196 = 56 := by
  exact count_node (l := p069) (r := p025) (a := 53) (b := 3) count069 count025
private theorem ann196 : annotate p196 = c196 := by
  exact ann_node (l := p069) (r := p025) (cl := c069) (cr := c025) (a := 53) count069 ann069 ann025

private def p197 : Tree := .node p175 p068
private def c197 : CTree := .node 10 c175 c068
private theorem count197 : SiteCoverage.leafCount p197 = 36 := by
  exact count_node (l := p175) (r := p068) (a := 10) (b := 26) count175 count068
private theorem ann197 : annotate p197 = c197 := by
  exact ann_node (l := p175) (r := p068) (cl := c175) (cr := c068) (a := 10) count175 ann175 ann068

private def p198 : Tree := .node p196 p197
private def c198 : CTree := .node 56 c196 c197
private theorem count198 : SiteCoverage.leafCount p198 = 92 := by
  exact count_node (l := p196) (r := p197) (a := 56) (b := 36) count196 count197
private theorem ann198 : annotate p198 = c198 := by
  exact ann_node (l := p196) (r := p197) (cl := c196) (cr := c197) (a := 56) count196 ann196 ann197

private def p199 : Tree := .node p195 p198
private def c199 : CTree := .node 6326 c195 c198
private theorem count199 : SiteCoverage.leafCount p199 = 6418 := by
  exact count_node (l := p195) (r := p198) (a := 6326) (b := 92) count195 count198
private theorem ann199 : annotate p199 = c199 := by
  exact ann_node (l := p195) (r := p198) (cl := c195) (cr := c198) (a := 6326) count195 ann195 ann198

private def p200 : Tree := .node p024 p199
private def c200 : CTree := .node 14 c024 c199
private theorem count200 : SiteCoverage.leafCount p200 = 6432 := by
  exact count_node (l := p024) (r := p199) (a := 14) (b := 6418) count024 count199
private theorem ann200 : annotate p200 = c200 := by
  exact ann_node (l := p024) (r := p199) (cl := c024) (cr := c199) (a := 14) count024 ann024 ann199

private def p201 : Tree := .node p021 p200
private def c201 : CTree := .node 14 c021 c200
private theorem count201 : SiteCoverage.leafCount p201 = 6446 := by
  exact count_node (l := p021) (r := p200) (a := 14) (b := 6432) count021 count200
private theorem ann201 : annotate p201 = c201 := by
  exact ann_node (l := p021) (r := p200) (cl := c021) (cr := c200) (a := 14) count021 ann021 ann200

private def p202 : Tree := .node p008 p201
private def c202 : CTree := .node 9 c008 c201
private theorem count202 : SiteCoverage.leafCount p202 = 6455 := by
  exact count_node (l := p008) (r := p201) (a := 9) (b := 6446) count008 count201
private theorem ann202 : annotate p202 = c202 := by
  exact ann_node (l := p008) (r := p201) (cl := c008) (cr := c201) (a := 9) count008 ann008 ann201

def counted : CTree := c202

private theorem mirror_eq : p202 = TreeRotation240.tree := by rfl

theorem counted_eq : counted = annotate TreeRotation240.tree := by
  rw [← mirror_eq]
  exact ann202.symm

theorem leaf_count : SiteCoverage.leafCount TreeRotation240.tree = 6455 := by
  rw [← mirror_eq]
  exact count202

theorem catalogue_length : (leafEntries TreeRotation240.tree).length = 6455 := by
  rw [leafEntries_length, leaf_count]

end SetTheory.BusyBeaver.ZFC.CountedTreeRotation240
