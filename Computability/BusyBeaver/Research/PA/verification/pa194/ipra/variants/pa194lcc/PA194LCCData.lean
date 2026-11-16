import PA194LCData
set_option autoImplicit false
set_option maxRecDepth 65536
namespace PA194LCCData

def labels : List Nat := [
74,0,64,94,66,198,54,40,113,4,302,97,
6,10,16,1,2,3,5,9,15,23,34,75,
84,53,310,68,69,214,62,77,213,31,188,312,
28,73,87,88,92,90,21,47,95,111,11,38,
331,42,82,83,301,122,103,104,185,105,106,24,
60,63,27,110,128,26,18,20,30,46,13,49,
33,93,45,137,108,123,124,107,98,72,59,58,
125,35,55,39,127,8,141,194,96,61,91,32,
109,70,138,126,19,114,56,81,71,139,22,36,
14,161,17,101,100,25,48,130,29,51,57,80,
330,2000,174,164,144,43,44,99,2001,2033,2002,2005,
2034,2039,12,2003,2006,2023,2025,2035,2052,2040,2004,2007,
2014,2046,2029,2026,2036,166,2041,2066,2008,2050,2064,2028,
2030,2031,2027,2015,179,2042,2047,221,2009,2019,2051,2065,
2032,2020,2044,2017,2043,2048,2053,196,217,2010,2011,2059,
2056,2061,2021,2045,2049,2054,197,2012,2063,2057,2058,2062,
2038,2013,254
]
def rows : List PA194BRows.Action := [
(1,1,1),(1,1,2),(1,1,3),(1,1,1),(0,1,0),(1,1,2),(0,1,4),(0,1,1),(1,1,5),(1,0,6),(1,0,7),(1,0,8),
(0,0,7),(1,0,6),(0,0,9),(1,0,6),(0,0,10),(0,0,11),(1,1,12),(0,0,9),(0,0,9),(0,0,10),(1,0,8),(1,0,11),
(0,1,12),(0,1,13),(0,0,14),(0,1,13),(1,0,15),(0,0,15),(0,0,15),(1,0,16),(0,0,17),(1,0,16),(0,0,18),(1,0,16),
(0,0,19),(1,0,16),(0,0,20),(1,0,16),(0,0,21),(1,0,16),(0,0,22),(1,0,16),(0,0,23),(1,0,16),(0,1,23),(1,1,24),
(0,1,25),(1,1,26),(0,1,27),(1,1,28),(0,1,29),(1,1,30),(0,1,31),(1,1,194),(0,0,32),(1,1,33),(0,1,34),(1,1,35),
(0,0,36),(1,0,37),(0,1,38),(1,1,39),(0,1,40),(1,1,41),(0,1,42),(1,1,43),(0,1,44),(1,1,45),(0,1,46),(1,1,47),
(0,1,48),(1,1,49),(0,1,50),(1,1,51),(0,1,52),(1,1,42),(0,1,53),(1,1,54),(0,1,55),(1,1,56),(0,1,57),(1,1,58),
(0,1,59),(0,1,60),(0,1,61),(0,0,14),(0,1,62),(1,1,63),(0,1,55),(1,1,64),(0,0,65),(1,1,66),(0,1,36),(1,1,67),
(0,0,68),(1,0,69),(0,1,70),(0,0,14),(0,1,71),(0,1,72),(0,1,73),(0,0,49),(0,1,74),(1,1,54),(0,0,75),(0,0,15),
(0,1,76),(0,0,10),(0,1,77),(1,1,78),(0,1,79),(1,1,80),(0,1,81),(1,1,82),(0,1,83),(1,1,84),(0,0,85),(0,1,1),
(0,1,86),(1,1,60),(0,0,77),(1,0,68),(0,1,87),(0,0,7),(0,1,88),(1,1,89),(0,1,42),(1,1,90),(0,1,91),(1,1,49),
(0,1,92),(0,0,76),(0,1,68),(1,1,33),(0,1,74),(1,1,69),(0,1,93),(1,1,30),(0,0,94),(1,0,33),(0,0,85),(0,1,2),
(0,1,95),(1,1,72),(0,1,76),(1,1,96),(0,1,59),(0,1,86),(0,1,68),(1,1,97),(0,1,42),(0,0,13),(0,1,87),(1,1,37),
(0,1,30),(1,1,98),(0,1,42),(1,1,99),(0,1,100),(1,1,101),(0,1,102),(1,0,103),(0,1,30),(1,1,81),(0,1,97),(1,1,104),
(0,1,30),(1,1,105),(1,1,85),(1,0,15),(0,1,106),(1,1,86),(0,0,46),(0,1,107),(0,1,108),(1,1,98),(0,1,108),(1,1,70),
(0,1,109),(0,0,14),(0,1,110),(1,0,75),(0,1,111),(1,1,112),(0,1,71),(0,1,113),(0,1,50),(1,1,103),(0,1,114),(1,1,95),
(0,1,30),(1,1,49),(0,1,48),(1,1,61),(0,1,87),(1,0,115),(0,1,104),(0,0,14),(0,1,36),(1,1,116),(0,1,115),(1,1,79),
(0,0,46),(0,1,117),(0,0,45),(1,1,118),(0,0,94),(1,1,119),(0,1,120),(1,1,48),(0,1,72),(1,1,106),(0,1,117),(1,1,107),
(0,0,46),(0,1,106),(0,1,71),(0,1,95),(0,1,59),(0,1,95),(0,0,65),(1,1,121),(0,1,122),(1,1,123),(0,1,107),(1,1,113),
(0,1,113),(1,1,114),(0,1,124),(1,0,67),(0,1,125),(1,1,126),(0,1,14),(1,1,117),(0,1,93),(0,0,14),(0,1,94),(1,0,98),
(0,1,127),(1,1,93),(0,1,128),(1,1,129),(0,1,32),(1,1,36),(0,1,31),(1,1,80),(0,1,59),(0,1,114),(0,1,102),(1,1,118),
(0,1,83),(1,1,82),(0,1,93),(1,1,93),(0,1,130),(1,1,131),(0,1,132),(1,1,133),(0,1,134),(1,1,135),(0,1,136),(1,1,137),
(0,1,138),(1,1,139),(0,1,140),(1,1,141),(0,1,100),(1,1,67),(0,1,142),(1,1,127),(0,1,143),(1,1,144),(0,1,145),(1,1,146),
(0,1,134),(1,1,147),(0,1,93),(1,1,148),(0,1,149),(1,0,131),(0,1,150),(1,1,151),(0,1,80),(1,1,41),(0,1,28),(1,1,152),
(0,0,153),(1,0,154),(0,0,129),(1,1,155),(0,1,156),(1,1,157),(0,1,149),(1,1,158),(0,1,159),(1,1,93),(0,1,100),(1,1,160),
(0,1,161),(1,1,162),(0,1,163),(0,0,10),(0,1,164),(1,1,165),(0,1,166),(1,1,157),(0,1,167),(1,1,156),(0,1,135),(1,1,130),
(0,1,147),(1,1,41),(0,1,134),(1,1,168),(0,1,41),(1,0,169),(0,0,170),(1,1,171),(0,1,91),(1,1,64),(0,1,172),(1,1,170),
(0,1,173),(1,1,174),(0,1,175),(1,1,176),(0,1,177),(1,1,178),(0,0,179),(1,0,180),(0,1,149),(1,1,140),(0,1,165),(1,1,181),
(0,0,130),(1,1,93),(0,1,182),(1,1,135),(0,1,183),(1,1,145),(0,1,158),(1,1,130),(0,1,139),(1,1,165),(0,1,158),(1,1,184),
(0,1,185),(1,1,91),(0,1,31),(1,1,53),(0,1,186),(1,1,175),(0,1,134),(1,1,142),(0,1,32),(1,1,187),(0,1,144),(1,1,188),
(0,1,189),(1,1,190),(0,1,41),(1,1,191),(0,1,168),(1,1,41),(0,1,192),(1,1,93),(0,1,153),(1,1,146),(0,1,165),(1,1,180),
(0,1,96),(1,1,115),(0,1,193),(1,1,159),(0,1,169),(1,1,154),(0,1,158),(1,1,192),(0,1,179),(1,1,182),(0,1,182),(1,1,41),
(0,1,149),(1,1,168),(0,1,80),(1,1,144)
]
def table : ConPA.Machine.Table := PA194BModelSteps.table rows
/-- Exact LC_C native machine, reusing every unchanged LC native row. -/
def machine (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  if q = 41 ∨ q = 190 then none
  else if q = 28 ∧ b = false then some (false,true,331)
  else if q = 70 ∧ b = false then some (false,true,331)
  else if q = 139 then if b then some (true,true,331) else some (false,true,330)
  else if q = 330 then if b then some (true,true,61) else some (false,true,99)
  else if q = 331 then if b then some (true,false,46) else some (false,false,30)
  else PA194LCData.machine q b

def denseControl (q : Nat) : Nat := labels.idxOf q

def newSourceNode0 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode82 PA194LCData.sourceNode58
def newSourceNode1 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode58 PA194LCData.sourceNode22
def newSourceNode2 : M6.Source.PathTrie.Tree := .node newSourceNode0 newSourceNode1
def newSourceNode3 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode17 newSourceNode2
def newSourceNode4 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode67 newSourceNode3
def newSourceNode5 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode29 newSourceNode4
def newSourceNode6 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode81 newSourceNode5
def newSourceNode7 : M6.Source.PathTrie.Tree := .node newSourceNode6 PA194LCData.sourceNode82
def newSourceNode8 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode74 newSourceNode7
def newSourceNode9 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode74 newSourceNode6
def newSourceNode10 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode94 newSourceNode5
def newSourceNode11 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode74 newSourceNode5
def newSourceNode12 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode81 newSourceNode11
def newSourceNode13 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode100 newSourceNode11
def newSourceNode14 : M6.Source.PathTrie.Tree := .node newSourceNode5 newSourceNode5
def newSourceNode15 : M6.Source.PathTrie.Tree := .node newSourceNode14 newSourceNode8
def newSourceNode16 : M6.Source.PathTrie.Tree := .node newSourceNode13 newSourceNode15
def newSourceNode17 : M6.Source.PathTrie.Tree := .node newSourceNode12 newSourceNode16
def newSourceNode18 : M6.Source.PathTrie.Tree := .node newSourceNode10 newSourceNode17
def newSourceNode19 : M6.Source.PathTrie.Tree := .node newSourceNode9 newSourceNode18
def newSourceNode20 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode108 newSourceNode5
def newSourceNode21 : M6.Source.PathTrie.Tree := .node newSourceNode20 newSourceNode7
def newSourceNode22 : M6.Source.PathTrie.Tree := .node newSourceNode21 newSourceNode20
def newSourceNode23 : M6.Source.PathTrie.Tree := .node newSourceNode19 newSourceNode22
def newSourceNode24 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode91 newSourceNode23
def newSourceNode25 : M6.Source.PathTrie.Tree := .node newSourceNode24 newSourceNode11
def newSourceNode26 : M6.Source.PathTrie.Tree := .node newSourceNode5 PA194LCData.sourceNode82
def newSourceNode27 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode100 newSourceNode26
def newSourceNode28 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode74 newSourceNode27
def newSourceNode29 : M6.Source.PathTrie.Tree := .node newSourceNode7 newSourceNode8
def newSourceNode30 : M6.Source.PathTrie.Tree := .node newSourceNode28 newSourceNode29
def newSourceNode31 : M6.Source.PathTrie.Tree := .node newSourceNode27 newSourceNode5
def newSourceNode32 : M6.Source.PathTrie.Tree := .node newSourceNode6 PA194LCData.sourceNode58
def newSourceNode33 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode74 newSourceNode32
def newSourceNode34 : M6.Source.PathTrie.Tree := .node newSourceNode31 newSourceNode33
def newSourceNode35 : M6.Source.PathTrie.Tree := .node newSourceNode30 newSourceNode34
def newSourceNode36 : M6.Source.PathTrie.Tree := .node newSourceNode25 newSourceNode35
def newSourceNode37 : M6.Source.PathTrie.Tree := .node newSourceNode8 newSourceNode36
def newSourceNode38 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode100 newSourceNode32
def newSourceNode39 : M6.Source.PathTrie.Tree := .node newSourceNode38 newSourceNode15
def newSourceNode40 : M6.Source.PathTrie.Tree := .node newSourceNode39 PA194LCData.sourceNode58
def newSourceNode41 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode58 newSourceNode40
def newSourceNode42 : M6.Source.PathTrie.Tree := .node newSourceNode28 newSourceNode41
def newSourceNode43 : M6.Source.PathTrie.Tree := .node newSourceNode41 newSourceNode22
def newSourceNode44 : M6.Source.PathTrie.Tree := .node newSourceNode38 PA194LCData.sourceNode58
def newSourceNode45 : M6.Source.PathTrie.Tree := .node newSourceNode13 newSourceNode29
def newSourceNode46 : M6.Source.PathTrie.Tree := .node newSourceNode44 newSourceNode45
def newSourceNode47 : M6.Source.PathTrie.Tree := .node newSourceNode43 newSourceNode46
def newSourceNode48 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode100 newSourceNode34
def newSourceNode49 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode100 newSourceNode48
def newSourceNode50 : M6.Source.PathTrie.Tree := .node newSourceNode49 newSourceNode33
def newSourceNode51 : M6.Source.PathTrie.Tree := .node newSourceNode50 newSourceNode34
def newSourceNode52 : M6.Source.PathTrie.Tree := .node newSourceNode14 newSourceNode51
def newSourceNode53 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode100 newSourceNode38
def newSourceNode54 : M6.Source.PathTrie.Tree := .node newSourceNode14 newSourceNode38
def newSourceNode55 : M6.Source.PathTrie.Tree := .node newSourceNode20 newSourceNode5
def newSourceNode56 : M6.Source.PathTrie.Tree := .node newSourceNode5 newSourceNode55
def newSourceNode57 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode100 newSourceNode56
def newSourceNode58 : M6.Source.PathTrie.Tree := .node newSourceNode53 newSourceNode56
def newSourceNode59 : M6.Source.PathTrie.Tree := .node newSourceNode58 newSourceNode31
def newSourceNode60 : M6.Source.PathTrie.Tree := .node newSourceNode21 newSourceNode59
def newSourceNode61 : M6.Source.PathTrie.Tree := .node newSourceNode57 newSourceNode60
def newSourceNode62 : M6.Source.PathTrie.Tree := .node newSourceNode61 newSourceNode20
def newSourceNode63 : M6.Source.PathTrie.Tree := .node newSourceNode54 newSourceNode62
def newSourceNode64 : M6.Source.PathTrie.Tree := .node newSourceNode53 newSourceNode63
def newSourceNode65 : M6.Source.PathTrie.Tree := .node newSourceNode64 PA194LCData.sourceNode154
def newSourceNode66 : M6.Source.PathTrie.Tree := .node newSourceNode52 newSourceNode65
def newSourceNode67 : M6.Source.PathTrie.Tree := .node newSourceNode47 newSourceNode66
def newSourceNode68 : M6.Source.PathTrie.Tree := .node newSourceNode67 PA194LCData.sourceNode164
def newSourceNode69 : M6.Source.PathTrie.Tree := .node newSourceNode13 newSourceNode68
def newSourceNode70 : M6.Source.PathTrie.Tree := .node newSourceNode42 newSourceNode69
def newSourceNode71 : M6.Source.PathTrie.Tree := .node newSourceNode37 newSourceNode70
def newSourceNode72 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode55 newSourceNode71
def newSourceNode73 : M6.Source.PathTrie.Tree := .node newSourceNode10 PA194LCData.sourceNode57
def newSourceNode74 : M6.Source.PathTrie.Tree := .node newSourceNode73 PA194LCData.sourceNode171
def newSourceNode75 : M6.Source.PathTrie.Tree := .node newSourceNode72 newSourceNode74
def newSourceNode76 : M6.Source.PathTrie.Tree := .node newSourceNode75 PA194LCData.sourceNode22
def newSourceNode77 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode55 newSourceNode76
def newSourceNode78 : M6.Source.PathTrie.Tree := .node newSourceNode77 PA194LCData.sourceNode176
def newSourceNode79 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode54 newSourceNode78
def newSourceNode80 : M6.Source.PathTrie.Tree := .node newSourceNode79 PA194LCData.sourceNode39
def newSourceNode81 : M6.Source.PathTrie.Tree := .node PA194LCData.sourceNode34 newSourceNode80

def sourceTrie : M6.Source.PathTrie.Tree := newSourceNode81
def path (i : Nat) : M6.Source.Path := ((M6.Source.PathTrie.nthSite sourceTrie i).map (·.path)).getD []
def codeAt (i : Nat) : Option M6.Source.Instruction := (M6.Source.PathTrie.nthSite sourceTrie i).bind (M6.FastResolve.resolveTree sourceTrie)
end PA194LCCData
