#!/usr/bin/env python3
"""Generate L2Axioms222.lean: the AX routine of dag222 (node 236 and its chain 301..).

dag222's node 236 is a linear chain: node n = (atom, next), the last node = (atom, atom). The
atoms are the macro nodes of L2Macros222 (par1/2/3, pushwff, cons, wel, wal, weq, wn, wex,
readp2), the literal read (158 then 208, as nodes 35/46 of the 219-node program) and the gate
(192, 131, 211, 197, 131, as nodes 71-74). For every chain node this script emits

    def fN (st : AS) : AS := f<next> (atomF st)
    theorem lN (st : AS) (hc : Clean st) : Rn (.node N) st (fN st)
    theorem cN (st : AS) (hc : Clean st) : Clean (fN st)
    theorem eN (st : AS) : fN st = <closed form>

bottom-up; the closed forms come from an untrusted symbolic simulator (as in
generate_l2_axioms_eval.py) and are checked by Lean against the definitions. The final
theorem `ax_eval` identifies the composite with Enum222's AX step.

Usage: generate_l2axioms222.py DAG222_NODES_JSON OUT_LEAN"""
import json
import sys

src, out = sys.argv[1], sys.argv[2]
d = json.load(open(src))
nodes = {int(k): v for k, v in d["nodes"].items()}
FIELDS = ["np", "tw", "ws", "ac", "p1", "p2", "s1", "s2", "pl"]

# the chain from 236
chain, n = [], 236
while True:
    a, b = nodes[n]
    assert a[0] == "N"
    chain.append(n)
    if b[0] == "N" and b[1] >= 301 and b[1] not in chain:
        n = b[1]
        continue
    break
last = chain[-1]
atoms = [nodes[m][0][1] for m in chain] + [nodes[last][1][1]]
assert atoms == d["word236"], "chain atoms differ from the recorded word"

LEAF = {166: ("par1L", "par1F", "par1C"), 121: ("par2L", "par2F", "par2C"),
        168: ("par3L", "par3F", "par3C"), 171: ("pushL", "pushF", "pushC"),
        119: ("consL", "consF", "consC"), 181: ("welL", "welF", "welC"),
        180: ("walL", "walF", "walC"), 182: ("weqL", "weqF", "weqC"),
        218: ("wnL", "wnF", "wnC"), 178: ("waL", "waF", "waC"),
        183: ("wexL", "wexF", "wexC"), 176: ("readp2L", "readp2F", "readp2C")}

# locate the literal read (158, 208) and the gate (192, 131, 211, 197, 131)
pos = {m: i for i, m in enumerate(chain)}
read_i = [i for i in range(len(atoms) - 1) if atoms[i] == 158]
assert len(read_i) == 1 and atoms[read_i[0] + 1] == 208
R = read_i[0]
assert atoms[-5:] == [192, 131, 211, 197, 131]
G = len(chain) - 4                 # chain[G] = (192, chain[G+1]), ..., chain[G+3] = (197, 131)
assert [nodes[chain[G + k]][0][1] for k in range(4)] == [192, 131, 211, 197]
other = set(atoms[:R] + atoms[R + 2:G])
assert other <= set(LEAF), sorted(other - set(LEAF))

# ---------- symbolic simulator (untrusted) ----------


def show(e):
    k = e[0]
    if k == "var":
        return e[1]
    if k == "lit":
        return str(e[1])
    if k == "P":
        return f"P {arg(e[1])} {arg(e[2])}"
    if k in ("wim", "wel", "wal", "weq", "wa", "wex"):
        return f"{k} {arg(e[1])} {arg(e[2])}"
    if k == "wn":
        return f"wn {arg(e[1])}"
    if k == "fst":
        return f"(Cantor.ofNat {arg(e[1])}).1"
    if k == "snd":
        return f"(Cantor.ofNat {arg(e[1])}).2"
    if k == "add":
        return f"{show(e[1])} + {arg(e[2])}"
    if k == "gate":
        return f"if {show(e[1])} = {show(e[2])} ∨ {show(e[1])} = {show(e[3])} then 0 else {show(e[4])}"
    raise ValueError(e)


def arg(e):
    s = show(e)
    return s if e[0] in ("var", "lit") or s.startswith("(") else f"({s})"


def fst(e):
    return e[1] if e[0] == "P" else ("fst", e)


def snd(e):
    return e[2] if e[0] == "P" else ("snd", e)


def add(a, b):
    if b == ("lit", 0):
        return a
    if a == ("lit", 0):
        return b
    return ("add", a, b)


def macro(name, st):
    st = dict(st)
    if name == "pushF":
        st["ws"], st["tw"] = ("P", st["tw"], st["ws"]), ("lit", 0)
    elif name in ("par1F", "par2F", "par3F"):
        srcf = {"par1F": "p1", "par2F": "p2", "par3F": "ac"}[name]
        st["ws"], st["tw"] = ("P", st["tw"], st["ws"]), st[srcf]
    elif name in ("consF", "welF", "walF", "weqF", "waF", "wexF"):
        op = {"consF": "wim", "welF": "wel", "walF": "wal", "weqF": "weq", "waF": "wa", "wexF": "wex"}[name]
        top, rest = fst(st["ws"]), snd(st["ws"])
        st["tw"], st["ws"] = (op, top, st["tw"]), rest
    elif name == "wnF":
        st["tw"] = ("wn", st["tw"])
    elif name == "readp2F":
        x = fst(st["pl"])
        st["pl"], st["p2"] = snd(st["pl"]), add(st["p2"], x)
    elif name == "readTw":
        x = fst(st["pl"])
        st["pl"], st["tw"], st["s1"] = snd(st["pl"]), add(st["tw"], x), ("lit", 0)
    elif name == "gateF":
        st["tw"] = ("gate", st["ac"], st["p1"], st["p2"], st["tw"])
        st["ac"], st["p1"], st["p2"] = ("lit", 0), ("lit", 0), ("lit", 0)
    else:
        raise ValueError(name)
    return st


def effect(i, st):
    """the effect of the chain from chain index i to the end"""
    while i < len(chain):
        if i == G:
            return macro("gateF", st)
        if i == R:
            st = macro("readTw", st)
            i += 2
            continue
        st = macro(LEAF[atoms[i]][1], st)
        i += 1
    raise AssertionError


generic = {f: ("var", f"st.{f}") for f in FIELDS}

# ---------- emit ----------
L = []
w = L.append
w("import BusyBeaver.ZFC.L2Control222")
w("import BusyBeaver.ZFC.Enum222")
w("")
w("/-!")
w("The AX routine of `dag222` (node 236 and its chain), L2 part 4 for the 222/221.")
w("")
w("Generated by `Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2axioms222.py`.")
w("Node 236 is a chain of macro atoms; each chain node gets its effect (`fN`), its run (`lN`),")
w("cleanliness (`cN`) and a closed form (`eN`) from an untrusted simulator, which Lean checks")
w("against the definitions bottom-up. `ax_eval` is Enum222's AX step: the stack becomes")
w("`Enum222.axStack` (rho6 a c, the merged row G in rho7's slot) and the current formula the")
w("gated seed bundle.")
w("-/")
w("")
w("namespace SetTheory.BusyBeaver.ZFC.L2K")
w("")
w("open RMDag Dag222 Code254 KCode222")
w("")
w("attribute [local irreducible] Code254.P")
w("")
w("set_option linter.unusedSimpArgs false")
w("set_option maxRecDepth 4096")
w("")
w("""def pushF (st : AS) : AS := { st with tw := 0, ws := P st.tw st.ws }
def par1F (st : AS) : AS := { st with tw := st.p1, ws := P st.tw st.ws }
def par2F (st : AS) : AS := { st with tw := st.p2, ws := P st.tw st.ws }
def par3F (st : AS) : AS := { st with tw := st.ac, ws := P st.tw st.ws }
def consF (st : AS) : AS :=
  { st with tw := wim (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def welF (st : AS) : AS :=
  { st with tw := wel (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def walF (st : AS) : AS :=
  { st with tw := wal (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def weqF (st : AS) : AS :=
  { st with tw := weq (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def wnF (st : AS) : AS := { st with tw := wn st.tw }
def waF (st : AS) : AS :=
  { st with tw := wa (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def wexF (st : AS) : AS :=
  { st with tw := wex (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }
def readp2F (st : AS) : AS :=
  { st with pl := (Cantor.ofNat st.pl).2, p2 := st.p2 + (Cantor.ofNat st.pl).1 }

theorem pushL (st : AS) (hc : Clean st) : Rn (.node 171) st (pushF st) := pushwff st hc
theorem par1L (st : AS) (hc : Clean st) : Rn (.node 166) st (par1F st) := par1 st hc
theorem par2L (st : AS) (hc : Clean st) : Rn (.node 121) st (par2F st) := par2 st hc
theorem par3L (st : AS) (hc : Clean st) : Rn (.node 168) st (par3F st) := par3 st hc
theorem consL (st : AS) (hc : Clean st) : Rn (.node 119) st (consF st) := cons st hc
theorem welL (st : AS) (hc : Clean st) : Rn (.node 181) st (welF st) := wel_m st hc
theorem walL (st : AS) (hc : Clean st) : Rn (.node 180) st (walF st) := wal_m st hc
theorem weqL (st : AS) (hc : Clean st) : Rn (.node 182) st (weqF st) := weq_m st hc
theorem wnL (st : AS) (hc : Clean st) : Rn (.node 218) st (wnF st) := wn_m st hc
theorem waL (st : AS) (hc : Clean st) : Rn (.node 178) st (waF st) := wa_m st hc
theorem wexL (st : AS) (hc : Clean st) : Rn (.node 183) st (wexF st) := wex_m st hc
theorem readp2L (st : AS) (hc : Clean st) : Rn (.node 176) st (readp2F st) := read_p2 st hc

theorem pushC (st : AS) (hc : Clean st) : Clean (pushF st) := hc
theorem par1C (st : AS) (hc : Clean st) : Clean (par1F st) := hc
theorem par2C (st : AS) (hc : Clean st) : Clean (par2F st) := hc
theorem par3C (st : AS) (hc : Clean st) : Clean (par3F st) := hc
theorem consC (st : AS) (hc : Clean st) : Clean (consF st) := hc
theorem welC (st : AS) (hc : Clean st) : Clean (welF st) := hc
theorem walC (st : AS) (hc : Clean st) : Clean (walF st) := hc
theorem weqC (st : AS) (hc : Clean st) : Clean (weqF st) := hc
theorem wnC (st : AS) (hc : Clean st) : Clean (wnF st) := hc
theorem waC (st : AS) (hc : Clean st) : Clean (waF st) := hc
theorem wexC (st : AS) (hc : Clean st) : Clean (wexF st) := hc
theorem readp2C (st : AS) (hc : Clean st) : Clean (readp2F st) := hc

/-- The gate: clear the bundle when `c = b` or `c = a`, and clear `axiomcode`, `param1`,
`param2`. -/
def gateF (st : AS) : AS :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

theorem gateC (st : AS) (hc : Clean st) : Clean (gateF st) := hc
""")
g0, g1, g2, g3 = chain[G], chain[G + 1], chain[G + 2], chain[G + 3]
w(f"""theorem l{g0} (st : AS) (hc : Clean st) : Rn (.node {g0}) st (gateF st) := by
  have := seqAS (n := {g0}) rfl (loop192 st) (seqAS (n := {g1}) rfl (ifeq_clear _)
    (seqAS (n := {g2}) rfl (loop211 _) (seqAS (n := {g3}) rfl (loop197 _) (ifeq_clear _))))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st
  simp only at h1 h2
  subst h1; subst h2
  simp only [gateF, Nat.zero_add]
  split <;> split <;> simp_all <;> omega
""")


def fname(i):
    return "gateF" if i == G else f"f{chain[i]}"


def lname(i):
    return f"l{chain[i]}"


def cname(i):
    return "gateC" if i == G else f"c{chain[i]}"


def ename(i):
    return "gateF" if i == G else f"e{chain[i]}"


# bottom-up over chain indices G-1 .. 0, skipping the second node of the read
for i in range(G - 1, -1, -1):
    if i == R + 1:
        continue
    m = chain[i]
    if i == R:
        m2 = chain[R + 1]
        nxt = R + 2
        w(f"/-- the literal read into topwff (atoms 158, 208) -/")
        w(f"def f{m2} (st : AS) : AS := {fname(nxt)} {{ st with tw := st.tw + st.s1, s1 := 0 }}")
        w(f"theorem l{m2} (st : AS) (h2 : st.s2 = 0) : Rn (.node {m2}) st (f{m2} st) :=")
        w(f"  seqAS (n := {m2}) rfl (loop208 st) ({lname(nxt)} _ ⟨rfl, h2⟩)")
        w(f"theorem c{m2} (st : AS) (h2 : st.s2 = 0) : Clean (f{m2} st) := {cname(nxt)} _ ⟨rfl, h2⟩")
        w(f"def f{m} (st : AS) : AS := f{m2} {{ st with pl := (Cantor.ofNat st.pl).2, s1 := (Cantor.ofNat st.pl).1 }}")
        w(f"theorem l{m} (st : AS) (hc : Clean st) : Rn (.node {m}) st (f{m} st) :=")
        w(f"  seqAS (n := {m}) rfl (read108 st hc) (l{m2} _ hc.2)")
        w(f"theorem c{m} (st : AS) (hc : Clean st) : Clean (f{m} st) := c{m2} _ hc.2")
    else:
        lf, ff, cf = LEAF[atoms[i]]
        nxt = i + 1
        w(f"def f{m} (st : AS) : AS := {fname(nxt)} ({ff} st)")
        w(f"theorem l{m} (st : AS) (hc : Clean st) : Rn (.node {m}) st (f{m} st) :=")
        w(f"  seqAS (n := {m}) rfl ({lf} st hc) ({lname(nxt)} _ ({cf} st hc))")
        w(f"theorem c{m} (st : AS) (hc : Clean st) : Clean (f{m} st) := {cname(nxt)} _ ({cf} st hc)")
    res = effect(i, generic)
    fields = ", ".join(show(res[f]) for f in FIELDS)
    w(f"theorem e{m} (st : AS) : f{m} st = ⟨{fields}⟩ := by")
    if i == R:
        w(f"  simp only [f{m}, f{chain[R + 1]}, {ename(R + 2)}, ofNat_P, Nat.zero_add]")
    else:
        w(f"  simp only [f{m}, {LEAF[atoms[i]][1]}, {ename(i + 1)}, ofNat_P, Nat.zero_add]")
    w("")

w("""/-- **The AX routine is Enum222's AX step.** -/
theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, Enum222.gate a (h + (Cantor.ofNat pl).1) c,
        Enum222.axStack a h (h + (Cantor.ofNat pl).1) c (Cantor.ofNat (Cantor.ofNat pl).2).1 t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  rw [e236]
  simp only [Enum222.gate, Enum222.axStack, bundle222, nks, clos, req, vrel, growG, rho1, rho2,
    rho3, rho4, rho5, rho6, rho8, wa, wex]

end SetTheory.BusyBeaver.ZFC.L2K
""")
open(out, "w", encoding="utf-8", newline="\n").write("\n".join(L))
print("wrote", out, "chain", len(chain), "read at", R, "gate at", G)
