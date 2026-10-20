"""Independent emitter check for the stacked B+C source (generalized: host word from a JSON field).

(1) Symbolic: with the 224 package's pinned executor (check_emitter.py), A's conditional
    bundle word with B's tail rule (omit H, one conjunction) emits And(Kc, RV), where Kc is the
    word's core and equals A's recorded conditional core; B's G row emits G.
(2) Literal: the combined source's primitive leaf sequence equals A's, with exactly two word
    substitutions (old rho7 row -> G at its unique place; A's bundle word -> new bundle word
    at its unique place); macro leaves use B's bindings of the Dag230 atoms to parent225 decoder subtrees.
Usage: verify_ab_emitter.py A_SITES COMBINED_SITES A_BINDING_JSON"""
import hashlib, importlib.util, json, sys
from pathlib import Path

S = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad")
K224 = S / "intake181/fresh/K224_Construction_2026-10-20/K224_Construction_2026-10-20/portable"
sys.path.insert(0, str(S / "intake179/fresh/K225_Construction_2026-10-19/K225_Construction_2026-10-19/portable/baseline226/verification"))
sys.path.insert(0, str(K224 / "verification"))
import reconstruct227 as c
import construct_rel225 as cr

em = K224 / "verification/check_emitter.py"
assert hashlib.sha256(em.read_bytes()).hexdigest() == "32fa8462a8ab95fbcd2969faf915f0a6fb872484723ae355297624c5d843d93f"
spec = importlib.util.spec_from_file_location("pinned_old_emitter", em)
old = importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
I, R, Q, E, N, A = old.I, old.R, old.Q, old.E, old.N, old.A

asrc = c.tree(json.loads(Path(sys.argv[1]).read_text()))
csrc = c.tree(json.loads(Path(sys.argv[2]).read_text()))
bind = json.load(open(sys.argv[3]))
a_word = bind.get("new_full_word") or bind.get("canonical_word") or bind["macro_word"]

old_r7 = [168, 166, 182, 168, 121, 182, 166, 121, 182, 119, 119]
new_g = [168, 166, 182, 168, 121, 182, 166, 121, 181, 166, 121, 182, 180, 119, 119]
assert old.execute(old_r7) == I(E("c", "a"), I(E("c", "b"), E("a", "b")))
assert old.execute(new_g) == I(E("c", "a"), I(E("c", "b"), Q(R("a", "b"), E("a", "b"))))
rv_word = [166, 121, 181, 168, 166, 121, 181, 180, 119]
h_word = [166, 121, 182, 166, 121, 181, 166, 121, 182, 180, 119]
rv = I(R("a", "b"), Q("c", R("a", "b")))
h = I(E("a", "b"), Q(R("a", "b"), E("a", "b")))
if a_word[-len(rv_word + h_word + [218, 119, 119, 218]):] == rv_word + h_word + [218, 119, 119, 218]:
    core_word = a_word[:-len(rv_word + h_word + [218, 119, 119, 218])]          # 224-style tail
    new_word = core_word + rv_word + [218, 119, 218]
    core = old.execute(core_word)
    assert old.execute(a_word) == N(I(core, I(rv, N(h))))
    assert old.execute(new_word) == A(core, rv)
else:
    assert a_word[:9] == rv_word and a_word[9:20] == h_word and a_word[-3:] == [119, 119, 218]   # seed-style head
    core_word = a_word[20:-3]
    new_word = rv_word + core_word + [119, 218]
    core = old.execute(core_word)
    assert old.execute(a_word) == N(I(rv, I(h, core)))
    assert old.execute(new_word) == N(I(rv, core))
print("(1) symbolic: the helper is gone from the bundle, nothing else changes; G row = Ec,a -> (Ec,b -> Q_Rel(a,b) Ea,b)")
print("    core =", core)

P225 = K224 / "parent225"
groups, _ = cr.decoder_map(c, cr.read_table(P225 / "candidate225.k.tm"), c.tree(json.loads((P225 / "sites225.json").read_text())))
q = lambda k: cr.sole(groups, k)
# B's bindings of the Dag230 atom macros to literal subtrees (check_g_emitter.py)
binding = {166: q(98), 121: q(12), 168: q(166), 171: q(19), 177: q(184)[0], 119: q(90),
           180: q(86), 181: (q(90), ("CI", 1)), 182: (q(86), ("CI", 1)), 218: q(184),
           178: (q(184), (q(90), q(184))), 183: (q(184), (q(86), q(184)))}
flat = lambda t: tuple((o, v) for p, o, v in c.sites(t))
wflat = lambda w: sum((flat(binding[k]) for k in w), ())
af, cf = flat(asrc), flat(csrc)
def once(seq, sub):
    hits = [i for i in range(len(seq) - len(sub) + 1) if seq[i:i + len(sub)] == sub]
    assert len(hits) == 1, (len(hits), len(sub))
    return hits[0]
r7, gf = wflat(old_r7), wflat(new_g)
bw, nw = wflat(a_word), wflat(new_word)
i = once(af, r7); j = once(af, bw)
assert i + len(r7) <= j
expected = af[:i] + gf + af[i + len(r7):j] + nw + af[j + len(bw):]
assert cf == expected, "combined leaves differ from A with the two substitutions"
print(f"(2) literal: combined = A with rho7->G at leaf {i} (+{len(gf) - len(r7)}) and the bundle word at leaf {j} ({len(nw) - len(bw)}); {len(cf)} leaves")
