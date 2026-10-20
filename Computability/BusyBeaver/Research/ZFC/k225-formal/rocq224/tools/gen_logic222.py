"""Fork Elliot's enumerator layer (Enum230, L1_Sound230, L1_Comp230, L1_230, Seed230) for the
seed-K 222 calculus thm222: rho7 -> growG, bundle -> bundle222, thm230 -> thm222.
Writes Enum222.v, L1_Sound222.v, L1_Comp222.v, L1_222.v, Seed222.v into src/."""
import re
from pathlib import Path

S = Path(r"C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-merge-article-groups-491e11\31b37d1b-6b02-4181-babf-8c85ac50cb17\scratchpad\k224rocq")
L = S.parent / "rocq225/pkg/vendor/k230-rocq/coq/logic"
OUT = S / "src"

HDR = ("(** Forked by gen_logic222.py from Elliot Glazer's k230-rocq (3142e4d) {src} for the seed-K\n"
       "    222 calculus [thm222]: rho7 is replaced by the merged equality row [growG] and the\n"
       "    bundle by the helper-free seed bundle [bundle222]. *)\n")

IMPORTS = {
    "Enum": "From K230L Require Import Codes230.\nFrom K224 Require Import Codes222.",
    "L1_Sound": "From K230L Require Import Codes230.\nFrom K224 Require Import Codes222 Enum222 Thm222.",
    "L1_Comp": "From K230L Require Import Codes230.\nFrom K224 Require Import Codes222 Enum222 Thm222.",
    "L1_": "From K224 Require Import Enum222 Thm222 L1_Sound222 L1_Comp222.",
    "Seed": "From K230L Require Import Codes230.\nFrom K224 Require Import Codes222 Thm222 Enum222 L1_Sound222 L1_Comp222.",
}


def sub_all(t, pairs):
    for a, b in pairs:
        n = len(re.findall(a, t))
        assert n > 0 or a.replace(chr(92)+"b", "") in OPTIONAL, (a, t[:80])
        t = re.sub(a, b, t)
    return t


def fork(name, key, pairs):
    src = L / f"{name}230.v"
    t = src.read_text(encoding="utf-8")
    lines = t.split("\n")
    req = [i for i, l in enumerate(lines) if l.startswith("From K230L Require Import")]
    assert len(req) == 1, (name, req)
    lines[req[0]] = IMPORTS[key]
    t = "\n".join(lines)
    t = sub_all(t, pairs)
    t = HDR.format(src=f"logic/{name}230.v") + t
    (OUT / f"{name}222.v").write_text(t, encoding="utf-8", newline="\n")
    print("wrote", f"{name}222.v")


OPTIONAL = {"T_true", "T_mp", "enum230_halts"}
common = [(r"\bthm230\b", "thm222"), (r"\benum230_halts\b", "enum222_halts"),
          (r"\bT_true\b", "W_true"), (r"\bT_mp\b", "W_mp")]

fork("Enum", "Enum", [(r"\(rho7 a b c\)", "(growG a b c)"),
                      (r"else bundle a b c", "else bundle222 a b c"),
                      (r"\benum230_halts\b", "enum222_halts")])
fork("L1_Sound", "L1_Sound", common + [(r"\bT_bundle\b", "W_bundle")])
fork("L1_Comp", "L1_Comp", common + [
    (r"apply bundle_ne_F", "apply bundle222_ne_F"),
    (r"gate a b c = bundle a b c", "gate a b c = bundle222 a b c"),
    (r"unfold rho1, rho2, rho3, rho4, rho5, rho6, rho7, rho8", "unfold rho1, rho2, rho3, rho4, rho5, rho6, growG, rho8"),
    (r"blk \(rho7 a b c\)", "blk (growG a b c)"),
    (r"blk \(bundle a b c\)", "blk (bundle222 a b c)")])
fork("L1_", "L1_", [(r"\bthm230\b", "thm222"), (r"\benum230_halts\b", "enum222_halts"),
                    (r"\bL1_230\b", "L1_222")])
fork("Seed", "Seed", [(r"\bthm230\b", "thm222"), (r"\bseed230\b", "seed222"),
                      (r"\bT_true\b", "W_true")])
