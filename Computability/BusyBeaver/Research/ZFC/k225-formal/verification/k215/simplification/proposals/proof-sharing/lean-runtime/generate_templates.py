#!/usr/bin/env python3
"""Render the inherited, label-correct 35 templates as kernel-checkable Lean data.

The generator is untrusted: KLeftFrame215.all_checked checks all resulting runs
against the maintained literal tm215. Full source-leaf coverage is not claimed.
"""
import argparse
import hashlib
import json
from pathlib import Path

EXPECTED_INPUT = "e2b8fd178afba6c85edf17eb647751d90a606541f03b01b76ec309acfdd62238"


def bit(value):
    if value not in (0, 1, False, True):
        raise ValueError(f"Not a bit: {value!r}")
    return "true" if value else "false"


def seg(s):
    if s[0] == "b":
        return f".bit {bit(s[1])}"
    if s[0] == "r":
        return f".run {bit(s[1])} {s[2]} {s[3]}"
    if s == ["x", "none", 0]:
        return ".box (.plain .none)"
    raise ValueError(f"Unexpected segment {s!r}")


def segs(xs):
    return "[" + ", ".join(map(seg, xs)) + "]"


def conf(s):
    return f"({s[0]}, {bit(s[1])}, {segs(s[2])}, {segs(s[3])})"


def bits(word):
    return "[" + ", ".join("true" if b == "1" else "false" for b in word) + "]"


def render_paths(templates):
    lines = [
        "import BusyBeaver.ZFC.RegisterPath", "",
        "/-! The control actions of the same 35 inherited templates preserve any left",
        "prefix. These equalities are about exact full paths, not only a suffix. -/",
        "namespace SetTheory.BusyBeaver.ZFC.KLeftFramePaths215",
        "open RegisterPath", "", "structure Action where",
        "  templateId : Nat", "  isContinue : Bool", "  levels : Nat",
        "  suffix : List Bool", "  result : List Bool", "",
        "def actions : List Action := [",
    ]
    lines.append(",\n".join(
        f"  ⟨{t['id']}, {'true' if t['key'][3]=='CC' else 'false'}, "
        f"{t['key'][4]}, {bits(t['key'][2])}, {bits(t['key'][6])}⟩" for t in templates))
    lines += ["]", "", "def applyAction (a : Action) (word : List Bool) : List Bool :=",
        "  if a.isContinue then continuePath a.levels word else breakPath a.levels word", "",
        "theorem action_count : actions.length = 35 := rfl", "",
        "theorem prefix_action {a : Action} (ha : a ∈ actions) (P : List Bool) :",
        "    applyAction a (P ++ a.suffix) = P ++ a.result := by",
        "  simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at ha",
        "  rcases ha with " + " | ".join(["rfl"] * 35),
        "  all_goals simp [applyAction, continuePath, breakPath, stripPath, incPath,",
        "    List.reverse_append, List.reverse_cons, stripRev, incRev, List.append_assoc]", "",
        "end SetTheory.BusyBeaver.ZFC.KLeftFramePaths215", "",
        "#print axioms SetTheory.BusyBeaver.ZFC.KLeftFramePaths215.prefix_action", ""]
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=Path(__file__).parent / "BusyBeaver/ZFC/KLeftFrame215.lean")
    args = ap.parse_args()
    source = args.repo / "Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/round13-left-frame/runtime/FORMAL_TEMPLATES.json"
    raw = source.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED_INPUT:
        raise SystemExit("Template input hash changed: review before regenerating")
    data = json.loads(raw)
    templates = data["templates_data"]
    if len(templates) != 35 or sum(t["steps"] for t in templates) != 444:
        raise SystemExit("Unexpected template census")
    lines = [
        "import BusyBeaver.ZFC.KLeftFrame",
        "import BusyBeaver.ZFC.KTable215",
        "import BusyBeaver.ZFC.KTape",
        "import BusyBeaver.ZFC.KHomeReady",
        "",
        "/-! Concrete kernel checks for the inherited 35 round13-left-frame bodies.",
        "    This is template validity, not all-leaf source coverage. -/",
        "namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215",
        "open KZip KRuntimeCore KTableCore KLeftFrame",
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
        "structure Template where",
        "  steps : Nat",
        "  entry : SConf",
        "  exitRight : List Seg",
        "",
        "def templates : List Template := [",
    ]
    rows = []
    for i, t in enumerate(templates):
        if t["id"] != i or t["pre_home"][:3] != [2, True, []]:
            raise SystemExit("Unexpected template id or boundary")
        rows.append(f"  -- Template {i}: {t['key'][3]} {t['key'][4]}, suffix {t['key'][2]}\n"
                    f"  ⟨{t['steps']}, {conf(t['start'])}, {segs(t['pre_home'][3])}⟩")
    lines += [",\n".join(rows), "]", ""]
    lines += [
        "def checked (t : Template) : Bool :=",
        "  decide (runLocal tm215 none t.steps t.entry = some (2, true, [], t.exitRight))",
        "",
        "theorem template_count : templates.length = 35 := rfl",
        "",
        "theorem all_checked : templates.all checked = true := by decide +kernel",
        "",
        "theorem local_of_mem {t : Template} (ht : t ∈ templates) :",
        "    runLocal tm215 none t.steps t.entry = some (2, true, [], t.exitRight) := by",
        "  have h := List.all_eq_true.mp all_checked t ht",
        "  exact of_decide_eq_true h",
        "",
        "theorem boxes : BoxLemmas tm215 := KTape.boxLemmas (by decide) (.inr rfl)",
        "",
        "theorem home_ready : KHomeReady.ready tm215 = true := by decide +kernel",
        "",
        "/-- Every listed body works for every gap, every valid register list, and",
        "every finite preserved prefix accepted by the existing Home guard. -/",
        "theorem template_prefix {t : Template} (ht : t ∈ templates)",
        "    (P : List Bool) (n : Nat) {vs : List Nat} (hv : Valid none vs)",
        "    {j : Nat} (hscan : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j) :",
        "    Reach1 tm215 (conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) t.entry))",
        "      (conc n vs (84, false, [.bit true], P.map Seg.bit ++ t.exitRight)) :=",
        "  local_prefix_sound boxes (KHomeReady.ready_sound home_ready).1",
        "    (KHomeReady.ready_sound home_ready).2 n hv P (local_of_mem ht) hscan",
        "",
        "end SetTheory.BusyBeaver.ZFC.KLeftFrame215",
        "",
        "#print axioms SetTheory.BusyBeaver.ZFC.KLeftFrame215.all_checked",
        "#print axioms SetTheory.BusyBeaver.ZFC.KLeftFrame215.template_prefix",
        "",
    ]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(lines))
    paths_output = args.output.with_name("KLeftFramePaths215.lean")
    paths_output.write_text(render_paths(templates))
    print(json.dumps({"templates":35,"symbolic_steps":444,"output":str(args.output),
                      "source_sha256":EXPECTED_INPUT,
                      "output_sha256":hashlib.sha256(args.output.read_bytes()).hexdigest(),
                      "paths_output_sha256":hashlib.sha256(paths_output.read_bytes()).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
