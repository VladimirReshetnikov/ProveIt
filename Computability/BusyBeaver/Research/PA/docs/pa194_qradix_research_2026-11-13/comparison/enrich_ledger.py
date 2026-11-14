#!/usr/bin/env python3
"""Add an explicit principal-contribution status to all 54 packet rows.

Statuses describe a packet's principal contribution, not every table it
contains. Historical copied baselines, search intermediates, and rejected
controls retain their own graph-level statuses in the frontier inventory.
"""
from pathlib import Path
import csv
import hashlib
import json
import re
import argparse

HERE = Path(__file__).resolve().parent
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--ledger',type=Path,default=HERE/'packet_ledger.json')
args = ap.parse_args()
REPO = args.repo.resolve()
PIN = "317b07268681b44ff352d173a162e2a8c241b2fe"
DATA = args.ledger.resolve()
d = json.loads(DATA.read_text())

groups = {
    "194-state construction(s) with supplied ordinary calibration": """
PA194R_research_2026-11-14
pa194C_conpa_2026-11-13_2
pa194N_conpa_2026-11-13
pa194_conpa_2026-11-13
pa194_conpa_2026-11-13_2
pa194_new_designs_2026-11-13
pa194_radix_family_2026-11-13
pa194c_conpa
pa194c_conpa_2026-11-13
pa194c_conpa_2026-11-13_1
pa194hs_conpa_2026-11-13
pa194j_pa194d_conpa_2026-11-13
pa194n5_n6_conpa_2026-11-13
pa194n6_research_2026-11-13
pa194ns_conpa_2026-11-13
pa194q_conpa_2026-11-13
pa194zr_conpa_2026-11-13
PA194NS_research
pa194haz_research_2026-11-14
pa194qn_research_2026-11-13
""",
    "195-state construction(s) with supplied ordinary calibration": """
PA195_ConPA_research_2026-11-14
pa195_conpa_2026-11-13
pa195_diagonal_combined_2026-11-13
pa195_followup_research
""",
    "196-state supported variants and reduction research": """
conpa_tm_comparison_and_search
conpa_tm_study_2026-11-13
pa_consistency_comparison_and_new196_2026-11-13
pa_consistency_cross_archive
pa_consistency_reduction
pa_consistency_research
pa_consistency_research_2026-11-13_2
pa_tm_comparison_and_reductions
pa_tm_extended_research_2026-11-13
pa_tm_research_2026-11-13
pa_tm_research_2026-11-13_2
""",
    "208-state supported constructions and reduction research": """
U208_ConPA_2026-10-29
U208_ConPA_Conditional_Context_2026-10-29
U208_ConPA_Entry_Context_2026-10-29
U208_ConPA_History_2026-10-29
pa208_research_2026-10-29
u208_research_2026-10-29
""",
    "negative smaller-state search with auxiliary source/logical results": """
Below_U208_Research_2026-10-29
ConPA_below208_research_2026-10-29
PA_consistency_TM_research_2026-11-13
pa196_research_2026-11-13
pa_below196_research
pa_consistency_comparison_2026_11_13
pa_consistency_reduction_audit_2026-11-14
pa_consistency_research_2026-10-29
u208_comparison_research_2026-10-29
""",
    "experimental command variants; incomplete universal physical evidence": """
conpa_tm_comparison_and_reduction_search
""",
    "199-state diagonal-calculus source compilation": """
pa_consistency_research_2026-11-13
""",
    "197-state NEG18 source compilation": """
pa_consistency_research_2026-11-14
""",
    "theory calibration and proof-search interface; no new literal TM": """
pa_unary_power_cover
""",
}
status = {}
for label, names in groups.items():
    for name in names.split():
        if name in status:
            raise ValueError(f"Duplicate status for {name}")
        status[name] = label
if set(status) != {p["packet"] for p in d["packets"]}:
    raise ValueError("Packet status coverage is not exact")

# This attributed historical audit contains finer contribution distinctions
# for 27 early packets. It is part of the pinned corpus, not a fresh rerun.
old_path = Path("Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13_2/reference/pa195_conpa/comparison/archive_notes.txt")
old_text = (REPO / old_path).read_text()
details = {}
for line in old_text.splitlines():
    match = re.fullmatch(r"\| `(.+)\.zip` \| (.+) \|", line)
    if match:
        name, contribution = match.groups()
        name = name.replace(" (2)", "_2")
        details[name] = contribution
extra = {
    "PA194R_research_2026-11-14": "R changes the decoder association; F changes a final known-zero return; A changes a zero-entry return. The packet's X table duplicates CSZ. All remain at 194 states.",
    "PA195_ConPA_research_2026-11-14": "195S uses 67 AX readers and six folds with the separate-head source unchanged (134+67-6). 195C retains that grammar with the cached controller. Both receive complete symbolic and independent physical audits in the packet.",
    "pa195_conpa_2026-11-13": "The bundled diagonal-vacuity calculus receives a 195-state allocation (68 AX readers, seven folds). Its written calibration supplies the syntactic calculus-to-PA direction beyond the upstream one-way internal theorem.",
    "pa195_diagonal_combined_2026-11-13": "PA195DC combines the bundled diagonal emitter with the Combined controller; six native rows change, with 3676 source sites and complete contracts/startup. Two secondary 195-state allocations are separately marked experimental.",
    "pa195_followup_research": "M195S8 is a supported 195-state eight-fold layout. The tempting seven-zero scanner 194 quotient passes its local folds but fails a primitive source contract; it is expressly rejected.",
    "pa_consistency_cross_archive": "Four supported 196-state compositions: bundled/separate diagonal emitter, each with Combined controller and with/without zero-jump closing. They retain exact source/runtime/startup evidence. Direct negation gives a separate 197-state composition; automatic freshness remains incomplete.",
    "pa_consistency_research_2026-11-14": "NEG18 implements encoded negation using INC R7 twice then node64. Eight replacements cut 3673 source sites to 3441, but the physical allocation is 134+68-5=197. Full scratch invariant, 4468 contracts, and exact startup are supplied.",
    "pa_consistency_reduction_audit_2026-11-14": "Comparison and bounded reduction audit. Explicitly no accepted sub-196 machine or new end-to-end theorem; includes scanner-synthesis positive controls that must not be counted as PA machines.",
    "pa194_conpa_2026-11-13": "Separate-head 190-token emitter with 67 reader states and seven contextual folds: 134+67-7=194. Exact source/CFG/physical startup and ordinary PA calibration are supplied.",
    "pa194_conpa_2026-11-13_2": "Alternative separate-head layout uses 68 readers and eight folds: 134+68-8=194. Includes original-controller all-store proof compiler and an independent free-algebra emitter/command audit.",
    "pa194_radix_family_2026-11-13": "M5 and M6 replace formula multiplier 4 by 5 or 6; hereditary formula/label recoding, unrestricted rho8 derivation, and all-residue PA interpretation calibrate them. M4R is a distinct reassociation at radix four.",
    "pa194j_pa194d_conpa_2026-11-13": "J replaces ten proved-zero jump returns by decrement returns. D constructs the diagonal head from a different source parameter. Their source commands differ materially; both remain 194.",
    "pa194zr_conpa_2026-11-13": "ZR uses nine known-zero return replacements in a new layout. Its additional node1-X edit is rejected by a 1361-step blank halt.",
    "pa194q_conpa_2026-11-13": "Q exchanges the two curried premises of the sixth quantifier head using a finite implicational derivation. CSZ combines symmetric Shift with a known-zero entry. Q's controller is cached-only; CSZ is later duplicated as X.",
    "pa194_new_designs_2026-11-13": "The C cached-result/cached-only-Shift table is repeated elsewhere; the additional CS machine symmetrizes Shift comparison. The physical tables receive their own changed-command calibration.",
    "pa194N_conpa_2026-11-13": "N removes the successful-MP dummy-zero push while retaining the original sum test in Shift. Its all-store proof compiler inserts a reserved zero in the proof word; simply deleting the old push without changing the compiler would be incorrect.",
}
cached = "C moves successful MP's result to cached H and makes Shift test H alone. It changes the command compiler, not only physical state names. This same C graph appears in five principal deliveries; auxiliary layouts are separately inventoried."
for name in ("pa194C_conpa_2026-11-13_2", "pa194c_conpa", "pa194c_conpa_2026-11-13", "pa194c_conpa_2026-11-13_1"):
    extra[name] = cached

detail_url = f"https://github.com/VladimirReshetnikov/ProveIt/blob/{PIN}/{old_path.as_posix()}"
for p in d["packets"]:
    name = p["packet"]
    p["principal_status"] = status[name]
    p["status_scope"] = "Principal contribution only; historical, auxiliary and rejected tables inside the packet are not collectively approved. No new end-to-end kernel theorem was rerun by this inventory."
    if name in extra:
        p["comparison_detail"] = extra[name]
        p["comparison_detail_source"] = p["source_url"]
    elif name in details:
        p["comparison_detail"] = details[name]
        p["comparison_detail_source"] = detail_url
    else:
        p["comparison_detail"] = p["summary"]
        p["comparison_detail_source"] = p["source_url"]

actual = {p.name for p in (REPO / "Computability/BusyBeaver/Research/PA/docs").iterdir() if p.is_dir()}
placed = {p["packet"] for p in d["packets"] if p["location"] == "placed"}
if actual != placed or len(placed) != 51 or len(d["packets"]) != 54:
    raise ValueError("Placed/current ledger directory mismatch")
d["coverage_check"] = {"principal_packets":54,"placed_directories":51,"incoming_archives":3,
    "every_principal_packet_has_status":True,"placed_directory_set_exact":True,
    "historical_detail_source_sha256":hashlib.sha256((REPO/old_path).read_bytes()).hexdigest(),
    "status_meaning":"Principal contribution, not blanket verification of every contained transition table."}
DATA.write_text(json.dumps(d, indent=2) + "\n")
fields = ["packet", "location", "path", "principal_status", "comparison_detail", "summary", "proof_boundary", "duplicate_note", "source_url", "comparison_detail_source", "status_scope"]
with DATA.with_suffix('.csv').open("w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=fields)
    w.writeheader()
    w.writerows({k:p[k] for k in fields} for p in d["packets"])
print(json.dumps(d["coverage_check"], indent=2))
