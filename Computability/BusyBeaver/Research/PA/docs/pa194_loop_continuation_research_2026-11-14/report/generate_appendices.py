#!/usr/bin/env python3
"""Generate the report's numbered, width-bounded corpus appendices.

Run from any directory. Inputs live beside this script unless --data is used.
The output contains only repository-relative locators, never local paths.
"""
import argparse
import csv
import json
import re
from pathlib import Path


def escape(value):
    substitutions = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
        "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
        "<": r"\textless{}", ">": r"\textgreater{}",
    }
    return "".join(substitutions.get(c, c) for c in value)


def inline(value):
    parts = re.split(r"(`[^`]*`)", value)
    return "".join(
        r"\nolinkurl{" + part[1:-1] + "}" if part.startswith("`") else escape(part)
        for part in parts
    )


def longtable(spec, heading, caption, label):
    count = len(heading.split(" & "))
    return [
        r"\begingroup", r"\footnotesize",
        r"\setlength{\tabcolsep}{2pt}",
        r"\setlength{\LTleft}{0pt}", r"\setlength{\LTright}{0pt}",
        r"\renewcommand{\arraystretch}{1.12}",
        r"\begin{longtable}{@{}" + spec + r"@{}}",
        r"\caption{" + caption + r"}\label{" + label + r"}\\",
        r"\toprule", heading + r"\\", r"\midrule", r"\endfirsthead",
        r"\multicolumn{" + str(count) + r"}{@{}l}{\textit{Table \thetable\ continued}}\\",
        r"\toprule", heading + r"\\", r"\midrule", r"\endhead",
        r"\midrule",
        r"\multicolumn{" + str(count) + r"}{r@{}}{\textit{Continued on the next page}}\\",
        r"\endfoot", r"\bottomrule", r"\endlastfoot",
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    packets = json.loads((args.data / "packet_ledger.json").read_text())
    graphs = json.loads((args.data / "frontier194_annotated.json").read_text())
    assert len(packets) == 82 and len(graphs) == 94
    args.output.mkdir(parents=True, exist_ok=True)
    category = {
        "reported principal construction": "P", "supplementary construction": "S",
        "research auxiliary": "A", "research seed": "D", "rejected": "R",
    }
    widths = lambda xs: "".join(r">{\raggedright\arraybackslash}p{" + x + r"\linewidth}" for x in xs)
    graph_text = [
        r"\section{The 94 initial-snapshot 194-state graph classes}",
        r"\label{app:frontier194}",
        "This appendix exhausts the complete spanning 194-state graphs recognized in the pinned supplied corpus; it excludes the constructions first delivered in this report. "
        "The category is an attributed packet status: P = reported principal construction (51), S = supplementary construction (7), "
        "A = research auxiliary (25), D = search seed (4), R = rejected (7). "
        "None of these letters certifies a completed absolute iPRA consistency theorem.",
        "The short hash is the first 12 hexadecimal digits of the canonical table-class identifier, not a literal-file hash. "
        "All 94 prefixes are distinct. The source column names one packet containing a representative; it is not necessarily the first origin of that design. "
        r"Packet identifiers are expanded in Appendix~\ref{app:packet-ledger}. "
        r"The full hashes, literal-file locators and JSON pointers are in \nolinkurl{comparison/frontier194_annotated.csv}; "
        r"\nolinkurl{report/graph_packet_mapping.csv} binds the short identifiers below to that data.",
    ]
    graph_text += longtable(
        widths([".16", ".19", ".045", ".065", ".49"]),
        "ID / class hash & Name & Cat. & Source & Mechanism",
        "Complete initial-snapshot 194-state graph census", "tab:frontier194")
    mappings = []
    for i, graph in enumerate(graphs, 1):
        matches = [j for j, packet in enumerate(packets, 1) if graph["source"].startswith(packet["location"])]
        assert len(matches) == 1, (graph["name"], matches)
        gid, pid = f"G{i:02}", f"P{matches[0]:02}"
        short_hash = graph["table_class_sha256"][:12]
        graph_text.append(
            r"\hypertarget{graph-" + gid + r"}{\textbf{" + gid + r"}}\newline"
            r"{\scriptsize\texttt{" + short_hash + "}} & " + escape(graph["name"]) + " & "
            + category[graph["evidence_category"]] + r" & \hyperlink{packet-" + pid + "}{" + pid + "} & "
            + escape(graph["mechanism"]) + r"\\[3pt]"
        )
        mappings.append({"graph_id": gid, "packet_id": pid, "name": graph["name"],
                         "table_class_sha256": graph["table_class_sha256"], "source": graph["source"],
                         "json_pointer": graph.get("json_pointer") or ""})
    graph_text += [r"\end{longtable}", r"\endgroup", ""]
    (args.output / "frontier194_appendix.tex").write_text("\n\n".join(graph_text[:4]) + "\n" + "\n".join(graph_text[4:]))
    with (args.output / "graph_packet_mapping.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(mappings[0]))
        writer.writeheader()
        writer.writerows(mappings)

    packet_text = [
        r"\section{The 82-packet delivery ledger}", r"\label{app:packet-ledger}",
        "This ledger preserves distinct deliveries even when their principal tables coincide. "
        "The final column summarizes the packet's own reported contribution; historical statements about PA proofs or calibration "
        "are attributed claims, not newly discharged iPRA endpoints. In particular, a packet's former state record reflects its date. "
        "The five incoming packets at the initial snapshot are P78--P82. All 84 top-level README files in these 82 packets were located and hashed.",
        r"For P01--P77, the exact repository directory is \nolinkurl{Computability/BusyBeaver/Research/PA/docs/} followed by the packet name. "
        r"For P78--P82, the exact repository file is \nolinkurl{docs/incoming/} followed by the packet name and \nolinkurl{.zip}. "
        r"The snapshot is \texttt{32d0d8b7d93a63ad4106c18cdb29b37927acdad2}. "
        r"Full source and README identities are retained in \nolinkurl{comparison/packet_ledger.csv} and \nolinkurl{comparison/packet_ledger.json}.",
    ]
    packet_text += longtable(
        widths([".055", ".355", ".55"]), "ID & Packet name & Reported contribution",
        "All filed and incoming packets at the initial snapshot", "tab:packet-ledger")
    for i, packet in enumerate(packets, 1):
        pid = f"P{i:02}"
        packet_text.append(
            r"\hypertarget{packet-" + pid + r"}{\textbf{" + pid + "}} & "
            + r"\nolinkurl{" + packet["packet"] + "} & " + inline(packet["reported_result"]) + r"\\[3pt]"
        )
    packet_text += [r"\end{longtable}", r"\endgroup", ""]
    (args.output / "packet_ledger_appendix.tex").write_text("\n\n".join(packet_text[:4]) + "\n" + "\n".join(packet_text[4:]))
    print(json.dumps({"graphs": len(graphs), "packets": len(packets), "output_files": [
        "frontier194_appendix.tex", "packet_ledger_appendix.tex", "graph_packet_mapping.csv"]}))


if __name__ == "__main__":
    main()
