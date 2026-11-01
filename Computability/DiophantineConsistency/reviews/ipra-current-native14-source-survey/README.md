# Preliminary 14-variable source follow-up

This first packet does not record three historical files and Git HEAD read by
the reused parser. It is preserved as preliminary; the distinct `-v2` packet
records those inputs before and after the survey.

This is a read-only source-header survey for the displayed 14-variable equation,
run while the separate 258-module 13-variable provider rebuild was in progress.
It reports 995 reachable project sources: 984 with matching hashes in the
1,099-source 13-variable survey and 11 extra sources matching the previously
frozen 14-variable snapshot. Its direct external imports are a subset of those
in the 13-variable survey. `extra_order` gives a prospective order for rebuilding
all 11 extra modules on a successfully authenticated new provider.

The separate `check_lean_deps.py` check compared Lean's `--deps` output for the
11 extra frozen files with their captured headers and exited zero; its receipt
SHA-256 is `11a087bc140011c90de24bedf0d4bade0e8d9bfab99d3e74ee84c6405f1eea8d`.
The matching 984 shared sources were included in the earlier 1,099-source Lean
dependency check. The extra check uses a historical provider only to resolve
dependency paths and does not authenticate its objects.

This is **not** a replay and does not authenticate any object environment. The
parent replays, their independent comparison, a new closure audit,
package-companion and selected-object guards, and a guarded 14-variable successor
and its peer remain necessary. Source drift after this snapshot must be rechecked.
The parent retains its recorded inherited external and package-transitive ancestry
limitations.

For that successor, the conservative plan is to rebuild all 11 extra modules,
including seven whose old objects are present in the parent overlay. Exclude each
old object and its `.olean.private`, `.olean.server`, `.ir`, `.ilean`, and hash
companions before compiling; verify absence of all corresponding 11 fallback
objects and companions in the package mirror and Lean toolchain. Pin the independently matched 258-module parent
states, comparator and subprocess-exit receipts, source snapshots, complete object
inventory, project-origin gates, and all recorded external companion and absence
guards. Check the union of the 1,099 parent and 11 extra workspace sources before
and after both replays. The 14-variable endpoint check must report exactly the
standard Lean axioms. None of these future checks has yet been performed here.

`survey.py` reuses the pinned header parser in the earlier survey and refuses to
overwrite its manifest. Its observed terminal exit was zero; output was
`PROSPECTIVE_SOURCE_GRAPH 995 984 11` with manifest SHA-256
`ab038e917c9596195cae0a49e4fa6612a56400829330b7bd79676b21024f3af9`.
