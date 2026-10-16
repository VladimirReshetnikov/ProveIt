#!/usr/bin/env python3
"""Check the 252-state runtime body under externally supplied dispatch inputs.

No blank-tape initialization or 252-state record is asserted. The affine
executor uses unchanged published register-box summaries and this script
does not invoke Coq/Lean or substitute for kernel verification.
"""
import argparse
from pathlib import Path
import json
from context_search import executor, program_sites, cases, check
from bootstrap_search import patched


def main():
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--sources', type=Path, default=here/'sources')
    ap.add_argument('--output', type=Path, default=here/'runtime252_results.json')
    a = ap.parse_args()
    reads = set()
    class Tracking(dict):
        def __getitem__(self, key):
            reads.add(key)
            return super().__getitem__(key)
    rows = patched(a.sources/'zfc_254.tm')
    table = Tracking({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in rows.items()})
    ns = executor(table, a.sources/'symexec.py')
    sites = program_sites(a.sources/'Prog254.v')
    cs = cases(ns, sites)
    for i, c in enumerate(cs):
        assert check(ns, c), ('runtime case failed', i)
    missing = sorted(set(table)-reads, key=lambda x:(int(x[0]),x[1]))
    # These include the entry/return states protected by the box interface.
    protected = {0,1,2,3,5,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,84,85,95,97,109,112,131}
    result = {
        'working_states_in_runtime_body': len({q for q,b in table}),
        'transitions_in_runtime_body': len(table),
        'instruction_sites': len(sites), 'branch_cases_passed': len(cs),
        'dispatch_old_label': 96, 'minimum_invariant_gap': 40,
        'explicit_table_entries_read': len(reads),
        'entries_hidden_inside_register_box_oracles': missing,
        'unused_noncore_entries_in_this_overapproximation': [x for x in missing if int(x[0]) not in protected],
        'runtime_delta_from_253': 'Delete old state 5 and redirect its sole remaining incoming edge 49/1 to old 64. States 5/1 and 64/1 both have transition 1 R 64.',
        'scope': '252-state runtime body only. Initialized dispatch configurations are supplied externally. No valid blank initializer, 252-state complete solution, kernel verification, or internalized consistency equivalence is claimed.'
    }
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
