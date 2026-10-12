"""Reproduce the 120-source deferred core audit against a patched checkout."""
import argparse
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--certificates', type=Path)
    args = parser.parse_args()
    root = args.fast_root.resolve()
    sys.path.insert(0,str(root))
    from fastunknot.normal_parallelity_geometry import _parallelity_geometry
    from fastunknot.normal_surface_geometry import _prepare, _coordinates
    from fastunknot.core_three_handle_reduction import reduce_core_three_handles
    from fastunknot.core_handlebody import core_handlebody_certificate, _forest
    from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
    from check_stopping_obstruction import verify_all_forest_obstruction
    bank = []
    for name in ('corpus.json','three_handle_corpus.json'):
        bank.extend(json.loads((root/'marked_parallelity_research'/name).read_text())['cases'])
    records = []
    for case in bank:
        source = _prepare(case['triangulation'],lambda:None)
        geometry = _parallelity_geometry(source,
            _coordinates(source,case['coordinates'],lambda:None),lambda:None)
        reduced, _ = reduce_core_three_handles(geometry)
        core = reduced['core']
        old = core_handlebody_certificate(core)
        new = core_handlebody_certificate(core,forest_strategy='deferred')
        if new['status'] == 'COMPLETE':
            assert verify_core_handlebody_certificate(core,new['certificate'])
        assert not (old['status']=='COMPLETE' and new['status']!='COMPLETE')
        record = dict(id=case['id'],handles=[len(core['handles'+str(i)]) for i in range(4)],
                      old_status=old['status'],new_status=new['status'])
        if new['status'] != 'COMPLETE':
            record['stopping_rows'] = new['remaining_two_handles']
            assert verify_all_forest_obstruction(core,record['stopping_rows'])
        if old['status'] != new['status']:
            record.update(old_forest=_forest(core,lambda:None)[0],
                          new_forest=new['certificate']['forest'],
                          new_certificate=new['certificate'])
            if args.certificates:
                args.certificates.mkdir(parents=True,exist_ok=True)
                packet = dict(source=case,geometry=reduced,new_certificate=new['certificate'])
                (args.certificates/(case['id'].replace('/','__')+'.json')).write_text(
                    json.dumps(packet,indent=2)+'\n')
        records.append(record)
    summary = dict(cases=len(records),
                   old_complete=sum(r['old_status']=='COMPLETE' for r in records),
                   new_complete=sum(r['new_status']=='COMPLETE' for r in records))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(dict(summary=summary,records=records),indent=2)+'\n')
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
