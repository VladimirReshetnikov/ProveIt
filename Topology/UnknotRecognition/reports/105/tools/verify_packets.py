"""Replay all supplied positive packets, rebuilding core geometry from source."""
import argparse
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    sys.path.insert(0,str(args.fast_root.resolve()))
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
    from fastunknot.normal_parallelity_geometry import _parallelity_geometry
    from fastunknot.normal_surface_geometry import _prepare, _coordinates
    from fastunknot.core_three_handle_reduction import reduce_core_three_handles
    package = Path(__file__).resolve().parents[1]
    whole, cores = [], []
    for path in sorted((package/'certificates/whole_cut').glob('*.json')):
        packet = json.loads(path.read_text())
        case = packet['source']
        assert verify_normal_cut_handlebodies(case['triangulation'],
            case['coordinates'],packet['certificate']),path
        whole.append(case['id'])
    for path in sorted((package/'certificates/core').glob('*.json')):
        packet = json.loads(path.read_text())
        case = packet['source']
        prepared = _prepare(case['triangulation'],lambda:None)
        geometry = _parallelity_geometry(prepared,
            _coordinates(prepared,case['coordinates'],lambda:None),lambda:None)
        reduced, _ = reduce_core_three_handles(geometry)
        assert reduced == packet['geometry'],path
        assert verify_core_handlebody_certificate(reduced['core'],
            packet['new_certificate']),path
        cores.append(case['id'])
    assert len(whole)==9 and len(cores)==8
    result = dict(status='VERIFIED',whole_cut_packets=whole,core_packets=cores,
        scope='Whole packets use the independent outer verifier. Core packets additionally rebuild the source geometry and baseline dual reduction before independent core replay.')
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
