"""Source-bound proofs of free groups with positive total second Betti number.

These research packets certify an Euler obstruction; they are not complete
handlebody censuses.  The independent source, presentation and group checkers
reconstruct every number used in b2 = chi - component_count + free_rank_sum.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys


PACKAGE = Path(__file__).resolve().parents[1]


def decode(value, encoded_integer):
    if isinstance(value, dict):
        return {key: decode(item, encoded_integer) for key, item in value.items()}
    if isinstance(value, list):
        return [decode(item, encoded_integer) for item in value]
    if isinstance(value, str) and value.lower().lstrip('+-').startswith('0x'):
        return encoded_integer(value)
    return value


def replay(packet):
    from fastunknot.integer_codec import encoded_integer, certificate_equal
    from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
    from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
    from fastunknot.source_cut_group_verify import verify_disk_cut_presentation
    from fastunknot.free_group_elimination_verify import replay_free_group
    c, p, b = packet['source'], packet['parallelity'], packet['boundary']
    if not verify_normal_cut_parallelity(c['triangulation'], c['coordinates'], p):
        return False
    if not verify_parallelity_boundary_words(c['triangulation'], c['coordinates'], b):
        return False
    geometry, summary = decode(p['geometry'], encoded_integer), decode(p['summary'], encoded_integer)
    skeleton = decode(b['skeleton'], encoded_integer)
    presentation = decode(packet['presentation'], encoded_integer)
    if not verify_disk_cut_presentation(geometry, summary, skeleton, presentation):
        return False
    if len(packet['groups']) != len(presentation['components']):
        return False
    r, z = 0, 0
    for component, proof in zip(presentation['components'], packet['groups']):
        if proof['component'] != component['id']:
            return False
        checked = replay_free_group(component['generators'], component['relators'], proof['proof'])
        if checked is None:
            return False
        r += checked['free_rank']
        z += checked['trivial_relators']
    c_count = len(presentation['components']) + presentation['isolated_ball_count']
    chi = (summary['core_euler_characteristic'] + summary['bundle_euler_characteristic']
           - summary['attachment_euler_characteristic'])
    h3 = len(geometry['core']['handles3'])
    b2 = chi - c_count + r
    if b2 <= 0 or b2 != z - h3:
        return False
    return certificate_equal(packet['diagnostics'],
        dict(chi=chi, components=c_count, free_rank_sum=r,
             trivial_relators=z, source_three_handles=h3, second_betti_sum=b2))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source-audit', type=Path, default=PACKAGE/'results/native_audit.json')
    parser.add_argument('--replay-only', type=Path)
    args = parser.parse_args()
    fast = args.fast_root.resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe
    if args.replay_only:
        report = json.loads(args.replay_only.read_text())
        for packet in report['packets']:
            if not replay(packet):
                raise ArithmeticError('Euler-defect replay failed: ' + packet['source']['id'])
        answer = dict(passed=True, packets=len(report['packets']), mode='replay_only')
        args.output.write_text(json.dumps(answer, indent=2)+'\n')
        print(json.dumps(answer))
        return
    from fastunknot.normal_parallelity import normal_cut_parallelity
    from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
    from fastunknot.source_cut_group import compile_disk_cut_presentation
    from fastunknot.free_group_elimination import certify_free_group
    source_audit = json.loads(args.source_audit.read_text())
    ids = [c['id'] for c in source_audit['cases']
           if c['group'].get('reason') == 'positive_second_betti_number']
    bank = {}
    for filename in ('corpus.json', 'three_handle_corpus.json'):
        bank.update((c['id'], c) for c in
            json.loads((PACKAGE/'fixtures'/filename).read_text())['cases'])
    packets = []
    for identity in ids:
        c = bank[identity]
        p = normal_cut_parallelity(c['triangulation'], c['coordinates'], record_certificate=True)
        b = normal_parallelity_boundary_words(c['triangulation'], c['coordinates'], record_certificate=True)
        presentation = compile_disk_cut_presentation(p['geometry'], p['summary'], b['skeleton'])
        if presentation is None:
            raise ArithmeticError('reported Euler defect has unsupported disk bases')
        groups, rank, trivial = [], 0, 0
        for component in presentation['components']:
            free = certify_free_group(component['generators'], component['relators'])
            if free['status'] != 'COMPLETE':
                raise ArithmeticError('reported Euler defect lacks a free-group trace')
            groups.append(dict(component=component['id'], proof=free['certificate']))
            rank += free['free_rank']
            trivial += free['stats']['trivial_relators']
        count = len(presentation['components']) + presentation['isolated_ball_count']
        chi = presentation['source_euler_characteristic']
        packet = dict(source=c, parallelity=p['certificate'], boundary=b['certificate'],
                      presentation=presentation, groups=groups,
                      diagnostics=dict(chi=chi, components=count, free_rank_sum=rank,
                          trivial_relators=trivial, source_three_handles=len(p['geometry']['core']['handles3']),
                          second_betti_sum=chi - count + rank))
        if not replay(packet):
            raise ArithmeticError('new Euler-defect packet failed source replay: ' + identity)
        packets.append(packet)
        print(identity, packet['diagnostics'], flush=True)
    files = ('source_cut_group.py', 'source_cut_group_verify.py',
             'free_group_elimination.py', 'free_group_elimination_verify.py')
    report = dict(schema='source-euler-defect-audit-v1', independently_replayed=True,
                  source_sha256={name: hashlib.sha256((fast/'fastunknot'/name).read_bytes()).hexdigest()
                                 for name in files}, packets=packets)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print(json.dumps(dict(passed=True, packets=len(packets))))


if __name__ == '__main__':
    main()
