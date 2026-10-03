#!/usr/bin/env python3
"""Export complete finite sparse local permutations for three test machines."""
from dataclasses import asdict
from pathlib import Path
import argparse, hashlib, json
from three_mass_collision_generator import Instruction, ThreeMassCA

MACHINES = {
    'cycle': (['q0','q1','q2','q3','halt'], 'halt', [
        Instruction('q0','q1','inc',0), Instruction('q1','q2','inc',1),
        Instruction('q2','q3','dec',0), Instruction('q3','q0','dec',1)]),
    'merge': (['zero_source','positive_source','halt'], 'halt', [
        Instruction('zero_source','halt','zero',0),
        Instruction('positive_source','halt','positive',0)]),
    'trap': (['run','halt'], 'halt', [Instruction('run','halt','dec',0)])}

def export(out):
    out.mkdir(parents=True, exist_ok=True)
    summaries = {}
    for name, (states, halt, instructions) in MACHINES.items():
        ca = ThreeMassCA(states, halt, instructions)
        data = {
            'format':'three-mass-literal-channel-rule-v1',
            'description':'Literal finite test instance; not a universal source machine',
            'machine':{'states':states,'halt':halt,'instructions':[asdict(x) for x in instructions]},
            'alphabet':'all subsets of the listed type IDs', 'weight':'subset cardinality',
            'vacuum':[], 'tick_order':['onsite_permutation','channel_shift'],
            'inverse_tick_order':['inverse_channel_shift','inverse_onsite_permutation'],
            'types':ca.names, 'velocities':ca.velocity,
            'singleton_outputs':[ca.single[i] for i in range(len(ca.names))],
            'pair_rows':[{'input':list(a),'output':list(b),'prescribed':a in ca.specified_pairs}
                         for a,b in sorted(ca.pairs.items())],
            'unlisted_pair_action':'identity', 'other_cardinality_action':'identity',
            'prescribed_pair_count':ca.required_pair_count,
            'radius':max(map(abs,ca.velocity)), 'generator_fingerprint':ca.fingerprint()}
        raw=(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n').encode()
        path=out/(name+'_rule.json');path.write_bytes(raw)
        summaries[name]={'types':len(ca.names),'pair_support':len(ca.pairs),
                         'prescribed_pairs':ca.required_pair_count,'radius':data['radius'],
                         'generator_fingerprint':ca.fingerprint(),
                         'file_sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw)}
    (out/'rule_index.json').write_text(json.dumps(summaries,indent=2,sort_keys=True)+'\n')
    return summaries

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('directory',type=Path)
    print(json.dumps(export(ap.parse_args().directory),indent=2))
