"""Untrusted canonical translation and named raw-boundary fixture builder."""
import json
from pathlib import Path
from translate import translate
ROOT=Path(__file__).resolve().parents[1]

def main():
    source=json.loads((ROOT/'tests/source_cases.json').read_text())['cases']
    cases=[dict(name=c['name'],accept=c['accept'],packet=translate(c['packet'])) for c in source]
    cases.extend([
        dict(name='new_junk_bottom_under_D',packet=[[0,0,0,[0]],[0,0,[0,0,0,0]]],accept=True),
        dict(name='new_junk_bottom_fake_DI',packet=[[0,0,0,[0]],[0,0,[0,0],0]],accept=False),
        dict(name='new_junk_five_fake_DI',packet=[[[],0,0,[0]],[0,0,[0,0],0,0]],accept=False),
        dict(name='new_Eq_dummy_slot_1',packet=[[0,[0,1,0],0,0],[[0,1,0],1]],accept=True),
        dict(name='new_Eq_dummy_slot_2',packet=[[0,[0,2,0],0,0],[[0,2,0],2]],accept=True),
        dict(name='ordinary_eq_cannot_be_DI',packet=[[0,0,0,[0]],[0,[0]]],accept=False),
    ])
    # A nonvacuous zero witness must be boxed because literal zero dispatches
    # to computation. W = I(0,0;v.0) is nonempty syntax and equals zero.
    # Goal: D_{x,y}(I(y,0;v.x)=0). The successor minor computes to W,
    # and transport along the checked W=0 computation finishes the proof.
    box = [0, 0, 0]
    following = [[-1], 0, box]
    cases.append(dict(
        name='nonvacuous_boxed_zero_witness', accept=True,
        packet=[
            [0, [-1, 0, box], 1, 0],
            [0, [0, 0, 0], 0, 0],
            [[box, 0], box, 0, [following, 3]],
            [[], 0, 0, box],
            [0, 0, [[7, 0, 9], 0]],
        ]))
    (ROOT/'tests/affine_cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    examples = ROOT / 'tests' / 'examples'
    examples.mkdir(exist_ok=True)
    for case in cases:
        (examples / (case['name'] + '.json')).write_text(
            json.dumps(case['packet'], indent=2) + '\n')
    print(json.dumps({'source_cases':len(source),'affine_cases':len(cases),'scope':'Finite producer; never imported by a checker.'}))

if __name__=='__main__':main()
