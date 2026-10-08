"""Independent full matrix identity checks plus deterministic source replay."""
from common import *
from radical import *
from disk_frontier import *
from fastunknot.planar import Planar
import json,argparse


def decode_map(rows):return [{int(k):v for k,v in row.items()} for row in rows]
def decode_complex(d):return Complex(d['mid'],d['deg'],decode_map(d['out']))

def verify(path):
    data=json.loads(Path(path).read_text());total=0
    if data['schema_version']!=1:raise ValueError('unknown certificate version')
    for case in data['cases']:
        replay=FastScan(shape_cache=False)
        for stage,cross in zip(case['stages'],case['pd']):
            replay.add_crossing(tuple(cross),reduce_now=False)
            verify_disk_certificate(stage['prefix'],stage['disk_certificate'])
            alg=Planar(False)
            for pairs in stage['matchings'][1:]:alg.intern(tuple(tuple(p) for p in pairs))
            c=decode_complex(stage['original'])
            if c!=snapshot(replay):raise ArithmeticError('source replay differs from certified input')
            sc=Contraction(**stage['scalar_contraction']);sc.verify()
            red=Reduction(decode_complex(stage['reduced']),sc,stage['stats'],
                          decode_map(stage['inclusion']),decode_map(stage['projection']),
                          decode_map(stage['homotopy']))
            verify_common_order([alg.pairs[m] for m in c.mid],stage['disk_certificate']['cyclic_order'])
            verify_reduction(c,red,alg)
            total+=1;replay.eliminate()
    print(f'{total} disk-bound strong deformation retracts verified, including source replay')
    return total

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('file',nargs='?',default=str(ROOT/'results'/'chain_certificates.json'))
    verify(parser.parse_args().file)
