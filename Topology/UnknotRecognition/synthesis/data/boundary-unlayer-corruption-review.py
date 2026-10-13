"""Small retained one-tetrahedron proof mutations, without discovery or timing."""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'fast'))
from boundary_unlayer_research.replay import replay_reduction
from boundary_unlayer_research.common import CAP_STATS, source_hashes

fixture = Path(__file__).with_name('boundary-unlayer-corruption-fixture.json')
original = json.loads(fixture.read_bytes())
assert replay_reduction(original)
records = []

def reject(name, mutate):
    value = deepcopy(original)
    mutate(value)
    try:
        replay_reduction(value)
    except (AssertionError, KeyError, TypeError, ValueError, IndexError):
        records.append(dict(name=name, rejected=True))
    else:
        raise AssertionError('mutation accepted: '+name)

reject('source digest', lambda x: x.update(source_sha256='0'*64))
reject('step source digest', lambda x: x['steps'][0].update(source_sha256='0'*64))
reject('unknown step schema', lambda x: x['steps'][0].update(schema='unknown'))
reject('nonshrinking successor', lambda x: x['steps'][0].update(successor=x['source']))
reject('wrong final source', lambda x: x.update(final_source=x['source']))
reject('proof replay flag', lambda x: x.update(independent_replay=False))
reject('positive query forged Euler', lambda x: x['queries'][0]['result'].update(euler_characteristic=10))
reject('positive query bool coordinate', lambda x: x['queries'][0]['result']['coordinates'][0].__setitem__(0, True))
reject('positive query missing source', lambda x: x['queries'][0].update(source_sha256='0'*64))
reject('query size bool', lambda x: x['queries'][0].update(tetrahedra=True))
reject('query size mismatch', lambda x: x['queries'][0].update(tetrahedra=2))
reject('negative stat', lambda x: x['queries'][0]['result']['stats'].update(lp_calls=-1))
reject('bool stat', lambda x: x['queries'][0]['result']['stats'].update(lp_calls=True))
reject('float stat', lambda x: x['queries'][0]['result']['stats'].update(lp_calls=1.0))
reject('missing work', lambda x: x['work'].pop('nodes'))
reject('bool work', lambda x: x['work'].update(nodes=True))
reject('inconsistent work', lambda x: x['work'].update(nodes=2))
reject('integer unreturned flag', lambda x: x.update(unreturned_query=0))
reject('integer complete flag', lambda x: x.update(work_complete=1))
reject('contradictory complete flag', lambda x: x.update(work_complete=False))
reject('unreturned complete outcome', lambda x: x.update(unreturned_query=True, work_complete=False))
reject('stale terminal negative packet', lambda x: x.update(negative_certificate={}))
reject('forged negative outcome', lambda x: x.update(outcome='COMPLETE_NEGATIVE_ENDPOINT'))
reject('nan elapsed diagnostic', lambda x: x.update(discovery_seconds=float('nan')))
reject('infinite elapsed diagnostic', lambda x: x.update(discovery_seconds=float('inf')))
reject('bool elapsed diagnostic', lambda x: x.update(discovery_seconds=True))
reject('changed fixed configuration', lambda x: x['search_config'].update(max_pivots=10001))
for cap, statistic in CAP_STATS.items():
    if cap not in original['search_config']:
        continue
    reject('missing configured '+statistic,
           lambda x, statistic=statistic: x['queries'][0]['result']['stats'].pop(statistic))
    def exceed(x, statistic=statistic, cap=cap):
        value = x['search_config'][cap]+1
        x['queries'][0]['result']['stats'][statistic] = value
        if statistic == 'nodes_attempted':
            x['work']['nodes'] = value
        elif statistic == 'lp_pivots':
            x['work']['pivots'] = value
    reject('exceeded '+cap, exceed)

output = dict(passed=True, scope='Direct retained one-tetrahedron supplied-reduction replay; no discovery and no performance measurement.',
    controls=len(records), valid_control=True, source_sha256=source_hashes(),
    fixture_sha256=sha256(fixture.read_bytes()).hexdigest(),
    script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), records=records)
Path(__file__).with_name('boundary-unlayer-corruption-review.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps(dict(passed=True, rejected_mutations=len(records), valid_control=True)))
