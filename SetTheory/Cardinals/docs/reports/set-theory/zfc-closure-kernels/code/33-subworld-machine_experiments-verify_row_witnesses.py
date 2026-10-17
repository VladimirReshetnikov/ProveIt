"""Independently replay the 504 prepared-tape transition-coverage witnesses.

Only the literal 254 table, the pinned program text and the witness JSON are
read. No symbolic executor or register-box summary is imported.
"""
from pathlib import Path
import argparse,hashlib,json,re

ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--json',type=Path,help='write a concise verification result to this path')
args=parser.parse_args()
raw=(ROOT/'machine/zfc_254.tm').read_bytes()
assert hashlib.sha256(raw).hexdigest()=='d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
table={}
for line in raw.decode().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,n=line.split();key=int(q),int(b)
    assert key not in table
    table[key]=int(w),(-1 if d=='L' else 1),int(n)
assert set(table)=={(q,b) for q in range(254) for b in (0,1)}
table[3,0]=(0,-1,48)
table[49,1]=(0,1,64)
table={key:row for key,row in table.items() if key[0] not in (5,8)}
states=set(range(254))-{5,8}
assert set(table)=={(q,b) for q in states for b in (0,1)}
assert all(n in states|{254} for w,d,n in table.values())

program=(ROOT/'Prog254.v').read_bytes()
assert hashlib.sha256(program).hexdigest()=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
body=program.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
assert len(nodes)==6459
registers=('nextproof','topwff','wffstack','axiomcode','param1','param2','scratch1','scratch2','prooflist')
physical=dict(nextproof=6,topwff=7,wffstack=0,axiomcode=2,param1=1,param2=8,scratch1=4,scratch2=3,prooflist=5)
def operation_at(path):
    e='CN 0'
    for bit in path:
        kind,arg=e.split();assert kind=='CN'
        e=nodes[int(arg)][int(bit)]
    kind,*arg=e.split();assert kind!='CN'
    if kind in ('CI','CD'):return 'x.'+registers[int(arg[0])]+('.inc' if kind=='CI' else '.decnz')
    if kind in ('CB','CC'):return ('_break.' if kind=='CB' else '_continue.')+arg[0]
    assert kind=='CH';return 'halt'

data=json.loads((ROOT/'row_coverage.json').read_text())
assert data['prepared_gap']==40 and len(data['witnesses'])==504
assert data['working_states']==252 and data['rows']==504
observed=set();steps=0
for witness in data['witnesses']:
    path=witness['path'];op=witness['operation'];vals=witness['physical_registers'];branch=witness['branch']
    assert len(path)<=34 and all(bit in '01' for bit in path) and operation_at(path)==op
    assert len(vals)>=9 and all(type(n)is int and n>=0 for n in vals)
    assert not any(vals[9:]),'all blocks after the nine named registers must contain zero'
    if op.endswith('.decnz'):
        value=vals[physical[op.split('.')[1]]]
        assert (branch=='z' and value==0) or (branch=='p' and value>0)
    else:assert branch=='-'
    ones={-1,40}|{i for i,bit in enumerate(path) if bit=='1'}
    at=41
    for value in vals:
        at+=1
        for _ in range(value+1):ones.add(at);at+=1
    q=96;h=0
    for _ in range(witness['step']):
        write,move,q=table[q,int(h in ones)]
        if write:ones.add(h)
        else:ones.discard(h)
        h+=move
        steps+=1
    assert (q,int(h in ones),h)==(witness['state'],witness['read'],witness['head'])
    key=q,int(h in ones);assert key not in observed
    observed.add(key)
assert observed==set(table)
if args.json:
    result={
        'status':'pass',
        'working_states':252,
        'distinct_transition_rows':len(observed),
        'witness_replay_steps':steps,
        'prepared_gap':40,
        'trailing_spare_blocks_zero':True,
        'uses_symbolic_executor':False,
        'uses_register_box_oracles':False,
        'scope':'Every transition row is reached by a concrete prepared-instruction input; this is not blank-run reachability or a kernel proof.',
        'input_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in ('machine/zfc_254.tm','Prog254.v','row_coverage.json')},
        'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.json.write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS: {len(observed)} literal rows; {steps} witness replay steps; pinned table and program; no symbolic oracles')
