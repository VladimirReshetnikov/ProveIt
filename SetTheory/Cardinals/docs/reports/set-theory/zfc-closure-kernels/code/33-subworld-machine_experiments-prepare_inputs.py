"""Prepare exact derived runtime/program inputs from two pinned upstream files."""
from pathlib import Path
import hashlib,json,re

ROOT=Path(__file__).resolve().parent
def prepare():
    machine=(ROOT/'machine/zfc_254.tm').read_bytes()
    assert hashlib.sha256(machine).hexdigest()=='d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
    rows={}
    for line in machine.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=q,int(b)
        assert key not in rows
        rows[key]=int(w),d,t
    assert set(rows)=={(str(q),b) for q in range(254) for b in (0,1)}
    rows['3',0]=(0,'L','48');rows['49',1]=(0,'R','64')
    rows={key:row for key,row in rows.items() if key[0] not in ('5','8')}
    assert len(rows)==504 and all(t not in ('5','8') for w,d,t in rows.values())
    output='#! start 0\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))
    (ROOT/'machine/runtime252_oldlabels.tm').write_text(output)
    program=(ROOT/'Prog254.v').read_bytes()
    assert hashlib.sha256(program).hexdigest()=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
    body=program.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
    assert len(nodes)==6459
    regs=('nextproof','topwff','wffstack','axiomcode','param1','param2','scratch1','scratch2','prooflist')
    paths=[]
    def walk(e,p):
        kind,*arg=e.split()
        if kind=='CN':
            left,right=nodes[int(arg[0])];walk(left,p+'0');walk(right,p+'1')
        elif kind in ('CI','CD'):paths.append(['110'+p,'x.'+regs[int(arg[0])]+('.inc' if kind=='CI' else '.decnz')])
        elif kind in ('CB','CC'):paths.append(['110'+p,('_break.' if kind=='CB' else '_continue.')+arg[0]])
        else:assert kind=='CH';paths.append(['110'+p,'halt'])
    walk('CN 0','')
    assert len(paths)==6460 and max(len(p)-3 for p,op in paths)==34
    (ROOT/'paths.json').write_text(json.dumps(paths)+'\n')
    return rows,paths

if __name__=='__main__':
    rows,paths=prepare()
    print(f'Pinned inputs: {len(rows)} runtime rows and {len(paths)} instruction leaves')
