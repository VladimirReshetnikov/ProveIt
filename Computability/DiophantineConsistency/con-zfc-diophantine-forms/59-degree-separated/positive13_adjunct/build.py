"""Build the degree126 adjunct from an authenticated inert parent DAG."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def build():
    pin=json.loads((ROOT/'PARENT_PIN.json').read_text())
    path=ROOT/'upstream/low_degree/thirteen_positive_degree132.json'
    if hashlib.sha256(path.read_bytes()).hexdigest()!=pin['parent_sha256']:
        raise ValueError('Parent DAG hash mismatch')
    blob=json.loads(path.read_text())
    rows=blob['source'][:73]
    if rows[-1]!=['V','-','r70','r71']:
        raise ValueError('Unexpected parent prefix')
    def op(name,kind,left,right):
        rows.append([name,kind,left,right]);return name
    M=op('M','+','a',1)
    ap3=op('ap3','+','a',3)
    C=op('Caux','*',ap3,'r62')
    d=op('daux','-','Aaux',1)
    v2=op('V2','*','V','V')
    v21=op('V2m1','-',v2,1)
    za=op('Za','*',C,v21)
    my=op('My','*',M,'y')
    my2=op('twomMy','-',2,my)
    dy=op('dy','*',d,'y')
    zb=op('Zb','*',dy,my2)
    z=op('Z','+',za,zb)
    zg=op('Zguard','+',1,z)
    ng=op('Nguard','+','N',1)
    a=op('factor1','*','Nt',ng)
    b=op('factor2','*',a,'strong')
    c=op('factor3','*',b,zg)
    op('out','-',c,1)
    blob.update(source=rows,operations=len(rows),exact_degree=126,proof='PROOF.md',
        coefficient_binding_file='coefficients/COEFFICIENT_BINDING.json',
        coefficient_payloads={k:'coefficients/coefficients/'+v for k,v in
            {'beta':'beta.bin.gz','K0':'K.bin.gz','MC':'MC.bin.gz','MF':'MF_source.bin.gz'}.items()},
        parent_sha256=pin['parent_sha256'])
    (ROOT/'thirteen_positive_degree126.json').write_text(json.dumps(blob,indent=2)+'\n')
    return blob
if __name__=='__main__':
    result=build()
    print(json.dumps({k:result[k] for k in ['operations','exact_degree','witnesses']},indent=2))
