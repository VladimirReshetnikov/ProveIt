"""Load and verify all four fixed integers as one coherent backend."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
ORDER=('beta','K','MC','MF_source')
def load():
    manifest=json.loads((HERE/'expanded/MANIFEST.json').read_text())
    values=[]
    for name in ORDER:
        raw=(HERE/'expanded'/f'{name}.bin').read_bytes()
        spec=manifest['ports'][name]
        assert len(raw)==spec['bytes']
        assert hashlib.sha256(raw).hexdigest()==spec['sha256']
        n=int.from_bytes(raw,'little')
        assert n.bit_length()==spec['bit_length']
        values.append(n)
    beta,K,MC,MF_source=values
    d=5**9;B=1<<d;MF_native=MF_source-beta
    assert beta==B-1 and K>0 and 0<MC<B-1 and 0<MF_native<B-1
    assert MC%4==2 and MF_native%8==4
    assert MC.bit_count()+MF_native.bit_count()==d
    return tuple(values)
if __name__=='__main__':
    values=load()
    print('PASS: wang943-mixed-radix4-zero-fields-5pow9; four coefficients verified.')
    print('Port bit lengths:',*[n.bit_length() for n in values])
