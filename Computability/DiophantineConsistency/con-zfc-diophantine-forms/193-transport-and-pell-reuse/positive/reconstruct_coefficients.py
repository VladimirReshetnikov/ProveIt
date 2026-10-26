"""Check the unchanged four fixed integers from their complete finite recipe."""
from pathlib import Path
import gzip,hashlib,importlib.util,json

ROOT=Path(__file__).resolve().parent

def check():
    path=ROOT/'retained_coefficient_recipe.py'
    spec=importlib.util.spec_from_file_location('retained_recipe',path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    vals=module.reconstruct()
    graph=json.loads((ROOT/'whole190.json').read_text())
    ports=graph['coefficient_binding']['ports']
    receipt=[]
    for name,m in ports.items():
        v=vals[name]
        raw=v.to_bytes((v.bit_length()+7)//8,'little')
        compressed=(ROOT/'coefficients'/m['file']).read_bytes()
        if v.bit_length()!=m['bits']:raise ValueError('bit length: '+name)
        if hashlib.sha256(raw).hexdigest()!=m['raw_sha256']:raise ValueError('raw hash: '+name)
        if hashlib.sha256(compressed).hexdigest()!=m['gzip_sha256']:raise ValueError('compressed hash: '+name)
        if gzip.decompress(compressed)!=raw:raise ValueError('coefficient bytes: '+name)
        receipt.append({'port':name,'bits':v.bit_length(),'raw_bytes':len(raw),'sha256':m['raw_sha256']})
    return {'complete_fixed_tuple_reconstructed':True,'endianness':'little','ports':receipt}

if __name__=='__main__':print(json.dumps(check(),indent=2))
