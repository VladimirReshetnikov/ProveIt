#!/usr/bin/env python3
"""Reconstruct new integer-family numerals; authenticate coherent inherited positive tuple."""
from pathlib import Path
import gzip, hashlib, importlib.util, json
ROOT=Path(__file__).resolve().parent

def need(test,msg):
    if not test: raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    p=ROOT/'integer/coefficients/recipe/source34_builder.py'
    spec=importlib.util.spec_from_file_location('frozen_integer_recipe',p)
    recipe=importlib.util.module_from_spec(spec);spec.loader.exec_module(recipe)
    vals,audit=recipe.construct()
    vals={'beta':vals['beta'],'K0':vals['K'],'MC':vals['MC'],'MF':vals['MF_source'],'cone_A':2**1113,'cone_B':2**666104}
    result={'status':'PASS','integer_recipe_audit':audit,'integer_and_lowdegree':{},'positive_inherited':{}}
    for group in ['integer','lowdegree']:
        binding=json.loads((ROOT/group/'coefficients/BINDING.json').read_text())
        for name,meta in binding['payloads'].items():
            rebuilt=vals[name].to_bytes((vals[name].bit_length()+7)//8,'little')
            archived=(ROOT/group/'coefficients'/meta['file']).read_bytes()
            raw=gzip.decompress(archived)
            need(rebuilt==raw,'reconstructed complete bytes '+group+'/'+name)
            need(sha(raw)==meta['raw_sha256'] and len(raw)==meta['raw_bytes'] and vals[name].bit_length()==meta['bits'],'binding '+name)
            result['integer_and_lowdegree'][group+'/'+name]={'raw_sha256':sha(rebuilt),'gzip_sha256':sha(archived),'raw_bytes':len(rebuilt),'mode':'full independent recipe reconstruction and byte equality'}
    old=ROOT/'prior/ZFC_Diophantine_Coprime_Projection/positive/coefficients'
    binding_path=ROOT/'positive/coefficients/BINDING.json'
    need(binding_path.read_bytes()==(old/'BINDING.json').read_bytes(),'whole positive binding unchanged')
    binding=json.loads(binding_path.read_text())
    for name,meta in binding['ports'].items():
        data=(binding_path.parent/meta['file']).read_bytes();raw=gzip.decompress(data)
        need(data==(old/meta['file']).read_bytes(),'coherent inherited positive payload '+name)
        need(sha(data)==meta['gzip_sha256'] and sha(raw)==meta['raw_sha256'],'positive authenticated hashes')
        need(int.from_bytes(raw,'little').bit_length()==meta['bits'],'positive bit length')
        result['positive_inherited'][name]={'raw_sha256':sha(raw),'gzip_sha256':sha(data),'mode':'exact inherited tuple bytes authenticated, not a fresh native compiler calibration'}
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
