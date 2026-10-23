"""Three deliberately corrupted copies must fail the independent checker."""
from pathlib import Path
import gzip,hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
results=[]
for mode in ('layout_target','threshold_scale','mask_bit'):
    with tempfile.TemporaryDirectory(prefix='conzfc-integer-negative-')as td:
        target=Path(td)/'integer'
        shutil.copytree(ROOT,target,ignore=shutil.ignore_patterns('alternative_low_cost','__pycache__'))
        if mode=='layout_target':
            f=target/'data/layout.json';o=json.loads(f.read_text());o['targets'][0]+=1;f.write_text(json.dumps(o))
        elif mode=='threshold_scale':
            f=target/'fixed/threshold.bin.gz';v=int.from_bytes(gzip.decompress(f.read_bytes()),'little')//2
            raw=v.to_bytes((v.bit_length()+7)//8,'little');compressed=gzip.compress(raw,mtime=0);f.write_bytes(compressed)
            man=target/'fixed/MANIFEST.json';o=json.loads(man.read_text())
            for r in o:
                if r['name']=='threshold':r.update(sha256=hashlib.sha256(raw).hexdigest(),gzip_sha256=hashlib.sha256(compressed).hexdigest())
            man.write_text(json.dumps(o))
        else:
            f=target/'generated/integer10.json';o=json.loads(f.read_text());tc=o['named_nodes']['tc']
            one=next(i for i,n in enumerate(o['nodes'])if n['kind']=='literal'and n['value']==1)
            o['nodes'][tc]['right']=one;f.write_text(json.dumps(o))
        run=subprocess.run([sys.executable,str(target/'verify_integer.py')],capture_output=True,text=True)
        if run.returncode==0:raise RuntimeError('corruption accepted: '+mode)
        results.append(dict(control=mode,rejected=True,last_error=run.stderr.strip().splitlines()[-1]))
(ROOT/'NEGATIVE_CONTROLS.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
