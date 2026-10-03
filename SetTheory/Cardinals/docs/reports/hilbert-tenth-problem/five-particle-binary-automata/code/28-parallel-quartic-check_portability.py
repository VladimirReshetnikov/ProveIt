"""Rebuild the tiny certificate after relocating only manifest-listed files."""
from pathlib import Path
import tempfile,shutil,subprocess,sys,json,hashlib
R=Path(__file__).resolve().parent;m=json.loads((R/'MANIFEST.json').read_text())
with tempfile.TemporaryDirectory(prefix='parallel-certificate-check-')as d:
    dst=Path(d)
    for name in list(m['files'])+['MANIFEST.json']:
        p=dst/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(R/name,p)
    run=subprocess.run([sys.executable,'-B','-c',"import json;from compiler import Certificate;s=json.load(open('example-source.json'));c=Certificate(s,2,1);v=c.witness([0,5],[1,6]);print(json.dumps({'score':c.circuit.score(v),'witnesses':c.circuit.ledger()['witnesses'],'new_rule_radius':c.ledger()['new_rule_radius']}))"],cwd=dst,check=True,capture_output=True,text=True)
    result=json.loads(run.stdout)
    if result!={'score':0,'witnesses':1494,'new_rule_radius':1698}:raise RuntimeError(result)
    subprocess.run([sys.executable,'-B','verify_bundle.py'],cwd=dst,check=True,capture_output=True,text=True)
print(json.dumps(dict(status='PASS',relocated_compiler=result,compiler_sha256=hashlib.sha256((R/'compiler.py').read_bytes()).hexdigest(),circuit_sha256=hashlib.sha256((R/'circuit.py').read_bytes()).hexdigest(),temporary_directory_removed=True),sort_keys=True))
