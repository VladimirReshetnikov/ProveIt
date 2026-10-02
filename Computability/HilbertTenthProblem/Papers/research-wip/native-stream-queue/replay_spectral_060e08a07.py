"""Extract authenticated spectral archives and replay the complete saved review."""
import hashlib,json,subprocess,sys,tempfile,zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
ARRIVAL='060e08a07d8e6a8ad5ab9ff6c1f7465e22e35630'
RECORDS=[('positive','Positive_Spectrum_Diophantine.zip','Positive_Spectrum_Diophantine','fe519471be068a0f7f5822c2fd89f1767f15d60379fb8d06d4b7b87f994dfdf8'),('spectral','Spectral_Guards_Without_Time_Expansion.zip','Spectral_Guards','0a5cf2d12333bab718453e1139622518f55b6361bd0e947f47d8e748d06f9e53'),('clock','clock_spectra_research.zip','clock_spectra_research','dbbcc5ed44b2a1b87da14ab863c32a5b125484480652fa9a04c5e0340082fb22')]
def require(v,message):
    if not v:raise ValueError(message)
def main():
    repo=next(p for p in HERE.parents if (p/'.git').exists())
    helper=HERE/'review_spectral_060e08a07.py'
    require(hashlib.sha256(helper.read_bytes()).hexdigest()=='a3c28def448d2bba825fc4b15ced1252ef06e661c0830955d2e8801574b74cdb','Review helper changed')
    with tempfile.TemporaryDirectory(prefix='spectral-archive-replay-') as td:
        td=Path(td);args=[sys.executable,str(helper)]
        for key,name,inner,wanted in RECORDS:
            p=repo/'docs/incoming'/name;data=p.read_bytes() if p.is_file() else subprocess.check_output(['git','show',f'{ARRIVAL}:docs/incoming/{name}'],cwd=repo)
            require(hashlib.sha256(data).hexdigest()==wanted,'Archive changed: '+name)
            p=td/name;p.write_bytes(data)
            with zipfile.ZipFile(p) as z:
                names=z.namelist();require(len(names)==len(set(names)) and all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names),'Unsafe archive');z.extractall(td)
            args.extend(['--'+key+'-root',str(td/inner)])
        args.extend(['--patch-dir',str(HERE/'spectral_repairs_060e08a07'),'--expect',str(HERE/'review_spectral_060e08a07.json')])
        p=subprocess.run(args,capture_output=True,text=True,timeout=600)
        require(p.returncode==0,p.stdout[-3000:]+p.stderr[-3000:])
        print(json.dumps(dict(status='PASS',original_author_commands=9,repaired_author_commands=9,complete_review_receipt_exact=True)))
if __name__=='__main__':main()
