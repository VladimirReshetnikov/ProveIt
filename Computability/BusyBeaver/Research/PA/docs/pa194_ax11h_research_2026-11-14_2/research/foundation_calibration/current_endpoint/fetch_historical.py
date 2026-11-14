from pathlib import Path
import subprocess,json,sys
base=Path(__file__).resolve().parent
repo=Path('/workspace/scratch/d50241bd3620/ProveIt')
prefix='Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/vendor/Foundation/'
rev='1c9524d8bf2e0a27b9a16ff622359927f536e663'
manifest=base/'historical_manifest.json'
data=json.loads(manifest.read_text()) if manifest.exists() else {'revision':rev,'prefix':prefix,'source':{}}
if 'source' not in data:
    data={'revision':rev,'prefix':prefix,'source':data}
for p in sys.argv[1:]:
    p=p.replace('Foundation/FirstOrder/Bootstrapping/','Foundation/FirstOrder/Arithmetic/Bootstrapping/')
    try:
        blob=subprocess.check_output(['git','-C',str(repo),'rev-parse',rev+':'+prefix+p],text=True,stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        print(p,'MISSING',flush=True)
        continue
    dest=base/'historical'/p
    if not dest.exists():
        raw=subprocess.check_output(['git','-C',str(repo),'cat-file','blob',blob])
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(raw)
    data['source'][p]=blob
    manifest.write_text(json.dumps(data,indent=2)+'\n')
    print(p,blob,dest.stat().st_size,flush=True)
