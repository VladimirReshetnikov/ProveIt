from pathlib import Path
import subprocess,json,sys
base=Path(__file__).resolve().parent
repo=base/'Foundation.git'
rev='32e1a0956a8622fad067328ca1959729a7634428'
manifest=base/'manifest.json'
data=json.loads(manifest.read_text())
for p in sys.argv[1:]:
    try:
        blob=subprocess.check_output(['git','-C',str(repo),'rev-parse',rev+':'+p],text=True,stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        print(p,'MISSING',flush=True)
        continue
    dest=base/'source'/p
    if not dest.exists():
        raw=subprocess.check_output(['git','-C',str(repo),'cat-file','blob',blob])
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(raw)
    data['source'][p]=blob
    manifest.write_text(json.dumps(data,indent=2)+'\n')
    print(p,blob,dest.stat().st_size,flush=True)
