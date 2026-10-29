from pathlib import Path
import os,subprocess,tempfile,hashlib,json,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs'); S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'; old=Path('/tmp/pra-universal-current-6et0rjpw/lib'); root=Path('/tmp/pra-universal-equivalence-current');root.mkdir(exist_ok=True);lib=root/'lib';lib.mkdir(exist_ok=True); dst=lib/'DiophantineConsistency';dst.mkdir(exist_ok=True); logs=root/'logs';logs.mkdir(exist_ok=True)
if not (lib/'Foundation').exists():(lib/'Foundation').symlink_to((old/'Foundation').resolve(),target_is_directory=True)
for f in (old/'DiophantineConsistency').glob('*.olean'):
 p=dst/f.name
 if not p.exists() and f.stem!='PRAUniversalEquivalence':p.symlink_to(f.resolve())
search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+search,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
name='PRAUniversalEquivalence';n=len(list(logs.glob('attempt*.lean')))+1;src=S/(name+'.lean');snap=logs/('attempt%02d.lean'%n);snap.write_bytes(src.read_bytes()); out=dst/(name+'.olean'); cmd=['lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(out)];start=time.monotonic();p=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(logs/('attempt%02d.log'%n)).write_text(p.stdout);print('attempt',n,'exit',p.returncode,'seconds',time.monotonic()-start);print(p.stdout)
