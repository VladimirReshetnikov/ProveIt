"""Run the full finite proof; checkpoints remain reusable in generated/."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,as_completed
import argparse,subprocess,sys,json,time
root=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--jobs',type=int,default=4);p.add_argument('--output',type=Path,default=root/'generated');args=p.parse_args()
assert args.jobs>=1
def check(m):
    subprocess.run([sys.executable,str(root/'replay_one.py'),str(m),'--output',str(args.output),'--reuse'],check=True)
    return m
start=time.time();done=[]
with ThreadPoolExecutor(max_workers=args.jobs)as pool:
    for future in as_completed([pool.submit(check,m)for m in range(111,1,-1)]):
        done.append(future.result())
        (args.output/'replay_progress.json').write_text(json.dumps({'completed':sorted(done)},indent=2)+'\n')
assert sorted(done)==list(range(2,112))
print('All 110 finite orders independently replayed in',time.time()-start,'seconds.')
