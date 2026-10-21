from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).parent))
import check_joint_fold as ck
import argparse, hashlib
cli=argparse.ArgumentParser(description=__doc__)
cli.add_argument('--baseline',type=Path,required=True)
cli.add_argument('--output',type=Path,required=True)
cli.add_argument('--variants',type=Path)
args=cli.parse_args()
if not __debug__:raise RuntimeError("Run without Python optimization")
assert hashlib.sha256(args.baseline.read_bytes()).hexdigest()=='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088', 'Wrong K217 baseline'
args.output.mkdir(parents=True,exist_ok=True)

T,start=ck.read(args.baseline);I=ck.domain(T,start,7);Q=sorted({q for q,b in T})
with (args.output/'search-domain.txt').open('w')as f:
 print(len(Q),file=f)
 for q in Q:
  print(q,*T[q,0],*T[q,1],file=f)
 for q in Q:
  a=sorted(I[q]);print(q,len(a),*a,file=f)
