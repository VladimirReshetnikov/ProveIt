#!/usr/bin/env python3
"""Recreate the accepted-provider overlay; replay verifies its entire local graph."""
from pathlib import Path
import subprocess,tempfile
base=Path('/tmp/pra-sndidx-family-independent-rd0fj_5x/lib')
entries=[('/tmp/pra-fstidx-derivation-bound-lz5iam21/lib',['PRAFstIdxDerivationBound','PRAFstIdxDerivationBoundChecks']),('/tmp/pra-lenbit-bound-9nnf4u_8/lib',['PRALenbitWitnessBound','PRALenbitWitnessBoundChecks']),('/tmp/pra-ext-bound-asis2thv/lib',['PRAExtWitnessBound','PRAExtWitnessBoundChecks']),('/tmp/pra-ext-rewriting-bound-r78_dct1/lib',['PRAExtRewritingBound','PRAExtRewritingBoundChecks']),('/tmp/pra-pair3-bound-independent-xmaajon3/lib',['PRAPairTripleWitnessBound','PRAPairTripleWitnessBoundChecks']),('/tmp/pra-bnd-rewriting-independent-7n8kd56j/lib',['PRABndRewriting','PRABndRewritingChecks'])]
parent=Path(tempfile.mkdtemp(prefix='pra-after-three-induction-overlay-'))/'lib';dst=parent/'DiophantineConsistency';dst.mkdir(parents=True)
for f in (base/'DiophantineConsistency').glob('*.olean'):(dst/f.name).symlink_to(f.resolve())
for folder,names in entries:
 for n in names:
  f=Path(folder)/'DiophantineConsistency'/(n+'.olean')
  if not f.is_file():raise RuntimeError(f'missing object {f}')
  p=dst/f.name
  if p.exists() or p.is_symlink():p.unlink()
  p.symlink_to(f.resolve())
foundation=base/'Foundation'
if not foundation.is_dir():raise RuntimeError('missing Foundation provider')
(parent/'Foundation').symlink_to(foundation.resolve(),target_is_directory=True)
print('OVERLAY',parent,flush=True)
raise SystemExit(subprocess.call(['python3',str(Path(__file__).resolve().parent/'replay.py'),'--parent',str(parent)]))
