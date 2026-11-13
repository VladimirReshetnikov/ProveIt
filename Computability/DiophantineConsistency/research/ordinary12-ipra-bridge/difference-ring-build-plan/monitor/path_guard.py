"""Point-in-time output-path guards, not adversarial race protection."""
from pathlib import Path

ROOT=Path(__file__).resolve().parents[6]

def default_protected():
 paths=[ROOT,Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun'),
        Path('/tmp/ipra-aq29-fresh-project-pair'),Path('/tmp/ipra-aq29-fresh-source-closure-v2'),
        Path('/tmp/ipra-model-diff-closure-plan-01'),Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0')]
 paths.extend(x for x in Path('/tmp').glob('ipra-ordinary12-coexistence-source-*') if x.is_dir())
 return paths

def fresh_output(path,protected=()):
 out=Path(path).absolute()
 if out.exists() or out.is_symlink():raise ValueError(('existing output',str(out)))
 for parent in out.parents:
  if parent.is_symlink():raise ValueError(('symlink output ancestor',str(parent)))
 resolved=out.resolve(strict=False)
 if resolved!=out:raise ValueError(('noncanonical output',str(out)))
 for p in (*default_protected(),*protected):
  q=Path(p).resolve(strict=False)
  if resolved.is_relative_to(q) or q.is_relative_to(resolved):raise ValueError(('output/protected overlap',str(resolved),str(q)))
 return resolved
