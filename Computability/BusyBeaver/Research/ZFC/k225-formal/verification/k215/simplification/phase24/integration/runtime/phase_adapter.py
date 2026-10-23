"""Owned phase24 adapter: validates pinned own helper bytes before exact expansion.
No supplied proposal source is imported. Entry points preserve the accepted CLI.
The source expansion is a reviewed fixed recipe, never arbitrary configuration code.
"""
from pathlib import Path
import hashlib,json

def digest(data):return hashlib.sha256(data).hexdigest()
def launch(kind,wrapper,config_sha,adapter_sha):
 wrapper=Path(wrapper);assert wrapper.is_file() and not wrapper.is_symlink()
 wrapper=wrapper.resolve();directory=wrapper.parent
 adapter=directory/'phase_adapter.py';config=directory/'phase24.json'
 assert digest(adapter.read_bytes())==adapter_sha
 assert digest(config.read_bytes())==config_sha
 cfg=json.loads(config.read_text());assert cfg['phase']==24
 assert wrapper.name==cfg['entrypoints'][kind]
 runtime={str(adapter):adapter_sha,str(config):config_sha}
 for name in cfg['entrypoints'].values():
  path=directory/name;assert path.is_file() and not path.is_symlink()
  runtime[str(path)]=digest(path.read_bytes())
 for profile in cfg['helpers'].values():
  path=Path(profile['base_path']);assert digest(path.read_bytes())==profile['base_sha256']
  runtime[str(path)]=profile['base_sha256']
 profile=cfg['helpers'][kind];source=Path(profile['base_path']).read_text()
 for edit in profile['replacements']:
  assert source.count(edit['before'])==edit['count'] and edit['count']>0
  source=source.replace(edit['before'],edit['after'])
 assert digest(source.encode())==profile['expanded_sha256']
 namespace={'__name__':'__main__','__file__':str(wrapper),
  'P24_RUNTIME_INPUTS':runtime,
  'P24_RUNNER_SHA':runtime[str(directory/cfg['entrypoints']['runner'])]}
 exec(compile(source,str(wrapper)+'::'+kind,'exec'),namespace)
