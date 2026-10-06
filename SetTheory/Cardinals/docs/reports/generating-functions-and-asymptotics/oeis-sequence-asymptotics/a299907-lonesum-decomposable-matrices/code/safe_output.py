"""External-only, no-symlink, exclusive output creation for reader commands."""
import os,stat
from pathlib import Path


def preflight(destination,bundle_root):
    candidate=Path(destination)
    if '..' in candidate.parts:
        raise ValueError('output path must not contain parent traversal')
    path=Path(os.path.abspath(candidate))
    root=Path(bundle_root).resolve()
    if path==root or root in path.parents:
        raise ValueError('output must be outside the bundle')
    if os.path.lexists(path):
        raise FileExistsError('output already exists: '+str(path))
    for ancestor in reversed(path.parents):
        if os.path.lexists(ancestor):
            mode=ancestor.lstat().st_mode
            if stat.S_ISLNK(mode):raise ValueError('symlink output ancestor: '+str(ancestor))
            if not stat.S_ISDIR(mode):raise ValueError('non-directory output ancestor: '+str(ancestor))
    return path


def write_new(destination,data,bundle_root):
    """Recheck and create with directory-relative O_NOFOLLOW and O_EXCL."""
    path=preflight(destination,bundle_root)
    directory=os.open('/',os.O_RDONLY|os.O_DIRECTORY)
    try:
        for component in path.parent.parts[1:]:
            try:next_fd=os.open(component,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=directory)
            except FileNotFoundError:
                try:os.mkdir(component,0o755,dir_fd=directory)
                except FileExistsError:pass
                next_fd=os.open(component,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=directory)
            os.close(directory);directory=next_fd
        fd=os.open(path.name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o644,dir_fd=directory)
        with os.fdopen(fd,'wb') as output:output.write(data)
    finally:os.close(directory)
    return path
