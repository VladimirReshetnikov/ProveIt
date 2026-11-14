import concurrent.futures
import hashlib
import json
import pathlib
import urllib.request
import zipfile

manifest = json.loads(pathlib.Path('sources_manifest.json').read_text())
base = pathlib.Path('upstream')
base.mkdir(exist_ok=True)

def get(item):
    url = (f"https://raw.githubusercontent.com/{manifest['repository']}/"
           f"{manifest['commit']}/{item['path']}")
    data = urllib.request.urlopen(url, timeout=90).read()
    digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert digest == item['git_blob_sha1'], (item['name'], digest)
    path = base / item['name']
    path.write_bytes(data)
    if path.suffix == '.zip':
        target = base / path.stem
        with zipfile.ZipFile(path) as archive:
            for info in archive.infolist():
                dest = (target / info.filename).resolve()
                assert dest.is_relative_to(target.resolve())
            archive.extractall(target)
    return item['name'], len(data), hashlib.sha256(data).hexdigest()

with concurrent.futures.ThreadPoolExecutor(max_workers=6) as executor:
    for item in executor.map(get, manifest['files']):
        print(*item, flush=True)
