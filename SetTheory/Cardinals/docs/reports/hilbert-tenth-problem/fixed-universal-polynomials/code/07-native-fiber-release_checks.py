"""Exact-inventory and mandatory-pin mutation tests on disposable external copies."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
import json
from pathlib import Path
import shutil
import tempfile
from verify_release import ROOT, MANIFEST, DIGEST, SCHEMA, require, inventory, verify
from replay import prepare_output, snapshot


def untrusted_seal(root, data=None):
    if data is None:
        files, dirs = inventory(root)
        entries = {}
        for name,path in sorted(files.items()):
            if name in (MANIFEST,DIGEST):
                continue
            raw = path.read_bytes()
            entries[name] = {'bytes':len(raw),'sha256':sha256(raw).hexdigest()}
        data = {'schema':SCHEMA,'files':entries,'directories':sorted(dirs)}
    raw = (json.dumps(data,indent=2)+'\n').encode('utf-8')
    (root/MANIFEST).write_bytes(raw)
    (root/DIGEST).write_text(sha256(raw).hexdigest()+'  '+MANIFEST+'\n')


def rejection(action, label):
    try:
        action()
    except (ValueError,OSError):
        return
    raise RuntimeError('mutation unexpectedly accepted: '+label)


def main():
    verify(ROOT)
    before = snapshot(ROOT)
    names = []
    with tempfile.TemporaryDirectory(prefix='report25-integrity-') as tmp:
        parent = Path(tmp)
        def trial(label, mutate, reseal=False):
            root = parent/label
            shutil.copytree(ROOT,root)
            mutate(root)
            if reseal:
                untrusted_seal(root)
            rejection(lambda:verify(root),label)
            names.append(label)
            shutil.rmtree(root)
        source = 'source/native_blocks.json'
        trial('changed-source',lambda p:(p/source).write_text('{}\n'))
        trial('missing-source',lambda p:(p/source).unlink())
        trial('additional-file',lambda p:(p/'unexpected.txt').write_text('unexpected'))
        trial('additional-hidden-file',lambda p:(p/'.unexpected').write_text('unexpected'))
        trial('additional-empty-directory',lambda p:(p/'unexpected').mkdir())
        trial('bytecode-directory',lambda p:((p/'__pycache__').mkdir(),(p/'__pycache__/unexpected.pyc').write_bytes(b'bad')))
        trial('file-symlink',lambda p:((p/source).unlink(),(p/source).symlink_to(ROOT/source)))
        trial('directory-symlink',lambda p:(p/'linked').symlink_to(p/'source',target_is_directory=True))
        trial('dangling-symlink',lambda p:(p/'dangling').symlink_to('missing'))
        trial('manifest-digest',lambda p:(p/DIGEST).write_text('0'*64+'  '+MANIFEST+'\n'))
        def duplicate_key(p):
            raw=(p/MANIFEST).read_text().replace('"schema":','"schema": "duplicate", "schema":',1).encode()
            (p/MANIFEST).write_bytes(raw)
            (p/DIGEST).write_text(sha256(raw).hexdigest()+'  '+MANIFEST+'\n')
        trial('duplicate-json-key',duplicate_key)
        def extra_entry(p):
            data=json.loads((p/MANIFEST).read_text());data['files']['../escape']={'bytes':0,'sha256':sha256(b'').hexdigest()};untrusted_seal(p,data)
        trial('manifest-parent-traversal',extra_entry)
        def directory_entry(p):
            data=json.loads((p/MANIFEST).read_text());data['directories'].append('unexpected');untrusted_seal(p,data)
        trial('manifest-additional-directory',directory_entry)
        trial('resealed-changed-source',lambda p:(p/source).write_bytes((p/source).read_bytes()+b'\n'),True)
        trial('resealed-missing-source',lambda p:(p/source).unlink(),True)
        trial('resealed-missing-relaxed-rank-proof',lambda p:(p/'source/PELL_RELAXED_AUXILIARY_PROOF.md').unlink(),True)
        trial('resealed-missing-second-term-proof',lambda p:(p/'proofs/second-term/THEOREM.md').unlink(),True)
        trial('resealed-missing-total-bitlength-proof',lambda p:(p/'proofs/total-bitlength/THEOREM.md').unlink(),True)
        trial('resealed-missing-canonical-transport',lambda p:(p/'proofs/canonical-transport/SUMMARY.md').unlink(),True)
        trial('resealed-additional-file',lambda p:(p/'unexpected.txt').write_text('unexpected'),True)
        trial('resealed-additional-directory',lambda p:(p/'unexpected').mkdir(),True)
        trial('resealed-missing-article',lambda p:(p/'report25.pdf').unlink(),True)
        trial('resealed-missing-review',lambda p:(p/'report25-math-review.md').unlink(),True)
        def pin_edit(p,kind):
            data=json.loads((p/'source-pins.json').read_text())
            if kind=='altered':data['files'][source]='0'*64
            elif kind=='missing':del data['files'][source]
            else:data['files']['source/additional.md']=sha256(b'new').hexdigest()
            (p/'source-pins.json').write_text(json.dumps(data,indent=2)+'\n')
        for kind in ('altered','missing','additional'):
            trial('resealed-'+kind+'-source-pin',lambda p,k=kind:pin_edit(p,k),True)
        trial('resealed-provenance-change',lambda p:(p/'delivery-provenance.json').write_text('{}\n'),True)
        rejection(lambda:prepare_output(ROOT/'inside',ROOT),'internal-output');names.append('internal-output')
        existing=parent/'existing';existing.mkdir()
        rejection(lambda:prepare_output(existing,ROOT),'existing-output');names.append('existing-output')
        link=parent/'link';link.symlink_to(existing,target_is_directory=True)
        rejection(lambda:prepare_output(link/'new',ROOT),'symlink-output');names.append('symlink-output')
        rejection(lambda:verify(link),'symlink-root');names.append('symlink-root')
    verify(ROOT)
    require(snapshot(ROOT)==before,'integrity testing changed the original release')
    print(json.dumps({'status':'PASS','optimized':not __debug__,'mutations_rejected':len(names),'tests':names,'original_release_unchanged':True},indent=2))


if __name__=='__main__':
    main()
