#!/usr/bin/env python3
"""Portable, fail-closed replay of the frozen independent Report58 audit.
Run: python3 -I -S -B replay_report58.py --packet-dir ABS --audit-dir ABS --output-dir NEW_ABS
Only three SHA-256-pinned independent checkers are compiled. Scientific bytes are
never edited. A restricted logical-path facade preserves historical receipt text.
"""
import argparse
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import traceback

FROZEN_PACKET = '/workspace/shared/five-signal-diophantine58-20261004'
FROZEN_AUDIT = '/workspace/shared/five-signal-certificate58-independent-audit-20261004'
FROZEN_PHYSICAL = '/workspace/shared/five-signal-obstruction-independent-audit-20261004/INDEPENDENT_AUDIT.md'
EXPECTED = {'packet': {'PACKET_MANIFEST.json': '8e2d450010e9029d500bfd2dec67995ec61d54ab08665d449c3b9d18143c965b', 'PROOF.md': 'b55f301d2b1531f348163f026b3c1f7f827669d266afb77d854eef7ceb21c482', 'README.md': '4d3f61b0b606e214e340a25b38d208e711ff6996a31b502d5fceb2ac23d7c75a', 'SCIENCE_HANDOFF.json': '8c9cb465529ba3f36eac750e23592f00bd797b6868331c5574da9ea5c633df53', 'check_semantics.py': '5f690e37c525e5247af5dcd7b2847da66c7a4765b8b63b2b3521d4f3104bfe82', 'emit_certificate.py': '2093773340d3e7a9891d786e99711a2662a61b952b1c40a8bb1af5392d33ac6d', 'evidence/one-input-linear.dag.json': 'b64a268cc03033c13c020abc0cb12c1c81f9ba630aa75812ac84b08e2971efc3', 'evidence/one-input-linear.receipt.json': '33054723720f081527769a4ca6e894a8208d55d88a85d0acc9e46503c07ea726', 'evidence/one-input-quartic.dag.json': '3d2fe384ea6564950e0ca4b392396e3fa4489d88e1974dfd269a42610428ed24', 'evidence/one-input-quartic.receipt.json': '7946a49e769851205dccb4649c50063aacaf4896dbeac394d4b8146e0bd8d358', 'evidence/semantic-checks.json': '5c98f9536cb517b629cafc9a5382cd82e0e11b274d8b76b650579ab8c94a4cf2', 'evidence/semantic-optimized.stdout.json': '5c98f9536cb517b629cafc9a5382cd82e0e11b274d8b76b650579ab8c94a4cf2', 'evidence/summary.json': '64e9eaed2f6a03bb302f0acec68f38a34502866d0a1cd2691f561d74331c6178', 'evidence/three-input-linear.dag.json': '707721d1a8dca21b29acda57df8df6e763a1df89761f513122bec5edd9261ccc', 'evidence/three-input-linear.receipt.json': 'e3d061b85cfc413fba16b275fc2296f037b6a5810ca020fe41f53671acb33ee0', 'evidence/three-input-quartic.dag.json': '11c1a3d6eca23af2a9ede232e1a5ab36ba395a3235a424ef76ff14d5e19f14d0', 'evidence/three-input-quartic.receipt.json': '1ef8f0f998892d5b00943d64eb372c41710999d75013b02986a70d17cc35e16d', 'freeze_manifest.py': '6b4624db8d2a948e244ace6a2bf0360e8aac17ab228f9abed956f7f6754d63ff', 'independent_audit/EXPANDED_SOURCE_REVIEW.md': 'fe7727fa09e90a6cc59de39af9af22ef4d3f77b6d69ecf4d12bccc15e655b482', 'independent_audit/MANIFEST.sha256': '163c40d908916ba42d049c2e5aacdc87fa27b756fcf0ab2bedd25a20e13c4486', 'independent_audit/audit-receipt.json': '2df25deb5807799132f8abcae1fa61a7655d3b513d82d25f651e989b8ae4ee3d', 'independent_audit/check_dags.py': '0960c524d21682c4e15255051f8e6bcabfd8acb8a107139d92331531daa5a81a', 'review/ALGEBRA_REVIEW.md': 'd640360159e2ec6436bc85c2e61a079bded5654ac372aca6e69588d7fd56e2b5', 'sources/BOUNDARY_AND_ARITHMETIC.md': '9642699a09f3ebc558fb1268c61370fb514839404e834acf288f9504e3e81b77', 'sources/INDEPENDENT_AUDIT.md': 'b119df1c0be8685078b011c14e3c71decabce343f9ba9041ee6f97b4c58a5226', 'sources/LICENSE.mathlib-Apache-2.0.txt': 'cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30', 'sources/NOTICE.md': '45800127cf9faad081c34d4ecf8d5689eba081b9483c842ee44138cf5468242b', 'sources/POWER_SOURCE_NOTES.md': '56051940c6ce974dd891f2fb549ece313b710d9ac60ee1591c4e976887ca2435', 'sources/SOURCE_PINS.json': '11d2372f087c5fb75fd23473d09839b595fe7ec5484cbbb9cb55bd202f203a48', 'sources/five-signal-PROOF.md': '1bea81f8f2e6693d4b7958fb44763eb644663d208fe70c577e0137184e17a725', 'sources/pell-dependency.json': '4117596dd3599d21ab8402b2d62313450828d56c85aea5f3f20cd814d71b455b', 'sources/pell-source.lean': '993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a', 'sources/prior-build_certificate.py.txt': '722db1e253ac3d241fdb538c46a86ffc15e6c208cb8116d168883b6c5bfaa799'}, 'audit': {'AUDIT_MANIFEST.json': '23e0751b30845d4925cd4ebb884ed537465715a0d184456d775a76ebfcac30ba', 'INDEPENDENT_AUDIT.md': 'e790c49af8d56190740520637af65d436e75f7af2a30856590646f3bf6372dbd', 'POWER_AUDIT.md': '90eab5e5b8f1fc369805e4722a0bc6cbc6534cb9997a2038095ae44157be1df3', 'POWER_DAG_RECEIPT.json': '5b3af57fa307404693bfe6fba020763bd4b7803ab364c726f385dcd3aa8dc994', 'arithmetic-receipt.json': '19cee408a8244382e18a8561a7288cfb903de6a21eb2bb506aa3e4a3cb3aa9fd', 'arithmetic-run.stdout.json': 'f7fd96950e74f15e08f9b259ed10307e10ad4651a3a06efa94ebaa4b45449b9b', 'audit_arithmetic.py': '2557c2e769b9bc128f87a5af014fe1e00df4bbb6a4a9a651fd4f19880d8312f5', 'audit_exact_source.py': '36f5cd9af5fef1ef1f3408509c8c8b170ab40d043702eef5a0dbb709803a5cf1', 'check_power_dag_independent.py': '36db04154e4d7f255b1fb5b78ed01ca74054e5239b0dd464cb12db3265cf3a82', 'exact-source-receipt.json': 'abf4b13afb1d2b839255f9fc49fdda26c7cfbadb51042d99bdf657cc3adb7f88', 'full-positive-witnesses.json': '6347a9f792c9f0cf198cef8cd0d4c5de6acfa036fa2917e7a3c05889ab47138c'}}
CHECKERS = ('audit_exact_source.py', 'check_power_dag_independent.py', 'audit_arithmetic.py')
RESULTS = ('exact-source-receipt.json', 'POWER_DAG_RECEIPT.json', 'arithmetic-receipt.json', 'full-positive-witnesses.json')

class ReplayError(Exception):
    pass

def require(condition, message):
    # Deliberately not an assert: path/authentication checks survive -O.
    if not condition:
        raise ReplayError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def safe_absolute(value, must_exist=True, directory=True):
    require(isinstance(value, str) and value.startswith('/') and not value.startswith('//'), 'paths must be explicit canonical absolute paths')
    require('\x00' not in value, 'NUL in path')
    p = Path(value)
    require(str(p) == value and all(x not in ('.', '..') for x in value.split('/')), 'path must be canonical without dot components or trailing slash')
    # Check every existing ancestor, including root, without following symlinks.
    parts = [p, *p.parents]
    for q in reversed(parts):
        try:
            st = q.lstat()
        except FileNotFoundError:
            if q == p and not must_exist:
                continue
            raise ReplayError('missing path component: ' + str(q))
        require(not stat.S_ISLNK(st.st_mode), 'symlink path component rejected: ' + str(q))
        if q != p or directory:
            require(stat.S_ISDIR(st.st_mode), 'directory required: ' + str(q))
    if must_exist:
        require(p.exists(), 'missing path: ' + value)
    return p

def tree_snapshot(root):
    """Authenticate file bytes and retain preservation-relevant metadata.
    atime is intentionally excluded because reading may update it.
    """
    records = {}
    def visit(p, rel):
        st = p.lstat()
        require(not stat.S_ISLNK(st.st_mode), 'symlink in input tree: ' + str(p))
        require(stat.S_ISREG(st.st_mode) or stat.S_ISDIR(st.st_mode), 'nonregular input entry: ' + str(p))
        row = {'kind': 'directory' if stat.S_ISDIR(st.st_mode) else 'file',
               'mode': stat.S_IMODE(st.st_mode), 'size': st.st_size, 'mtime_ns': st.st_mtime_ns,
               'ctime_ns': st.st_ctime_ns, 'device': st.st_dev, 'inode': st.st_ino,
               'links': st.st_nlink, 'uid': st.st_uid, 'gid': st.st_gid}
        if stat.S_ISREG(st.st_mode):
            fd = os.open(p, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
            try:
                fst = os.fstat(fd)
                require((fst.st_dev, fst.st_ino) == (st.st_dev, st.st_ino), 'input changed while opening')
                with os.fdopen(fd, 'rb', closefd=False) as f:
                    raw = f.read()
                require(len(raw) == st.st_size, 'input size changed while reading')
                row['sha256'] = digest(raw)
            finally:
                os.close(fd)
        records[rel] = row
        if row['kind'] == 'directory':
            for child in sorted(p.iterdir(), key=lambda x: x.name):
                visit(child, child.name if rel == '.' else rel + '/' + child.name)
    visit(root, '.')
    return records

def authenticate(root, kind):
    snapshot = tree_snapshot(root)
    actual = {name: row['sha256'] for name, row in snapshot.items() if row['kind'] == 'file'}
    require(actual == EXPECTED[kind], 'source authentication failed for ' + kind + ': missing, extra, or altered file')
    expected_dirs = {'.'}
    for name in EXPECTED[kind]:
        expected_dirs.update(str(p) for p in Path(name).parents if str(p) != '.')
    require({name for name, row in snapshot.items() if row['kind'] == 'directory'} == expected_dirs,
            'source authentication failed for ' + kind + ': unexpected directory inventory')
    return snapshot

def copy_pinned_tree(src, dst, kind):
    dst.mkdir(mode=0o700)
    for rel, expected_hash in sorted(EXPECTED[kind].items()):
        source = src / rel
        fd = os.open(source, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
        try:
            with os.fdopen(fd, 'rb', closefd=False) as f:
                raw = f.read()
        finally:
            os.close(fd)
        require(digest(raw) == expected_hash, 'source changed while staging: ' + rel)
        target = dst / rel
        target.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        with target.open('xb') as f:
            f.write(raw)
        target.chmod(0o400)
    # Read-only private staging; the original inputs are never chmodded.
    for directory in sorted([dst, *[p for p in dst.rglob('*') if p.is_dir()]], key=lambda p: len(p.parts), reverse=True):
        directory.chmod(0o500)

class LogicalPath:
    """Small path facade covering only operations used by the pinned checkers.
    Printed names remain frozen; I/O is restricted to authenticated staged files
    and four fresh result files. It is not a general filesystem sandbox.
    """
    def __init__(self, logical, mapping):
        self.logical = str(logical)
        self.mapping = mapping
        require(self.logical.startswith('/') and '..' not in self.logical.split('/'), 'invalid logical path')
    def __str__(self):
        return self.logical
    def __lt__(self, other):
        return self.logical < other.logical
    @property
    def name(self):
        return Path(self.logical).name
    def __truediv__(self, value):
        require(isinstance(value, str) and not value.startswith('/') and '..' not in value.split('/'), 'invalid logical child')
        return LogicalPath(str(Path(self.logical) / value), self.mapping)
    def location(self, writing=False):
        packet, audit, result = self.mapping
        if self.logical == FROZEN_PHYSICAL:
            require(not writing, 'inherited physical source is read-only')
            return packet / 'sources/INDEPENDENT_AUDIT.md'
        for prefix, base, kind in ((FROZEN_PACKET, packet, 'packet'), (FROZEN_AUDIT, result if writing else audit, 'audit')):
            if self.logical.startswith(prefix + '/'):
                rel = self.logical[len(prefix)+1:]
                if writing:
                    require(prefix == FROZEN_AUDIT and rel in RESULTS, 'unapproved checker write')
                else:
                    require(rel in EXPECTED[kind], 'unapproved checker read: ' + self.logical)
                return base / rel
        raise ReplayError('unmapped logical path: ' + self.logical)
    def read_bytes(self):
        return self.location().read_bytes()
    def read_text(self):
        return self.read_bytes().decode('utf-8')
    def write_text(self, value):
        require(isinstance(value, str), 'checker output must be text')
        destination = self.location(writing=True)
        with destination.open('x', encoding='utf-8', newline='') as f:
            return f.write(value)
    def glob(self, pattern):
        require(self.logical == FROZEN_PACKET + '/evidence' and pattern == '*.dag.json', 'unapproved checker glob')
        return [LogicalPath(FROZEN_PACKET + '/' + name, self.mapping)
                for name in sorted(EXPECTED['packet'])
                if name.startswith('evidence/') and name.count('/') == 1 and name.endswith('.dag.json')]

def worker(packet_value, audit_value, result_value):
    require(sys.flags.optimize == 0 and sys.flags.isolated == 1 and sys.flags.no_site == 1 and sys.dont_write_bytecode, 'worker isolation flags invalid')
    packet = safe_absolute(packet_value)
    audit = safe_absolute(audit_value)
    results = safe_absolute(result_value)
    authenticate(packet, 'packet')
    authenticate(audit, 'audit')
    mapping = packet, audit, results
    logs = {}
    for checker in CHECKERS:
        raw = (audit / checker).read_bytes()
        require(digest(raw) == EXPECTED['audit'][checker], 'checker authentication failure')
        namespace = {'__name__': 'frozen_independent_checker', '__file__': FROZEN_AUDIT + '/' + checker}
        # Compile exactly the authenticated scientific source bytes. No textual
        # or AST substitution; assert statements are forcibly enabled.
        exec(compile(raw, FROZEN_AUDIT + '/' + checker, 'exec', dont_inherit=True, optimize=0), namespace)
        namespace['ROOT'] = LogicalPath(FROZEN_PACKET, mapping)
        namespace['OUT'] = LogicalPath(FROZEN_AUDIT, mapping)
        namespace['Path'] = lambda path: LogicalPath(str(path), mapping)
        capture = io.StringIO()
        with contextlib.redirect_stdout(capture):
            if checker == 'check_power_dag_independent.py':
                # The frozen file's main guard serializes audit() without a main
                # function. Match that guard byte-for-byte in output formatting.
                text = json.dumps(namespace['audit'](), indent=2) + '\n'
                (namespace['OUT'] / 'POWER_DAG_RECEIPT.json').write_text(text)
                print(text)
            else:
                namespace['main']()
        logs[checker] = capture.getvalue()
    require(set(p.name for p in results.iterdir()) == set(RESULTS), 'unexpected regenerated result files')
    matches = {}
    for name in RESULTS:
        actual = (results / name).read_bytes()
        expected = (audit / name).read_bytes()
        require(actual == expected, 'regenerated receipt differs byte-for-byte: ' + name)
        matches[name] = digest(actual)
    require(logs['audit_arithmetic.py'].encode() == (audit / 'arithmetic-run.stdout.json').read_bytes(), 'arithmetic stdout differs from frozen run')
    return {'exact_receipt_sha256': matches, 'exact_arithmetic_stdout_sha256': digest(logs['audit_arithmetic.py'].encode()),
            'isolation': {'isolated': sys.flags.isolated, 'no_site': sys.flags.no_site, 'optimize': sys.flags.optimize,
                          'dont_write_bytecode': sys.dont_write_bytecode}, 'logs': logs}

# The child imports this authenticated adapter as inert definitions, then calls
# worker. Its source bytes are authenticated in the child before compilation.
CHILD_BOOTSTRAP = """
import hashlib, pathlib, sys
raw = pathlib.Path(sys.argv[1]).read_bytes()
if hashlib.sha256(raw).hexdigest() != sys.argv[2]:
    raise SystemExit('adapter changed before child startup')
ns = {'__name__': 'portable_replay_adapter', '__file__': sys.argv[1]}
exec(compile(raw, sys.argv[1], 'exec', dont_inherit=True, optimize=0), ns)
answer = ns['worker'](*sys.argv[3:6])
print(ns['json'].dumps(answer, sort_keys=True))
"""

def main(argv=None):
    require(sys.flags.optimize == 0, 'optimized Python is forbidden: assertions must remain enabled')
    require(sys.flags.isolated == 1 and sys.flags.no_site == 1 and sys.dont_write_bytecode,
            'invoke with python3 -I -S -B to isolate imports and disable bytecode writes')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet-dir', required=True)
    parser.add_argument('--audit-dir', required=True)
    parser.add_argument('--output-dir', required=True)
    args = parser.parse_args(argv)
    packet = safe_absolute(args.packet_dir)
    audit = safe_absolute(args.audit_dir)
    output = safe_absolute(args.output_dir, must_exist=False)
    require(not os.path.lexists(output), 'output directory must be fresh and nonexistent')
    require(packet != audit and packet not in audit.parents and audit not in packet.parents, 'input trees must be disjoint')
    require(all(output != p and p not in output.parents and output not in p.parents for p in (packet, audit)), 'output must be external to both input trees')
    before = {'packet': authenticate(packet, 'packet'), 'audit': authenticate(audit, 'audit')}
    adapter = safe_absolute(str(Path(__file__).absolute()), directory=False)
    adapter_raw = adapter.read_bytes()
    adapter_hash = digest(adapter_raw)
    output.mkdir(mode=0o700)
    sandbox = output / '_sandbox'
    sandbox.mkdir(mode=0o700)
    staged_packet, staged_audit = sandbox / 'packet', sandbox / 'audit'
    result_dir = output / 'results'
    result_dir.mkdir(mode=0o700)
    try:
        copy_pinned_tree(packet, staged_packet, 'packet')
        copy_pinned_tree(audit, staged_audit, 'audit')
        staged_before = {'packet': authenticate(staged_packet, 'packet'), 'audit': authenticate(staged_audit, 'audit')}
        completed = subprocess.run([sys.executable, '-I', '-S', '-B', '-c', CHILD_BOOTSTRAP,
                                    str(adapter), adapter_hash, str(staged_packet), str(staged_audit), str(result_dir)],
                                   cwd=str(sandbox), env={'PATH': os.defpath, 'LANG': 'C.UTF-8'},
                                   stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=120, check=False)
        (output / 'worker.stderr.txt').write_text(completed.stderr, encoding='utf-8')
        require(completed.returncode == 0, 'isolated checker worker failed: ' + completed.stderr.strip())
        answer = json.loads(completed.stdout)
        # Recheck exact output independently in the parent before issuing PASS.
        require(set(p.name for p in result_dir.iterdir()) == set(RESULTS), 'unexpected result-file inventory')
        for name in RESULTS:
            require((result_dir/name).read_bytes() == (audit/name).read_bytes(), 'parent receipt comparison failed: '+name)
        after = {'packet': authenticate(packet, 'packet'), 'audit': authenticate(audit, 'audit')}
        staged_after = {'packet': authenticate(staged_packet, 'packet'), 'audit': authenticate(staged_audit, 'audit')}
        require(before == after, 'input bytes or metadata changed during replay')
        require(staged_before == staged_after, 'staged inputs changed during replay')
        require(adapter.read_bytes() == adapter_raw, 'adapter changed during replay')
        logs = answer.pop('logs')
        for checker, value in logs.items():
            (output / (checker + '.stdout.txt')).write_text(value, encoding='utf-8')
        receipt = {'status': 'PASS', 'adapter_sha256': adapter_hash,
                   'input_paths': {'packet': str(packet), 'audit': str(audit)}, 'output_path': str(output),
                   'source_authentication': 'complete exact file inventory and SHA-256',
                   'original_inputs_preserved': True, 'private_staged_inputs_preserved': True,
                   'preservation': 'bytes, types, mode, size, mtime_ns, ctime_ns, device, inode, links, uid, gid; atime excluded',
                   'frozen_checker_bytes_unchanged': True, 'assertions_enabled': True,
                   'executed_checkers': {name: EXPECTED['audit'][name] for name in CHECKERS},
                   'replay': answer}
        (output / 'REPLAY_RECEIPT.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n', encoding='utf-8')
        print(json.dumps({'status': 'PASS', 'receipt': str(output/'REPLAY_RECEIPT.json')}, sort_keys=True))
    except BaseException as error:
        # Preserve failed output for inspection; it can never be reused as fresh.
        preserved = False
        try:
            preserved = before == {'packet': tree_snapshot(packet), 'audit': tree_snapshot(audit)}
        except BaseException:
            pass
        (output/'REPLAY_FAILURE.json').write_text(json.dumps({'status':'FAIL','error':str(error),'original_inputs_preserved':preserved},indent=2)+'\n',encoding='utf-8')
        raise

if __name__ == '__main__':
    try:
        main()
    except (ReplayError, OSError, ValueError, subprocess.SubprocessError) as exc:
        print('REPLAY REFUSED: ' + str(exc), file=sys.stderr)
        raise SystemExit(2)
