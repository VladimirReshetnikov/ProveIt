"""Re-audit the complete parallelity corpus and require historical proof identity."""
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from normal_orbit_research.parallelity import audit


def encode(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()


def main(output):
    root=Path(__file__).resolve().parents[2];baseline=root/'synthesis/data/parallelity-audit.json';old=json.loads(baseline.read_bytes())
    with TemporaryDirectory(prefix='unknot-selector-replay-')as folder:
        path=Path(folder)/'audit.json';audit(path);new=json.loads(path.read_bytes())
    assert old['records']==new['records']
    assert old['source_proofs']==new['source_proofs']
    for key in ('finite_cases','pilot_cases','literal_vertex_links_checked','literal_polygons','large_binary_cases','pilot_sha256','corpus_sha256'):
        assert old[key]==new[key],key
    result={k:v for k,v in new.items()if k not in ('records','source_proofs')}
    result.update(baseline_audit_sha256=sha256(baseline.read_bytes()).hexdigest(),
        identical_finite_proof_records=len(new['records']),identical_saved_source_proofs=len(new['source_proofs']),
        finite_records_sha256=sha256(encode(new['records'])).hexdigest(),saved_source_proofs_sha256=sha256(encode(new['source_proofs'])).hexdigest())
    Path(output).write_bytes(encode(result)+b'\n');print('All finite records and saved source proofs remain identical.',flush=True)

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',required=True);main(parser.parse_args().output)
