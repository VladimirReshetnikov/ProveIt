#!/usr/bin/env python3
"""Mandatory immutable scientific-input pins, active in normal and -O modes."""
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
SOURCE_SHA256 = "fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3"
KNOWN_SHA256 = {'baseline/build_source.py': '1a531f13acaa7a022a9d5fefe2f21c4c39a612b697cac50adde901c477f737cf',
 'baseline/expected-outputs.json': '7fecff844a318cad7a6fa227def338aaa5233c51a75b63ad23729adb7c4d76de',
 'baseline/loader.py': 'c371be6b8f7382fb351821f66c86591467195250e41759eb9240e00321e2be08',
 'build-stats.json': '367e75fb65181e876f797401cb3f496e9bf2c2acfaf438783b70e992ab616c2a',
 'build_source.py': '9cf7b8c73766b3cacda741c5719caf61487bfef18b71fdc6ef37af60e7ce8016',
 'certificates.json': '86a26de87c5ea263f262fa9f5a60454a76289e5df6213b35223a810439ee0194',
 'compiler-reference/COMPILER_PROOF.md': '55ecb9c26bf0c2ce929c97187013171f8b8ec52ee30cb9a8703b41b1d106a4e8',
 'compiler-reference/SOURCE_SCHEMA.md': '4929b248dcf3f604694d3abf7d9efbf4649f6a5f8219661f01fc3469e900dcd3',
 'compiler-reference/reversible_binary.py': 'f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f',
 'dependency/PROOF.md': '8511e3d09f9c69a73838329159b5e1e8e3a250d235252bdc54b9d46449db2b1b',
 'dependency/UniversalTM15x2.tm.txt': 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae',
 'dependency/macro_certificates.json': '8f89296219f161dc4b55e902f667c9c4a63806e197cdd62b9594ef7decd51815',
 'dependency/tm_table.json': '0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a',
 'dependency/virtual3.json': '24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf',
 'dependency/virtual3.txt': '72338fd033a31d61e261d6074e6524d35a8d56022f8bcece411efb764fb02b5a',
 'loader.py': 'c4505405f705ac6e4d3442c56890f9eee136919d00ae94f3983475fc8d33cd1d',
 'normalized3.json': '7072d5c2806f43d01435aa35418b2cf918ef4d45eb6c173d96d0c7323fc12e06',
 'orientation-addendum/FIRST_ENCOUNTER_OPTIMALITY.md': 'f60a1b6659e8c059119036b2c0c4bb8075a4ff1699cec910af53ab53221e85be',
 'orientation-addendum/first-encounter-independent-audit.md': '65e0386c436c0de3e83183e604d5a2c2d39521881cc87b89c04d8efb21f4c7e7',
 'orientation-addendum/first-encounter-manifest.json': '21dc502d3ac4744e1f028f26443596756888b3a9d7f04c8ada003bfa0a986c09',
 'primitive3.json': '125e82a33b50cda150a03cb71a39c196b4ee61c0d302fc2350de720f2d931df3',
 'reversible2-primitives.json': '32dd31710c2590ab8d6c3869753702e3a35261f53a875e510fa1101076d81575',
 'reversible5.json': '2f426dda9743a80d1677bf367f4c75b1522efbd31cd6f07ab59ff7643b4ed31f',
 'source.json': 'fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'}

def verify_inputs():
    for name, expected in KNOWN_SHA256.items():
        path = ROOT / name
        if not path.is_file() or path.is_symlink():
            raise RuntimeError('Missing/nonregular mandatory pinned input: '+name)
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError('Mandatory input SHA-256 mismatch: '+name)
    if KNOWN_SHA256['source.json'] != SOURCE_SHA256:
        raise RuntimeError('Source identity mismatch')
    return len(KNOWN_SHA256)

if __name__ == '__main__':
    print('PASS:', verify_inputs(), 'mandatory scientific inputs match known SHA-256 pins')
