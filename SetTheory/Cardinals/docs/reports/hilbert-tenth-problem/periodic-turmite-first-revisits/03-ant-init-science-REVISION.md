# Revision2: exact inventory hardening

Version1 is preserved unchanged. Its manifest SHA256 is defcf2e114124e656faa228b1cb1309649c8d7d02ee9c8b5023e37c340a6033f; its exact manifest is retained at lineage/MANIFEST.v1.json.

The sole existing-file change is replay.py. Previously every file named MANIFEST.json was excluded from the inventory, regardless of directory, and nonregular entries were not explicitly rejected. Revision2 excludes only the root MANIFEST.json, uses lstat to reject symlinks and every non-directory/nonregular entry, and requires the root manifest itself to be regular before reading it. Nested extra MANIFEST.json files now trigger the exact-inventory mismatch.

Version1 replay.py SHA256: 50945723f2b05e9d39b654309e55a0bc3dd44bc9ae80659a3c701fbca19c8c8d
Version2 replay.py SHA256: 9a339b8c007bef164026ec3fc2c4f581606eb27e1f7b5d0994120a1ee1e8c0ef

All mathematical proofs, arithmetic source generators, prescribed recipe data, witness/count/degree results and independent mathematical audits are byte-identical to version1. The new revision note, v1 manifest copy and regenerated v2 manifest record this operational-only change.
