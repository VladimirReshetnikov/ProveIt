# Proposed guarded join command

Do not execute until the independent v6 runner audit and final-manifest review pass. The runner uses fresh attempt/output paths and refuses overwrites.

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary12-direct90-ipra-join/run-v6.py \
  --attempt attempt01 \
  --completion Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact12-ipra-expanded-cone-rebuild-stage420/observations/batch-085/stage-0425/terminal.json \
  --completion-sha 5483e0f8444fcaeaec8a68929f63a77d2aa3435d27fafa1b89c78eed3dc57977 \
  --final-sha 7af1eefd72bdfb476941ae311cd2ddcbfd06d55f2e47e245b2a773679457519e \
  --cone Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact12-ipra-expanded-cone-rebuild-stage419-source-retry/cone-repinned.json \
  --cone-sha b5eb6a00e30599c49a851b38746582c75f1eaba2e6c9a66ed6a8adec9f4dc424
```

The command's outcome must be judged from the complete receipt and logs, including actual serialized header closure and six endpoint axiom reports. It does not independently authenticate package-transitive, dynamic, or all historical source-to-object ancestry.
