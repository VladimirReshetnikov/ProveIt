# Reproduction command correction

The reproduction commands in the frozen README omit required Python flags and refer to the wrong working directory. From the `Computability/DiophantineConsistency` directory, use:

```sh
python3 -I -S -B research/nine-sharing-sign32-sextic-lean-draft/generate.py
python3 -I -S -B research/nine-sharing-sign32-sextic-lean-draft/check.py
python3 -I -S -B research/nine-sharing-sign32-sextic-lean-draft/check_bridge.py
```

These scripts write their outputs. For an independent replay, use a temporary copy preserving the relative `research/nine-sharing-sign32-sextic-lean-draft/` and `research/nine-sharing-sign32-sextic-candidate-v2/seed.json` paths, and compare the resulting hashes with the frozen packet. The README and all previously pinned source and result bytes are unchanged.
