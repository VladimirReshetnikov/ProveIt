# generator/

This folder rebuilds `../machines/A361.tm`, `B354.tm`, `R3s336.tm` and `R3Y1_335.tm` byte for byte:

```
python mkcand.py A361.json A361     # writes A361.tm (361 states: 66 framework + 295 DAG)
python mkcand.py B354.json B354     # writes B354.tm (354 states: 66 framework + 288 DAG)
python mkcand.py R3s336.json R3s336 # writes R3s336.tm (336 states: 66 framework + 270 DAG)
python mkcand.py R3Y1_335.json R3Y1_335  # writes R3Y1_335.tm (335 states: 66 framework + 269 DAG)
```

- `TMBuilder.py`, `tm.py`, `tmdb.py` and `zf2.py` are Andrew Wade's files from
  <https://codeberg.org/ajwade/turing_machine_explorer>, unmodified. They are under MIT No Attribution;
  see `LICENSE.wade`.
- `zfp.py` is our program. It contains Wade's subroutines plus:
  - a clause table;
  - per-clause parameter-role permutations;
  - axiom-text variants (built with `forms.py`);
  - the optional program changes listed in `../README.md`.
- The JSON files hold the configurations found by search: clause order, permutations, options and
  variants.
