# Decoder reassociation experiments

These are exploratory searches, not successful sub-194 machines.
The nominal fold heuristic is only a proposal stage; every accepted runtime
requires the full universal source check. Whole-program control-flow identity
is checked because preserving leaf order alone need not preserve structured jumps.

The two rotation tables passed runtime contracts but do not have a new blank-start
calibration. Their state count remains 194.

The bundled JSON and logs preserve the completed historical runs. To avoid
overwriting them, copy this archive before rerunning a search. From the root:

    python3 research/decoder/global_rotations.py
    python3 research/decoder/global_rotation_search.py 180

Imports use the bundled HAZ vendor reference with the exact primary grammar.
The scripts use Python standard library only and must not be run with -O.
No long search is necessary to replay the core runtime certificates.
