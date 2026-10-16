Prepared, unexecuted archival helper for repaired NEXT829 source 5e5af281970d9f5c1ea637fa6b32fa7c4551a810. Run only after the three actual core/shared/supplemental stages pass, keeping source/HEAD/inventory fixed.

Use archive.py --snapshot PATH SHA256 --source-ledger PATH SHA256 --core PATH SHA256 --shared PATH SHA256 --supplemental PATH SHA256 --extra-evidence PATH SHA256 --output NEW_ABSOLUTE_TMP_DIRECTORY.

Required scopes remain572/1915/351 modules and1/65/18 roots, fresh union1964. No historical retention. Preserve failed f4e4 core and targeted repair evidence in the extra manifest. Only the source-commit literal differs from the independently reviewed f4e4 archival helper; runtime validation is unchanged.
