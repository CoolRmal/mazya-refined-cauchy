#!/usr/bin/env python3
"""Check that the definitions in MazyaRefinedCauchy/Defs.lean are identical to Challenge.lean's.

Solution.lean states the advertised theorems using the definitions from Defs.lean, while
Challenge.lean carries its own copy. Comparator requires the two to agree, so this check keeps them
textually identical: the block from `open scoped ContDiff` up to the first theorem docstring.
"""
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parent.parent
challenge = (root / "Challenge.lean").read_text(encoding="utf-8")
defs = (root / "MazyaRefinedCauchy" / "Defs.lean").read_text(encoding="utf-8")

start_marker = "open scoped ContDiff"
end_marker = "/-- **Theorem I(a).**"
block = challenge[challenge.index(start_marker):challenge.index(end_marker)]
defs_block = defs[defs.index(start_marker):defs.rindex("end MazyaRefinedCauchy")]

if block != defs_block:
    print("error: MazyaRefinedCauchy/Defs.lean is out of sync with Challenge.lean", file=sys.stderr)
    sys.exit(1)
print("Defs.lean matches Challenge.lean")
