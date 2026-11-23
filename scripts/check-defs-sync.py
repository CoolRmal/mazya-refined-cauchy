#!/usr/bin/env python3
"""Check that MazyaRefinedCauchy/Defs.lean repeats Challenge.lean's header and definitions verbatim.

Comparator compares the elaborated definitions exactly (including auxiliary `_proof_` constants),
and these depend on the imports and options, so both the import header and the block from
`open scoped ContDiff` up to the first theorem docstring must agree.
"""
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parent.parent
ch = (root / "Challenge.lean").read_text(encoding="utf-8")
defs = (root / "MazyaRefinedCauchy" / "Defs.lean").read_text(encoding="utf-8")
marker = "@[expose] public section"
ok = ch[: ch.index(marker)] == defs[: defs.index(marker)]
start = "open scoped ContDiff"
block = ch[ch.index(start): ch.index("/-- **Theorem I(a).**")]
ok = ok and block == defs[defs.index(start): defs.rindex("end MazyaRefinedCauchy")]
if not ok:
    print("error: MazyaRefinedCauchy/Defs.lean is out of sync with Challenge.lean;"
          " run scripts/regen-from-challenge.py", file=sys.stderr)
    sys.exit(1)
print("Defs.lean matches Challenge.lean")
