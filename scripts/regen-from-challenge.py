#!/usr/bin/env python3
"""Regenerate the files that must repeat parts of Challenge.lean verbatim.

* MazyaRefinedCauchy/Defs.lean: Challenge's import header and everything from `open scoped ContDiff`
  up to the first theorem docstring (opens, options, namespace, definitions).
* With --statements, also the statement parts of Solution.lean, MainA.lean and MainB.lean (only
  while their proofs are still placeholders; it overwrites them).
"""
import pathlib
import sys

root = pathlib.Path(__file__).resolve().parent.parent
ch = (root / "Challenge.lean").read_text(encoding="utf-8")
header = ch[: ch.index("@[expose] public section")]
defs_start = ch.index("open scoped ContDiff")
thm_a = ch.index("/-- **Theorem I(a).**")
thm_b = ch.index("/-- **Theorem I(b).**")
end = ch.index("end MazyaRefinedCauchy")

defs = (header + "@[expose] public section\n\n/-!\n# Definitions of the advertised statement\n\n"
        "These definitions must stay *identical* to the ones in `Challenge.lean` (including the import\n"
        "header and options): the statements proved in `Solution.lean` refer to them, and Comparator\n"
        "checks that they match. `scripts/check-defs-sync.py` checks this in CI.\n-/\n\n"
        + ch[defs_start:thm_a] + "end MazyaRefinedCauchy\n")
(root / "MazyaRefinedCauchy" / "Defs.lean").write_text(defs, encoding="utf-8")
print("wrote Defs.lean")

if "--statements" in sys.argv:
    opens = ch[defs_start: ch.index("namespace MazyaRefinedCauchy")]
    sol = ("module\n\npublic import MazyaRefinedCauchy\npublic import MazyaRefinedCauchy.MainA\n"
           "public import MazyaRefinedCauchy.MainB\n\n/-!\n# Proved solution\n\n"
           "The two theorems below have exactly the statements of `Challenge.lean`; Comparator checks this\n"
           "and that the proofs use only the permitted axioms. The definitions they mention come from\n"
           "`MazyaRefinedCauchy.Defs`, which repeats the definitions of `Challenge.lean`.\n-/\n\n"
           "public section\n\n" + opens + "namespace MazyaRefinedCauchy\n\n")
    a_stmt = ch[thm_a:thm_b].replace(":= by\n  sorry", ":=\n  mainA hn Γ hΓ hΓ0 ρ hρ a ha ha_symm ha_ell b hb c hc u Du hu hu_cont hDu_cont hDu hL hDir h\n    hNeu hh")
    b_stmt = ch[thm_b:end].replace(":= by\n  sorry", ":=\n  mainB hn Γ hΓ hΓ0 ρ hρ u Du hu hu_cont hDu_cont hDu hDir h hNeu hh_pos hh_mono hΛ_super\n    hΛ_convex hΛ_growth hlog")
    (root / "Solution.lean").write_text(sol + a_stmt + b_stmt + "end MazyaRefinedCauchy\n", encoding="utf-8")
    for name, stmt, new in (("MainA", ch[thm_a:thm_b], "mainA"), ("MainB", ch[thm_b:end], "mainB")):
        old_name = "refined_cauchy_superexp" if name == "MainA" else "refined_cauchy_laplace"
        title = "Theorem I(a)" if name == "MainA" else "Theorem I(b)"
        body = ("module\n\npublic import MazyaRefinedCauchy.Interfaces\n\n/-!\n# " + title +
                "\n\nAssembly of the proof from the package interfaces in `MazyaRefinedCauchy.Interfaces`.\n-/\n\n"
                "public section\n\n" + opens.replace("open Filter Topology InnerProductSpace",
                "open Filter Topology InnerProductSpace MeasureTheory") +
                "namespace MazyaRefinedCauchy\n\n" + stmt.replace("theorem " + old_name, "theorem " + new) +
                "end MazyaRefinedCauchy\n")
        (root / "MazyaRefinedCauchy" / f"{name}.lean").write_text(body, encoding="utf-8")
    print("wrote Solution.lean, MainA.lean, MainB.lean")
