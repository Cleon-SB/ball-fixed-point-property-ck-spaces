# Verification record

## Scope

The manuscript checked by the original verification was `csb-BFPP-JFA.tex`, SHA-256
`d4854ad370dc16ab81ee2c5c35f2801e9d2c3c82cb685d860133e3bf9725cdaf`.
Its mathematical results are represented by 73 source modules, imported by
`BFPP.lean`. The correspondence and proof adaptations are in `COVERAGE.md`.

### Manuscript revision of 2026-09-14

The unused Appendix A and its explanatory references were removed. The revised
manuscript hash is
`2c11258a51e3059546f7aeba10aeb54935789b5dd6ab02513b5aa4fb0809ca26`.
All mathematical statements and proofs in the main text are unchanged. The
former appendix modules remain supplementary material and are not in the
import closures of `MainTransfinite` or `Characterization`. No Lean source,
dependency configuration, or verification log was changed by this editorial
revision. Their hashes were checked against the original manifest. This is
an update of the correspondence documentation, not a new Lean verification run.

### Subsequent author and Boolean-background revision of 2026-09-14

The author's manuscript has SHA-256
`36bd40ea4436df9284d07b76fca70d977eaacc63b9bdd2464324bb86c9007748`.
After integrating Boolean terminology, three motivating sentences, the
Koppelberg reference, and a duplicate-label correction, the manuscript hash is
`a56b3864237bedd10b40791938ce02e8e9b53abed842b810ca780affc1bf473d`.
The 34 existing statement/proof blocks were compared. Between the earlier
manuscript and the author's version, 33 are identical modulo whitespace;
the remaining block is the ordinal-encoding proof, whose changes only
reformat displays and leave the mathematical formulas unchanged. Between
the author's version and this edit, only the duplicated label changes inside
these blocks. The added background is consistent with the Boolean and order
notions already used in the formalization. All 81 source, configuration,
script, and evidence files outside the three documentation files retain
their previous hashes. No Lean recompilation was needed or performed for
this editorial revision; the original kernel-verification record is retained.

### Final submission filename and availability paragraph (2026-09-14)

The current manuscript is `csb-BFPPCKsps-FV.tex` (928 lines), SHA-256
`feefe0f1af582753d5b22ada4baa01e87b1c1533706f47cd02d4c3c1b8ddc5ca`.
The author requested this final filename. The source bytes match the author's
saved `csb-BFPP-JFA.tex`; only the distributed filename changes.

Compared with the 918-line version identified by hash
`a56b3864237bedd10b40791938ce02e8e9b53abed842b810ca780affc1bf473d`,
the source adds a Lean formalization paragraph ("is available at") and an extra
blank line. All 38 definition, theorem, proposition, lemma, corollary, remark,
and proof environments were compared and are identical modulo whitespace.
Removing the new paragraph makes the complete sources identical modulo
whitespace. The matching PDF was recompiled: 21 pages, with no warnings or
undefined references in the final log.

All 81 manifest-listed files outside README.md, COVERAGE.md, and VALIDATION.md
retain their previous hashes, including all 75 Lean source files, both scripts,
the dependency configuration, and the verification log. SOURCE-SHA256.txt and
the downloadable archive were regenerated to record the documentation changes.
No new Lean compilation or new semantic audit was performed for this editorial
synchronization. The original verification record below remains the evidence
for the unchanged formalization. Repository access is a separate publication step.

## Checked environment

- Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Platform: `x86_64-w64-windows-gnu`, release build.
- mathlib Git HEAD: `85e3a25e006c35636f0e53b0e9296caca2685bc0`, matching `lakefile.toml`.
- The only declared library dependency is mathlib; its own transitive dependencies
  are the standard cached packages. No external project theorem is imported.

## Kernel and axiom checks

Every mathematical module was compiled with the pinned Lean executable, using
the existing compiled mathlib checkout read-only. The aggregate import and
`Audit.lean` were compiled as well. `build-final.log` consolidates the full
rebuild and the final checks of the supporting modules added during review.
The final log contains all 75 distinct Lean source files. No mathematical
source was newer than its compiled object, and no compiled module was missing.
Verification completed on 2026-09-14 UTC.

The audit passed for **988 declarations** in namespace `BFPP`, including
generated declarations. Its allowlist contains exactly:

```text
propext
Classical.choice
Quot.sound
```

The audit rejects any other axiom, including `sorryAx`. A separate source scan
found no `sorry`, `admit`, custom `axiom`, or `unsafe` declarations. All 73
mathematical modules are present in both the aggregate import and build list.
Style/deprecation warnings in the log are not proof errors.

## Statement checks

An independent read-only review compared the manuscript with the exported
formal statements. It confirmed the exact main hypotheses and conclusions,
the actual construction of A/J/P, the regular uncountable initial ordinal,
the TCP prefix and limit rules, both BFPP implications, the synthesis lemma,
and the appendix. Supporting claims identified during review were subsequently
added and checked: arbitrary closed balls, discrete affine propagation, the
convex-integral identity and combined mass bound, and bundled normalization.

## Lake configuration

In an isolated workspace, the unchanged Lake configuration passed
`lake --no-cache check-build`. An offline `lake env lean` smoke check imported
the characterization and printed its standard axiom dependencies. Dependency
paths were redirected to existing caches only in that isolated probe.

A fresh online `lake update` / conventional dependency-rebuilding `lake build`
was not run against the external read-only caches. The complete verification
above uses `scripts/build-local.ps1` and direct Lean compilation. The project
also includes the pinned conventional Lake configuration for independent builds.

## Integrity

`SOURCE-SHA256.txt` lists hashes of the delivered source, configuration, scripts,
documentation, and verification log. Compiled caches are excluded from the
source archive. The original manuscript was not modified by this formalization.
