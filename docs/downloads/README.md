# Transfinite propagation and the BFPP of C(K)

Lean formalization of the mathematical results in `csb-BFPPCKsps-FV.tex`, using
mathlib as its only library dependency, in 73 mathematical modules.
See [COVERAGE.md](COVERAGE.md) for the
paper-to-theorem correspondence and differences in proof organization.

Current manuscript: `csb-BFPPCKsps-FV.tex` (928 lines), synchronized on
2026-09-14. Source SHA-256:
`feefe0f1af582753d5b22ada4baa01e87b1c1533706f47cd02d4c3c1b8ddc5ca`.
The corresponding PDF and LaTeX source are in the repository's `docs/downloads`
directory. The website's paper page links to this version. The latest revision
adds the author's Lean formalization paragraph; the mathematical statements,
proofs, and all Lean source files are unchanged. See `VALIDATION.md` for the
editorial comparison and the scope of the original verification.

The principal results are:

- `BFPP.hasBFPP_iff_extremallyDisconnected`: for compact Hausdorff K, the real
  space C(K) has the ball fixed point property exactly when K is extremally
  disconnected. Both implications are proved.
- `BFPP.exists_transfinite_realization`: constructs the uncountable regular
  initial ordinal, closed bounded convex domain, nonexpansive A/J/P, precise
  successor/limit propagation rules, and fixed-point-free whole-ball map.
- `BFPP.positiveSynthesis_measure_representation`: positive synthesis represented
  by finite regular measures, including initial-segment and total-mass identities.
- `BFPP.exists_complex_fixedPointFree_of_not_ED`: extension to the complex unit ball.

The project also retains `BFPP.exists_terminal_pointwise_supremum_of_not_ED`
and its normalization as supplementary results. Their former manuscript
appendix was removed on 2026-09-14 because no proof in the main text uses it.
These modules are independent of the main realization and characterization.

There are no `sorry` proofs, paper-specific axioms, or assumed realization maps
in these existence results. The audit permits only Lean's standard logical
axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Dependency and build

Lean is pinned to `v4.34.0-rc2`, and mathlib to
`85e3a25e006c35636f0e53b0e9296caca2685bc0`.
From this directory, with that toolchain and network access:

```text
lake update
lake exe cache get
lake build
```

Both `BFPP` and `Audit` are default targets. Import `BFPP` to use the results.
The final environment, audit evidence, and build limitations are recorded in
[VALIDATION.md](VALIDATION.md).
mathlib's own transitive dependencies are installed by Lake. No theorem from
the host user's other projects is imported.

## Offline verification used during development

The checker invokes the pinned Lean executable directly, reusing an existing
compiled checkout of mathlib read-only. It builds each local source in dependency
order, then checks `BFPP.lean` and `Audit.lean`:

```powershell
./scripts/build-local.ps1 -MathlibRoot <mathlib-path> -LeanExe <lean-path>
```

For one module whose dependencies have already been built:

```powershell
./scripts/check-local.ps1 -File BFPP/MainTransfinite.lean -MathlibRoot <mathlib-path> -LeanExe <lean-path>
```

The scripts' defaults match the development machine. Output stays inside this
project's `.lake/build/lib/lean`; the existing mathlib checkout is not modified.
`build-final.log` records the project-wide verification run.

The unchanged Lake configuration and the cached dependency environment were
also validated in an isolated probe with `lake --no-cache check-build` and
`lake env lean`, importing the characterization and inspecting its axioms.
A fresh network-based `lake update` / ordinary `lake build` was not exercised;
the complete project verification uses the direct Lean build described above.
