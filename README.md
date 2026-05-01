# Probability

A [Verso Blueprint](https://github.com/leanprover/verso-blueprint) describing
results in probability theory formalized in Lean 4 and Mathlib.

## Layout

```text
.
├── Probability.lean              # library root
├── Probability/
│   ├── Blueprint.lean            # top-level Blueprint document
│   └── Chapters/
│       └── Introduction.lean     # starter chapter
├── ProbabilityMain.lean          # `blueprint-gen` entry point
├── lakefile.lean                 # depends on verso, verso-blueprint, mathlib
├── lean-toolchain                # leanprover/lean4:v4.29.0
├── scripts/
│   └── ci-pages.sh               # local build-and-render check
└── .github/workflows/            # GitHub Pages workflows
```

## Build

After cloning, fetch dependencies once:

```bash
lake update
```

This pulls Verso, Verso Blueprint, and Mathlib (a large download on first run).

Then build the Blueprint site locally:

```bash
./scripts/ci-pages.sh
```

That runs `lake build` followed by `lake exe blueprint-gen --output _out/site`.
The rendered HTML lands in `_out/site/html-multi/`.

To regenerate just the site without rebuilding:

```bash
lake exe blueprint-gen --output _out/site
```

## Adding chapters

1. Create a new file under `Probability/Chapters/`, e.g. `LawOfLargeNumbers.lean`.
2. Use the same import preamble as `Introduction.lean`.
3. Register the chapter in `Probability/Blueprint.lean` with both an `import`
   and an `{include 0 ...}` line.

Each `:::theorem` block can link to an existing Mathlib declaration via
`(lean := "MeasureTheory.someLemma")`, or attach a local Lean block:

````
```lean "label_id"
theorem foo : ... := by ...
```
````

## GitHub Pages

The included workflows build on pull requests and deploy `main` to GitHub
Pages. Enable Pages with "GitHub Actions" as the source in your repository
settings.

## References

- [Verso Blueprint](https://github.com/leanprover/verso-blueprint)
- [Verso](https://github.com/leanprover/verso)
- [Mathlib](https://github.com/leanprover-community/mathlib4)
