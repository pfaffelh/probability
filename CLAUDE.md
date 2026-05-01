# CLAUDE.md

Context for Claude Code working in this repository.

## What this repo is

A [Verso Blueprint](https://github.com/leanprover/verso-blueprint) project
describing Lean 4 / Mathlib results in probability theory. The Blueprint pairs
informal mathematical exposition with links to formal Lean declarations and
renders to a browsable HTML site (graph + per-statement progress summary).

Scaffolded from `leanprover/verso-blueprint` at tag `v4.29.0`.

## Toolchain

- Lean: `leanprover/lean4:v4.29.0` (pinned in `lean-toolchain`)
- Lake deps (`lakefile.lean`):
  - `verso` @ `v4.29.0`
  - `verso-blueprint` @ `main`
  - `mathlib4` @ `v4.29.0`

`lake update` pulls a large dep tree (Mathlib). Don't run it unless asked.

## Layout

```
Probability.lean              library root (just imports Blueprint)
Probability/
  Blueprint.lean              top-level Blueprint document
  Chapters/
    Introduction.lean         starter chapter
ProbabilityMain.lean          blueprint-gen executable entry point
lakefile.lean                 package + lib + lean_exe blueprint-gen
scripts/ci-pages.sh           local build-and-render check
.github/workflows/            GitHub Pages deployment
```

## Common commands

```bash
lake update                          # one-time, fetches verso/blueprint/mathlib
lake build                           # compile the Lean library
lake exe blueprint-gen --output _out/site   # render HTML only
./scripts/ci-pages.sh                # full local build + render check
```

Rendered site lands in `_out/site/html-multi/` (gitignored).

## Adding a chapter

1. Create `Probability/Chapters/Foo.lean` with the same imports as
   `Probability/Chapters/Introduction.lean`.
2. In `Probability/Blueprint.lean`, both `import Probability.Chapters.Foo`
   and add `{include 0 Probability.Chapters.Foo}` in document order.

Inside a chapter, the Blueprint vocabulary used here is:

- `:::group "label"` — group header
- `:::definition "label" (parent := "...")` — informal definition block
- `:::theorem "label" (parent := "...") (lean := "Mathlib.Decl.Name") (tags := "...") (effort := "small|medium|large") (priority := "...")` — link to an existing Mathlib lemma
- `:::proof "label"` — informal proof sketch
- ` ```lean "label" ` blocks attach a local Lean snippet to a Blueprint label
- `{uses "label"}[]` cross-references another Blueprint node

The `(lean := "Foo.bar")` attribute links a theorem entry to an existing
Mathlib declaration; alternatively, use a fenced ` ```lean "label" ` block to
state the proof inline.

## GitHub Pages

Workflows in `.github/workflows/`:
- `pages.yml` — triggers on PR / push-to-main / manual
- `blueprint-pages.yml` — reusable workflow that runs `scripts/ci-pages.sh`
  and publishes `_out/site/html-multi`

Repo Pages source must be set to **GitHub Actions** in Settings → Pages once.

## Repo

- Remote: https://github.com/pfaffelh/probability (public)
- Default branch: `main`
