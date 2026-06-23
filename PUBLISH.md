# Publishing to the public repository

The public showcase repo
[**lean-wqo-continuous-functions**](https://github.com/yannpequignot/lean-wqo-continuous-functions)
is a **curated mirror** of this development repository. It is *not* a plain `git push`: this
repo tracks internal material (the memoir `.tex` sources and PDF, `CLAUDE.md`, internal notes)
and two stub chapters that must **not** appear publicly.

## What is excluded

Curation is driven by [`.publishignore`](.publishignore):

| Excluded | Why |
|---|---|
| `*.tex`, `*.pdf` | unpublished memoir sources |
| `CLAUDE.md`, `ARISTOTLE_SUMMARY.md`, `.claude/` | internal working notes |
| `WqoContinuousFunctions/PrelimMemo/blackboard.lean` | scratch file |
| `WqoContinuousFunctions/DoubleSuccessor/` | stub chapter (near-all-`sorry`, not in the default build) |
| `WqoContinuousFunctions/PreciseStructure/` | stub chapter (near-all-`sorry`, not in the default build) |
| `.git/`, `.lake/`, `build/`, `.vscode/`, `.venv/` | VCS / build artefacts |

Everything else is published: the three libraries `ZeroDimensionalSpaces`, `BQO`, and
`WqoContinuousFunctions` (minus the stubs), `lakefile.toml`, `lake-manifest.json`,
`lean-toolchain`, `README.md`, `STRUCTURE.md`, `LICENSE`.

> The two stub chapters are not imported anywhere in the published build and are absent from
> the `lakefile.toml` globs, so the public build is unaffected by their removal. (The lakefile
> retains a comment mentioning them; harmless, since they simply aren't present in the mirror.)

## How to publish

```bash
./publish.sh          # dry run: refresh a clone of the public repo, mirror the
                      # curated tree into it, and print the diff that WOULD be published
./publish.sh --push   # same, then commit and push to showcase/main
```

The script clones (or refreshes) the public repo at `../lean-wqo-continuous-functions`
(override with `PUBLISH_CLONE_DIR`), resets it to `origin/main`, then mirrors the curated
working tree with `rsync -a --delete --delete-excluded` (the public repo's `.git` is protected
from deletion). On `--push` it commits (message via `PUBLISH_MSG`) and pushes.

**Recommended before `--push`:** build the staged tree to confirm the public mirror compiles:

```bash
(cd ../lean-wqo-continuous-functions && lake build ZeroDimensionalSpaces BQO WqoContinuousFunctions)
```

## Notes

* This is distinct from [`.rsyncignore`](.rsyncignore), which is used in the *opposite*
  direction — to **import** Aristotle exports into this repo without clobbering curated files.
* The public `README.md` is the same file as this repo's `README.md`; keep it public-facing.
