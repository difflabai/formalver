# The local Kani record

36 of the 89 Kani harnesses and 16 of the 31 mutants peaked above 13 GB
when measured (`../RESULTS.md`; `h_wedge` reached 39.0 GB). GitHub's hosted
runner for a public repository has 16 GB, and on swap those harnesses
failed or crawled (CI runs 43469880167 and 43488691444; strategy.md
section 14). So they run on a local machine with enough memory, and this
directory records the run. Without the `KANI_RUNNER` repository variable,
CI checks the record instead of running them again.

The split is in `.github/workflows/shared-pool.yml`:

| Hosted runner (every Kani run) | Local record (or `KANI_RUNNER`) |
|---|---|
| `kani`: 53 harnesses in 8 groups, peaks of 13 GB or less | `kani-large`: 36 harnesses in 21 groups |
| `kani-mutants`: 15 mutants | `kani-mutants-large`: 16 mutants |

## Files

| File | Written by | Contents |
|---|---|---|
| `provenance.txt` | `record.py` | The run's provenance as `key<TAB>value` lines: `commit` (the commit run), `kani_tree` (its `projects/shared-pool/kani` tree), one `input<TAB>name<TAB>value` line per Kani input, `fingerprint`, `digest` (sha256 of `jobs.tsv` then `covers.tsv`), `kani`, `cbmc`, `rustc`, `host`, `started`, `finished`, `parallel` (lanes and memory budget), `kani_max_gb`, `runner`, `jobs` (counts). |
| `jobs.tsv` | `record.py` | One row per job: `kind` (harness or mutant), `name` (a mutant's full patch name), `result` (`ok`, `ok-FAILED` for `h_canary`; a mutant's expect/plain/kani, such as `killed/killed/killed`), `seconds` (`run.sh`'s time for a harness; the whole job for a mutant), `job_seconds`, `cbmc_peak_gb` (CBMC's largest resident memory, sampled every 3 s), `tree_peak_gb` (the whole `run.sh` process tree), `limit_s` (the job's `KANI_TIMEOUT`, its matrix timeout), `covers` (a harness's "N of M"), `kani_harnesses` (the harnesses a mutant ran), `started_utc`. Harnesses come first, in `run.sh list` order, then mutants by name. |
| `covers.tsv` | `record.py` | The recorded harnesses' cover results: `family`, `cover`, `status` (`run.sh`'s `covers.tsv`, run with `KANI_DEFER_COVERS=1`) plus the `harness`. The `covers` job checks them with the hosted groups' covers. |
| `run-local.py` | (source) | Runs the jobs on this machine and, with `--record`, records them. |
| `record.py` | (source) | Checks a finished run and writes the three files above, or prints the record's Markdown (`table`). |

`kani/RESULTS.md` holds the record's tables between
`<!-- kani-local-record: begin ... -->` and `<!-- kani-local-record: end -->`.
`record.py` rewrites that block, and the CI check fails if the block is not
`record.py table`.

## The fingerprint

A Kani verdict depends on these inputs, and the record is valid only while
they are unchanged:

- `projects/shared-pool/kani/src`, `kani/Cargo.toml`, `kani/Cargo.lock`, `kani/mutants`, `kani/run.sh` and `kani/.gitignore`
- `projects/shared-pool/source-mirror`: the gitlink, which is the pinned core's commit
- `projects/shared-pool/conformance/traces/core.txt`: the traces a mutant's plain mode replays
- `tools/versions.env`: `KANI` and `CBMC` (the file's other pins are for other layers' tools)

Each path's value is its git object id at the commit (`git rev-parse
REV:path`): a tree id for a directory, a blob id for a file, a commit id
for the gitlink. The two versions are their values. The fingerprint is the
sha256 of the `name<TAB>value\n` lines in that order. Git objects are all
it reads, so CI computes it in a shallow checkout without the submodule:

    tools/scripts/check-kani-record.py fingerprint [REV]

These do not change the fingerprint: the Markdown, this directory, the
workflow, and the rest of the repository. The
workflow's matrices are checked separately (see CI below).

## Commands

    # Run the 36 harnesses and 16 mutants at HEAD, then record them
    # (about 4 hours on a 10-core, 64 GB Mac; two jobs at a time, their
    # measured peaks summing to at most 50 GB):
    projects/shared-pool/kani/local/run-local.py --record
    git add projects/shared-pool/kani/local projects/shared-pool/kani/RESULTS.md

    # The jobs, without running them:
    projects/shared-pool/kani/local/run-local.py --dry-run

    # Record a run directory that has already finished:
    projects/shared-pool/kani/local/record.py projects/shared-pool/kani/target/local-run/run-<time>

    # The record's Markdown (RESULTS.md's block):
    projects/shared-pool/kani/local/record.py table

    # What CI runs:
    tools/scripts/check-kani-record.py
    tools/scripts/test-check-kani-record.sh

`run-local.py` needs Kani and CBMC at `tools/versions.env`'s versions
(`cargo install --locked kani-verifier --version <KANI>; cargo kani setup`)
and the submodule (`git submodule update --init
projects/shared-pool/source-mirror`). It runs `kani/run.sh` unchanged in a
`git archive` copy of the commit's inputs, one copy per lane, with each job's
matrix timeout as `KANI_TIMEOUT`, `KANI_DEFER_COVERS=1`, and `KEEP_LOGS` set to the job's log directory.
It writes to `kani/target/local-run/` (git-ignored). If it is stopped, its
jobs are stopped too, and nothing is recorded.

`record.py` refuses a run, leaving the record and RESULTS.md untouched,
when any of these holds:

- the run is incomplete (no `ALL DONE` in `progress.log`, or a job has no result)
- a job exited non-zero
- a harness is not `ok` (`h_canary`: `ok-FAILED`)
- a mutant is not as its patch expects (`killed/killed/killed`, or `survive/survived/survived` for `# must-survive`)
- the run's commit, Kani tree, core pin or Kani/CBMC versions do not match
- the run's commit has other Kani inputs than HEAD
- the new record would fail `check-kani-record.py`

To re-record (for example v1.1.0, or after any change to an input), run the
first command again at the new commit and commit the result.

## CI

The `kani-record` job runs on every workflow run. It runs the self-test,
then `check-kani-record.py`, which fails when:

- The record's fingerprint is not HEAD's. The message names the changed
  inputs and says "re-run the local Kani record:" with the command above.
- The fingerprint is not the hash of its input lines, or `jobs.tsv` or
  `covers.tsv` does not match the digest, as when they are edited by hand.
- A recorded harness is not `ok`, or a recorded mutant is not as its patch
  expects.
- The `kani` groups and the recorded harnesses do not cover `run.sh list`
  exactly once each, or the `kani-large` groups are not the recorded
  harnesses.
- The same holds for `mutants/*.patch`: the `kani-mutants` entries plus the
  recorded mutants must cover them exactly once, and the
  `kani-mutants-large` entries must be the recorded mutants.
- A `kani` or `kani-mutants` entry peaked above 13 GB.
- RESULTS.md's block is not `record.py table`.

The `covers` job counts the recorded harnesses with the groups' harnesses
(89 in all) and checks the recorded covers with the groups' covers.

When `KANI_RUNNER` names a runner with enough memory (49 GB, 1.25 times
`h_wedge`'s peak) and the run is not routed to `ubuntu-latest`, the pin
job's `large` output is true. Then `kani-large` and `kani-mutants-large`
run there as before, a stale record is only a warning, and `covers` uses
the groups' covers alone.

## Notes on the recorded run

- `KANI_MAX_GB` is `run.sh`'s default, 40 GB, as in the measurements in
  `../RESULTS.md`. `h_wedge` peaked at 39.0 GB there, so a run where it
  needs 1 GB more stops it (OUT-OF-MEMORY, not ok) and is not recorded.
- Mutants' plain mode uses the host's default Rust toolchain
  (`provenance.txt`'s `rustc`), not `tools/versions.env`'s
  `RUST_TOOLCHAIN`. Kani pins its own toolchain. CI's `mutants` job
  re-checks plain mode for every mutant with the pinned toolchain on every
  run.
