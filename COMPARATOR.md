# Comparator verification of the main theorem

The official [Lean Comparator](https://github.com/leanprover/comparator) passed
on the main theorem. The latest run completed at **2026-09-30 00:55:46 UTC** (September
29 in Georgia), with exit code 0 and the final messages:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The machine-readable report is [verification/comparator-status.json](verification/comparator-status.json).
The full output is [verification/comparator.log](verification/comparator.log),
and [verification/comparator-source-hashes.json](verification/comparator-source-hashes.json)
identifies the checked inputs. All copied source/configuration files were checked
against their original hashes after the run.

## What was checked

- [Challenge.lean](Challenge.lean) imports only Mathlib. It states the quantified
  form of the manuscript's Theorem 1 (`thm:main`), with the count, positivity,
  distinctness, and both proper-divisor-sum equations written out explicitly.
  The amicable partner is not required to lie below x.
- [Solution.lean](Solution.lean) has the same statement and supplies its proof
  using `AmicableCertificate.explicit_count_upper_bound`, which follows from
  `AmicableCertificate.amicable_count_upper_bound` in Certificate.lean.
- [comparator.json](comparator.json) selects `AmicableComparator.main_theorem`
  and permits only `propext`, `Classical.choice`, and `Quot.sound`.

Comparator checked the statement and the definitions on which it depends,
checked the proof's permitted axioms, and replayed the exported proof and its
dependencies in Lean's kernel. The solution does not import the challenge.
The intentional `sorry` in Challenge.lean is the question to be answered;
`sorryAx` is not permitted in the checked solution.

The initial run used a fresh Linux project directory and the official pinned
Mathlib cache; the project proof modules were first compiled inside Comparator's
sandbox. Its records are preserved in `verification/comparator-initial/`.
After adding copyright headers without changing proof bodies, the check was
rerun in that project, retaining dependency caches. Both runs used real Landrun
sandboxing and systemd's `RestrictAddressFamilies=~AF_UNIX` protection.
No independently implemented external kernel was used.

The match between the written theorem and the challenge was reviewed by the
agent; no separate human review is recorded here. The paper's introductory
heuristics and historical assertions are outside this check's scope.

## Reproduction

Use a fresh checkout and the repository's pinned Lean 4.35.0-rc3 toolchain, on
Linux as a non-root user with a working systemd user manager. Build the following
unmodified upstream tool revisions:

| Tool | Revision |
|---|---|
| Comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` |
| lean4export | `66f1fb4bc256072069767fce52d39480e4524869` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

In the Comparator checkout, `lake build lean4export comparator` builds the
checker and its pinned exporter. In the Landrun checkout, `go build -o landrun
./cmd/landrun` builds the sandbox tool. Then, from this proof repository:

```sh
lake exe cache get
export COMPARATOR_BIN=/absolute/path/to/comparator/.lake/build/bin/comparator
export COMPARATOR_LEAN4EXPORT=/absolute/path/to/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
export COMPARATOR_LANDRUN=/absolute/path/to/landrun/landrun
bash verify-comparator.sh
```

Do not prebuild the solution on the fresh checkout: the script lets Comparator
perform that step within its sandbox. Fetching the trusted official Mathlib
cache beforehand is supported by Comparator's documented workflow.

The accompanying [formalization.yaml](formalization.yaml) records the scope,
attribution, assumptions, review status, and manuscript-to-Lean map.
[LICENSE_SCOPE.md](LICENSE_SCOPE.md) explains the MIT grant for original code,
the retained third-party licenses, and the exclusion of the manuscript.
