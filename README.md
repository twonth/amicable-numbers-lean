# Lean certificate for the amicable-number manuscript

The entry point is **Certificate.lean**. Its theorem
`AmicableCertificate.amicable_count_upper_bound` proves:

> For every real c < 1/2, there is x0 such that, for every real x >= x0,
> A(x) <= x exp(-c log(x) log_3(x) / log_2(x)).

This is the quantified form of the manuscript's exponent-1/2 asymptotic bound.
A(x) counts positive integers in distinct amicable pairs; their partners need not
be <= x. `explicit_count_upper_bound` expands that predicate in the statement.
The definitions use the actual sum of proper divisors, not an abstract replacement.

The complete theorem and every local dependency have passed a fresh Lean rebuild.
The results are recorded in `verification/`; see Certificate.log,
StructuralReduction.log, and proof-hashes.json.
An additional fresh kernel replay of Certificate and all its imported declarations
also passed; see kernel-replay.log and status.json. The replayed development
artifacts agree with the freshly rebuilt artifacts for the compared local modules.
The reported theorem axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
No mathematical result is assumed through a custom axiom, `sorry`, or `native_decide`.

## Relation to the manuscript

The current paper is [USER_PROOF_HALF.tex](USER_PROOF_HALF.tex), updated on
September 29, 2026. The certificate concerns the proof of the main theorem;
the introductory heuristics are outside its scope.

The original formalization source is the unchanged `manuscript-input.txt`, copied from attachment
8d1dc442-c142-4799-a616-78ee8072be7e. Its SHA256 matches the attachment:
`6324e9e9cac2f6324a6b2213c8f20fcd8c206f7388b951af5d3f039212516fa7`.
The separately supplied definition L(x)=exp(log(x) log_3(x)/log_2(x)) is included.

This formalization follows the manuscript's argument: the weighted Rankin lemma,
the squarefree structural reduction and its two eliminations, the two kinds of R
in Case I, and the common-divisor/weighted-selection/reconstruction count in Case II.
`PROOF_MAP.md` identifies the corresponding checked declarations and explains the
finite and asymptotic bookkeeping used to express the prose precisely.
`AUDIT.md` records the mathematical review and points worth making explicit in print.
The original formalization input is preserved separately from the current paper.

## Main checked results

| Manuscript component | Lean entry point |
|---|---|
| Pollack's gcd lemma | PollackTheorem.lean: `AmicablePollack.pollack` |
| Weighted technical lemma | TechnicalLemma.lean: `AmicableTechnical.technicalLemma` |
| Proposition 3 | StructuralReduction.lean: `AmicableManuscript.structuralReduction` |
| Case I construction | CaseOneWitness.lean: `AmicableCases.caseOneWitness` |
| Case I count, including the stated power saving | CaseOneCountingSharp.lean: `AmicableCases.caseOneCountingSharp` |
| Case II construction | CaseTwoPairWitness.lean: `AmicableCases.caseTwoPairWitness` |
| Case II count | CaseTwoCounting.lean: `AmicableCases.caseTwoCounting` |
| Both cases and their exceptions | RegularCounting.lean: `AmicableCases.regularCounting` |
| Final theorem | Certificate.lean: `AmicableCertificate.amicable_count_upper_bound` |

The intermediate predicates `CaseOneData`, `CaseTwoData`, `RegularPair`, and
`StructuralReduction` are not unproved assumptions of the final theorem. Their
witnesses or theorems are supplied by the later modules. `FinalReduction.lean`
is an intermediate implication; `StructuralReduction.lean` discharges its premise.

## Outside results and trust

The arithmetic-progression sieve bound and its reciprocal-prime consequence are
proved in ProgressionSieve.lean, SieveAsymptotics.lean, and PrimeReciprocals.lean.
They use four unchanged Selberg-sieve files from Alex Kontorovich's
PrimeNumberTheoremAnd repository. The interval Brun--Titchmarsh file is not used
as if it were an arithmetic-progression theorem.

MertensUpper.lean is an attributed extraction from AxiomMath/PrimeGapsLib, rechecked
against the pinned mathlib. It supplies the coefficient-one upper estimate actually
used in the manuscript. Zeta bounds, the uniform divisor bound, squarefull estimates,
and Pollack's theorem are proved in the accompanying files.

The exact repository revisions and retained licenses are in `vendor-provenance.json`
and `vendor-licenses/`. All other dependencies are the pinned mathlib and its normal
manifest dependencies. A proof certificate verifies the formal statements; the
manuscript-to-statement correspondence is separately explained in PROOF_MAP.md.

## Rechecking

Install Lean through elan, then run from the repository root:

```sh
lake update
lake exe cache get
lake build
lake env lean Certificate.lean
```

The final command prints the transitive axiom reports. They should contain only
`propext`, `Classical.choice`, and `Quot.sound`. For an additional replay of all
imported declarations in a fresh Lean kernel environment:

```sh
lake env leanchecker --fresh --verbose Certificate
```

This is Lean's own kernel, not a second independently implemented proof checker.
The source configuration is pinned to:

- Lean 4.35.0-rc3, source commit 470d5ce1400764999581fd26d5d72b00d990b0f4.
- Mathlib commit 3f6737de4761ec7bf368491fe9faccc991ebd6ca.

The `verification/` directory preserves the successful original rebuild and
kernel-replay records. Its source hashes use repository-relative paths.
The portable Lake configuration has been checked separately; the original
verification was performed using the same pinned compiler and dependencies.

Upstream licenses are retained in `vendor-licenses/`; no new blanket license is
assigned to the manuscript or original project files by this upload.
