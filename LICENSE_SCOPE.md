# License scope and attribution

The original Lean code and supporting verification scripts are released under
the MIT license in [LICENSE](LICENSE), with Paul Pollack named as copyright
holder. Their headers credit ChatGPT Astra for generating the formalization
and identify Paul Pollack as the responsible maintainer. These credits do not
attribute discovery of the proof to Paul Pollack.

The following third-party code retains its existing Apache-2.0 license and
copyright notices:

- `MertensUpper.lean`: Axiom Math; see
  [vendor-licenses/PrimeGapsLib-LICENSE](vendor-licenses/PrimeGapsLib-LICENSE).
- The four Lean files in `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/`:
  Arend Mellendijk; see
  [PrimeNumberTheoremAnd/LICENSE](PrimeNumberTheoremAnd/LICENSE) and
  [vendor-licenses/PrimeNumberTheoremAnd-LICENSE](vendor-licenses/PrimeNumberTheoremAnd-LICENSE).

Their exact upstream revisions and the extraction/adaptation details are
recorded in [vendor-provenance.json](vendor-provenance.json). Dependencies
obtained through Lake retain their own licenses.

The MIT grant does not apply to `USER_PROOF_HALF.tex`, `manuscript-input.txt`,
or any rendering of the manuscript. This change leaves the paper's licensing
unchanged.
