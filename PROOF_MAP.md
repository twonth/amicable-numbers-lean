# Correspondence with the manuscript

The frozen input is `manuscript-input.txt`, from attachment
8d1dc442-c142-4799-a616-78ee8072be7e. Its SHA256 is
`6324e9e9cac2f6324a6b2213c8f20fcd8c206f7388b951af5d3f039212516fa7`.
The user's separately supplied definition of L(x) is included. The TeX has not
been changed. This map distinguishes mathematical steps from implementation details;
it does not assert that every sentence of prose is itself a Lean declaration.

## Definitions and final statement

`ManuscriptArithmetic.lean` defines sigma as mathlib's divisor-sum arithmetic
function, s as the sum of proper divisors, and Amicable using positivity,
distinctness, and both equations s(n)=n' and s(n')=n. A(x) is the cardinality of
the corresponding filtered finite set up to floor(x). The partner is unrestricted.
L(x) is exp(log(x) log_3(x)/log_2(x)).

`Certificate.lean` supplies both a statement using A and a statement with its
counting predicate expanded. For every real c<1/2 it proves the bound with
coefficient c for all sufficiently large real x. This expresses the manuscript's
asymptotic assertion without an unspecified error function.

## Lemma 1: Pollack's gcd bound

`PollackTheorem.lean`, theorem `AmicablePollack.pollack`, proves the uniform
exceptional-set bound for every beta>0 and every G above the stated threshold.
The proof is assembled from the gcd-decomposition modules, squarefull estimates,
large-coprime-divisor construction, prime-factor tails, and sigma-divisibility
counts. It is a proof of the cited input, not an axiom standing for that input.

## Lemma 2: weighted technical estimate

The multiplicative weight and its relation to the small-prime part and rough
Omega are in `WeightArithmetic.lean` and `RoughParts.lean`.
`RankinFinite.lean` starts with the Rankin inequality and finite Euler products.
`MomentWeight.lean`, `AnalyticInputs.lean`, and `MomentEuler.lean` establish the
convergent moment bound for the selected parameters. `RankinParameters.lean`
proves their limiting properties. `TechnicalLemma.lean`, theorem
`AmicableTechnical.technicalLemma`, supplies the uniform bound with an explicit
error function tending to zero.

The coefficient-one Mertens upper estimate is in `MertensUpper.lean`; the zeta
and prime reciprocal bounds used in this moment argument are in `ZetaBounds.lean`.
Only the upper consequences used in the manuscript are needed, rather than full
two-sided asymptotic formulas. Infinite sums are used only with convergence proved.

## Proposition 3: structural reduction

`StructuralExceptional.lean` bounds integers with large gcd, a large squarefull
divisor, or small size. `StructuralFactorization.lean`,
`SquarefullDecomposition.lean`, and `PreparedPair.lean` construct B,a,B',a' and
prove their size, squarefreeness, unitary, and cross-coprimality properties.

`SmallProductCount.lean` implements the first elimination of p and bounds pairs
with small mm'. `StructuralLargePrime.lean` constructs D and implements the second
elimination when p>x^(4/5). `StructuralCounting.lean` counts M through the resulting
congruence and proves the double-sum estimate, using `SigmaAverage.lean`.
`StructuralPowerCount.lean` absorbs this fixed power saving.

`PreparedExceptional.lean` joins these exceptional sets. Finally,
`StructuralReduction.lean`, theorem `AmicableManuscript.structuralReduction`,
proves the complete structural input. Partner injectivity handles exceptions in
either member and interchange of the pair. The predicate StructuralReduction is
defined in `FinalReduction.lean`; it is discharged here, not left as an assumption.

## Case I

`DivisorAllocation.lean` distributes r among q+1, including repeated prime factors.
`GoodPrimeProduct.lean` and `CaseOneSelection.lean` find the product r0 and then R
of one of the two stated kinds. `ComplementaryDivisor.lean` constructs the integer
d dividing sigma(m) with d>p/R^(9/10). `CaseOneWitness.lean` joins these steps for
an actual amicable pair with the structural factorizations.

`CaseReconstruction.lean` proves the two uniqueness arguments: the linear residue
class for prime R<p, and the small determinant followed by equality of reduced
fractions for the second kind of R. `CaseOneCount.lean` and `CaseOneRange.lean`
count p,d,R for each m and dyadic range. `DyadicRanges.lean` supplies the finite
cover and logarithmic bound on the number of ranges.

`CaseOneCountingSharp.lean`, theorem `AmicableCases.caseOneCountingSharp`, proves
the manuscript's saving x^(1-epsilon^2/100+o(1)). The main assembly only needs a
power saving, and uses the weaker bound x^(1-epsilon^2/400) from
`CaseOneCounting.lean`. The sharper bound is therefore checked separately too.

## Case II

`DivisorSelection.lean` chooses R in the prescribed interval. Exceptions to the
technical lemma are counted through multiples of b by
`TechnicalExceptionalCount.lean` and `LogarithmicFactors.lean`. Their reciprocal
sum is estimated by a finite dyadic decomposition, giving the same logarithmic
factor as the partial summation in the prose.

`CommonDivisor.lean` constructs r and proves the weighted logarithmic inequality.
`DivisorPartition.lean` and `IndexedPartition.lean` construct the V_i and d_i.
`CaseTwoSelectedDivisor.lean` and `CaseTwoSelection.lean` implement the averaging
argument, including its strict positive margin, and exponentiate the selected
inequality. `CaseTwoWitness.lean` joins these operations.
`CaseTwoPairWitness.lean` starts with the actual pair and yields either an
exceptional b or all the required counting data.

The uniqueness of R for fixed m,V is the actual sigma reconstruction from
`CaseReconstruction.lean`, with its determinant estimate in `SigmaUniform.lean`.
The bound for V uses `FactorizationCounting.lean`, `SigmaCounting.lean`,
`SigmaCountBound.lean`, and `SharpFactorCost.lean`. It is made uniform and combined
with the selected inequality in `CaseTwoUniform.lean` and `CaseTwoBudget.lean`.
`CaseTwoCounting.lean` sums over m and divisors d of sigma(m), giving
x^(1-4 epsilon^3+o(1)).

## Arithmetic-progression input

`ProgressionSieve.lean` and `SieveAsymptotics.lean` prove an arithmetic-progression
Brun--Titchmarsh bound with an absolute constant. `PrimeReciprocals.lean`, theorem
`AmicablePrimeReciprocals.primeReciprocalUniform`, proves the required uniform
reciprocal estimate. The interval Brun--Titchmarsh theorem is not substituted
for this progression estimate. The optimal constant 2 is not required or claimed.

Four unchanged Selberg-sieve modules from PrimeNumberTheoremAnd are vendored;
their revision and licenses, and the provenance of MertensUpper, are recorded in
`vendor-provenance.json` and `vendor-licenses/`. Their proofs and all dependencies
are checked in the same Lean environment.

## Formal bookkeeping and intermediate estimates

- Every asymptotic assertion used in a sum has explicit uniform quantifiers.
  Dependence on fixed epsilon and structural constants is permitted, as in the paper.
- Factorization counting bounds even ordered lists of factors greater than one by
  Omega(d)^Omega(d); this also bounds the unordered multiplicative partitions used
  in the text, with no missing sum over their length.
- The main reciprocal-count bound uses the sufficient totient loss 2^Omega(d).
  This still gives the manuscript's exp(Omega(d) log_2(x)+o(log x)) estimate.
  `FineTotientBound.lean` separately proves the sharper displayed loss
  exp(2 Omega(d)/y), including the version for a product of totients of factors.
- The Case II remainder from V0 is absorbed by an arbitrarily small multiple of
  log x. The stronger estimate stated in the prose also follows from the checked
  sigma bound; the averaging only needs this vanishing relative error.
- The structural double sum is proved quantitatively before being relaxed to
  x^0.95 for the final exceptional-set bookkeeping. No exponent near 1/2 is
  obtained from this relaxation; its sole role is to remain a power saving.
- No formal statement assumes that the chosen divisors or representations are
  unique. Finite-image and fibre counts explicitly allow overcounting.

## Closing the proof

`RegularAlternatives.lean` connects actual structural pairs to the two cases.
`RegularCounting.lean` combines them and their technical exceptions.
`FinalReduction.lean` gives the implication from the structural proposition to
MainBound; `StructuralReduction.lean` supplies its hypothesis and proves
`AmicableManuscript.amicableUpperBound`. `Certificate.lean` exposes this result
and prints its transitive axiom report. The reported axioms are only propext,
Classical.choice, and Quot.sound.

Thus the final certificate is unconditional within the usual Lean foundations.
The connection to the prose is documented above rather than hidden behind assumed
analytic lemmas or abstract counting predicates.

