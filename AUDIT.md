# Audit of the exponent-1/2 manuscript

Source: `manuscript-input.txt`, from attachment `8d1dc442-c142-4799-a616-78ee8072be7e`.
The full quantified exponent-1/2 theorem has now passed Lean checking. This document
records the mathematical audit; `PROOF_MAP.md` explains its correspondence with the
formalization, and `README.md` gives the certificate and rechecking instructions.

## Conclusion and qualifications

The weighted estimate, structural reduction, and two counting arguments fit together
with the claimed constant 1/2. The final formal theorem is
`AmicableCertificate.amicable_count_upper_bound`. The required outside estimates have
also been proved or imported through checked proofs, rather than assumed as axioms.

The following points are handled explicitly in the formalization and are worth clarifying in print:

1. The author has now specified L(x)=exp(S(x)), where S(x)=log(x)log_3(x)/log_2(x). This definition
   is absent from the attached text but is used throughout this audit.
2. In Lemma 2, the first Rankin inequality can be stated for arbitrary positive eta,delta, but
   the infinite products should be used only after choosing parameters that ensure convergence.
   Alternatively all intermediate products can first be finite. In Lean, an infinite sum is
   not automatically interpreted as +infinity when it diverges; convergence must be proved.
   For the actual chosen parameters it holds, as checked below.
3. Counting exceptional integers also counts exceptional amicable pairs because the partner
   is uniquely determined by s. This observation is implicit in the current structural proof.
4. Every o(1) used in the subsequent summations must be uniform in the summed variables. The
   estimates in this proof provide that uniformity, as detailed below. Constants can depend
   on the fixed epsilon.

No changes have been made to the manuscript.

## 1. Precise target and asymptotic scales

Write t=log_2(x), u=log_3(x)=log(t), and S=log(x)u/t. Then

    S/log(x) = u/t -> 0,      log_2(x)/S -> 0.

Thus every fixed power of log(x) is L(x)^{o(1)}. Also, for every fixed c>0 and C>0,

    x^{1-c+o(1)} = o(x exp(-C S)).

A precise target avoiding an unspecified error function is:

    For every real c<1/2, there exists x0 such that for all real x>=x0,
    A(x) <= x exp(-c S(x)).

The proof establishes the stronger-than-needed intermediate statements for each fixed
0<epsilon<1/10 with coefficient 1/2-4epsilon+o(1). Given c<1/2, choose epsilon small enough
that c<1/2-4epsilon and then absorb the error. No uniformity in epsilon is needed.

## 2. Weighted technical lemma

H(v)=v_{<=y} y^{Omega(v_{>y})}, y=log(x), is completely multiplicative on positive integers.
For squarefree b, sigma(b)=product_{q|b}(q+1); hence H(sigma(b)) is multiplicative as a function
of squarefree b. Primes may repeat in the factorizations of different q+1: complete
multiplicativity is exactly what is needed here.

For each exceptional b<=Y,

    1 <= Y^{1+delta} x^{-kappa eta} H(sigma(b))^eta / b^{1+delta}.

Summing and expanding over finite sets of primes gives the Rankin bound in the text. The
infinite version follows by increasing the finite sets once convergence has been proved.

For the chosen parameters

    A=t/u^2,       eta=(log A)/t,       delta=1/t,

we have A>1, eta>0, delta>0 eventually, and y^eta=A. The following estimates are uniform in
1<=Y<=X=x log(x):

    delta log(Y) <= (log(x)+log_2(x))/t = o(S),
    eta log(x) = S(1-2 log(u)/u).

Thus the prefactor is Y exp(-(kappa+o(1))S).

For convergence of the auxiliary sum over v, the finitely many factors p<=y have ratios
p^{-1-delta+eta}<1 eventually, since eta<1/4 eventually. For p>y the ratios A p^{-1-delta}
are at most A/y=o(1), and their sum converges for each fixed x because delta>0.
The nonnegative Euler product therefore represents a finite sum over v.

The discarded logarithmic terms are uniformly bounded: for p<=y their total is
O(sum_{n>=2} n^{-3/2}) when eta<1/4; for p>y it is
O(A^2 sum_{n>y} n^{-2})=O(A^2/y)=o(1). The first-order terms are at most

    A sum_{p<=y} 1/p + A sum_{p>y} p^{-1-delta}.

Mertens' estimate gives the first term (1+o(1))t/u. The Euler product for zeta and
zeta(1+delta)<=1+1/delta bound the second by A(log(1/delta)+O(1))=(1+o(1))t/u.
Consequently the sum over q in the Rankin bound is at most exp((2+o(1))t/u).
Its ratio to S tends to zero: log(S)=t+log(u)-u, while (2+o(1))t/u=o(t).
This verifies the claimed error, including uniformity in Y.

`MertensUpper.lean` proves the consequence of Mertens used here, with leading
coefficient one and an absolute additive constant. `MomentEuler.lean` and
`TechnicalLemma.lean` complete the convergent Euler-product and uniform Rankin steps.
The full two-sided Mertens asymptotic is not needed for this upper estimate.

## 3. Structural reduction

The Pollack statement in Lemma 1 agrees with Theorem 1.1 of the cited paper:
https://www.pollack-math.net/combined3.pdf . `PollackTheorem.pollack` now proves the
stated uniform estimate. Its hypothesis holds for G=Y^{1/rho}, Y=exp(S/2), since
log G=S/(2rho) grows faster than (log log X)^{1/2}.

Both members of the pair are <=X for sufficiently large x. In fact the elementary inequality
s(n)<=n log(n) already suffices: sigma(n)/n=sum_{d|n}1/d<=sum_{d<=n}1/d<=1+log(n).
The cited stronger bound for sigma is valid and more than sufficient.

The squarefull estimate used here is correct. Every squarefull q is expressible as a^2 b^3
with b squarefree, so its counting function is O(sqrt(T)) by summing b^{-3/2}. Summing over
dyadic intervals gives sum_{q>Y^2, squarefull}1/q=O(1/Y). Integers divisible by any such q
therefore contribute O(X/Y). Integers <=X/Y contribute the same bound. Taking a union for
both members costs at most an absolute factor, since an amicable integer determines its partner.

B consists of the full squarefull part and the remaining shared primes, and is a unitary
divisor of n. The latter primes have product dividing gcd(n,n'), so B<=Y^2Y^{1/rho}.
The stated size and cross-coprimality properties follow; both squarefree parts exceed 1
eventually, allowing their largest prime factors to be compared.

The first elimination identity is correct. Its positive right side forces a nonzero
coefficient of p'. Fixed m,m' consequently give at most one p', then at most one p via
mp=p's(m')+sigma(m'). The number of m,m' with mm'<=X/Y is at most
(X/Y)(1+log(X/Y))=O((X/Y)log x).

For p>x^{4/5}, the inequalities m<=x^{1/5+o(1)}, m'>=x^{4/5+o(1)},
p'<=x^{1/5+o(1)} are consistent. The least divisor D of a' above x^{1/2} exists. Removing
any one of its prime factors leaves a divisor <=x^{1/2}, so D<=x^{1/2}p'. D is unitary in n'
and gcd(D,sigma(D))=1 by cross-coprimality. The second elimination identity is correct.
Solving the resulting linear congruence gives either no M or one class modulo
sigma(D)/gcd(sigma(D),sigma(m)). The upper bound 1+X sigma(m)/D^2 follows from sigma(D)>=D.

Finally, sum_{m<=Z}sigma(m)=O(Z^2): expand sigma(m) as a divisor sum and use
sum_{k<=Z} sum_{d<=Z/k} d = O(Z^2 sum_{k>=1}k^{-2}). Thus the final displayed bound
x^{0.92}+X x^{0.42}x^{-1/2}=O(x^{0.92}log x) is correct.

## 4. Case I: constructing and recovering R

If u divides AB, then u/gcd(u,A) divides B; this follows prime by prime, with multiplicities.
It justifies the definition of r. Factoring r among the q+1 also works with repeated prime
factors. The e_q need not be relatively prime.

The product of the q with e_q>q^{9/10} is at most r^{10/9}. Hence
r0>=a'/r^{10/9}=x^{1/9+o(1)}>x^{1/10}, using r<=p+1<=x^{4/5}+1. The harmless +1 is absorbed
in o(1). This is enough to construct R in either of the two ways stated.

R is squarefree and unitary in n'. Dividing p+1 by product_{q|R}e_q gives an integer d
dividing sigma(m), even if g and the e_q share prime factors. The product of divisibility
relations suffices; pairwise coprimality of those factors is not required.

For Type I the linear congruence and p∤s(m) give at most one R in 0<R<p. For Type II the
coprimality of R and sigma(R), and that of p and sigma(m), are justified in the text. The
determinant is an integer divisible by p whose absolute value is at most x^{4alpha+o(1)}.
Since p>x^{epsilon^2} and 4alpha=2epsilon^2/5, the determinant must vanish. Equality of
reduced fractions gives R1=R2. The two types may overlap, but the upper bound of two remains valid.

The integer reconstruction, coprimality, and asymptotic size steps are checked in
`CaseReconstruction.lean`, and instantiated with the actual divisor sum. The construction
from an amicable pair is completed in `CaseOneWitness.lean`.

## 5. Case I: counting

For fixed dyadic P,U and m<=X/U, all relevant d divide sigma(m). Uniformly for m<=X,
sigma(m)<=X(1+log X)=x^{1+o(1)} and the standard divisor bound gives tau(sigma(m))=x^{o(1)}.
The needed divisor bound can be proved elementarily: for each fixed h>0, separate finitely
many small primes; for the remaining primes, e+1<=2^e<=p^{he}. The small primes contribute
a finite constant to tau(N)<=C_h N^h.

For fixed d the interval P<=p<2P contains at most 1+P/d numbers in the class -1 modulo d.
Since d>=P/(2U)^{9/10}, this is O(U^{9/10}). Each p admits at most two R. Thus the count is
at most X U^{-1/10}x^{o(1)}. Importantly, U>x^alpha/2, not merely U>x^{alpha/2}; the draft
has the correct version. The saving is x^{-alpha/10+o(1)}. The number of dyadic intervals is
O(log^2 x), which is absorbed in x^{o(1)}.

Overcounting through multiple possible d or representations causes no problem: each actual
pair has at least one admissible representation, and the estimate is an upper bound.

## 6. Case II: exceptions and selection

Choosing R with x^epsilon<=R<=x^{epsilon+epsilon^2} is justified by multiplying prime factors
of a until the first threshold is reached. It is a unitary divisor of n. For fixed b there
are at most X/b integers n<=X divisible by b, irrespective of the other factorization choices.

The exceptional b bound is uniform in Y. If E(t)<=t F(x) on 1<=t<=X, partial summation gives
sum_{exceptional b<=X}1/b <= F(x)(1+log X). This proves the exceptional bound in the text;
no independent summation over B or R is needed.

The factorization into V0,V1,...,Vt is valid, and t>=1 eventually because a'=x^{1+o(1)} and
2epsilon+3epsilon^2<1. The distribution r=product d_i does not require coprime d_i.

Put E_i=log(V_i/d_i)+(log_2 x)Omega(d_i). Additivity of Omega on products gives exactly
sum E_i=log(a'/r)+(log_2 x)Omega(r). Substitution of the definition of r gives the bound
(1/2-3epsilon+epsilon^2+o(1))log x; the displayed intermediate calculation is correct.

E_0>=-log(sigma(V0)/V0)>=-log_2 x eventually. The contradiction in the averaging argument
has a fixed positive margin, because its coefficient difference is

    (1/2-epsilon)(1-2epsilon-3epsilon^2) - (1/2-3epsilon+epsilon^2)
       = epsilon - epsilon^2/2 + 3epsilon^3 > 0.

It follows that an i>=1 satisfies the desired inequality. Such d_i cannot equal 1: otherwise
log V_i <=(1/2-epsilon)log V_i with V_i>1. Exponentiating and using the upper bound on V_i
gives (V/d)exp(J log_2 x)<=x^{epsilon-4epsilon^3}, with the exponent calculated correctly.

## 7. Case II: reconstruction and counting V

The reconstruction uses a modulus V, which need not be prime. Cross-coprimality implies
gcd(mR,V)=1. From the congruence, any common divisor of sigma(m),V would divide mR, so
sigma(m) is invertible modulo V. The determinant of two solutions is divisible by V and
has absolute value at most x^{2epsilon+2epsilon^2+o(1)}, whereas V>x^{2epsilon+3epsilon^2}.
The fixed positive exponent gap epsilon^2 makes the determinant zero for large x.
The reduced-ratio conclusion is therefore legitimate.

The reciprocal-prime estimate is uniform in the modulus a. To derive it from Brun--Titchmarsh,
treat primes <=2a directly (at most two possibilities, each >=a/2 for a>=2). For primes >2a,
partial summation bounds the contribution by a constant times

    1/phi(a) * (1 + integral_{2a}^X dt/[t log(t/a)]).

The integral is O(1+log log X). The case a=1 is the ordinary prime reciprocal bound, and
1+log log X=O(log log X) uniformly for X>=3. Thus the exact estimate used in the draft follows.
`SieveAsymptotics.lean` proves the arithmetic-progression sieve estimate with an
absolute constant; `PrimeReciprocals.lean` proves the uniform reciprocal estimate.
The sharp constant 2 in Brun--Titchmarsh is not needed or claimed by this formalization.

Each admissible V is represented by an unordered factorization of d into factors >1, an
ordered list of associated primes, and a remaining cofactor u. Sorting the d_i is legitimate:
every V supplies at least one such list, including when factors are equal. No extra h! is
required for an upper bound. Distinctness of the chosen primes and squarefreeness of u can
be dropped when taking upper bounds.

If J=Omega(d), there are at most J^J unordered multiplicative partitions, by mapping set
partitions of J distinguished prime occurrences onto them. No sum over h is missing: that
bound already includes all possible numbers of factors. Since all primes dividing d exceed y,
product d_i/phi(d_i) <= exp(2J/y), with repeated primes counted as necessary. This step does
not require d squarefree.

The logarithm of the remaining factor is bounded as claimed. More explicitly, for J>=1,

    log J <= log_2 x - log_3 x,
    log(C log_2 X) = log_3 x + O(1),
    log log X = log_2 x + o(1),      2J/y <= 2/log_2 x.

Adding these gives J log_2 x + O(J+log_2 x), uniformly for J<=log x/log_2 x. Thus the
reciprocal bound is uniform in d. In the final count the error is x^{o(1)}, since
(J+log_2 x)/log x=O(1/log_2 x)+o(1), uniformly in the same range.

Multiplying the reciprocal bound by the admissible upper limit
d x^{epsilon-4epsilon^3}exp(-J log_2 x) cancels both the factor d and the main J-dependent
exponential. This leaves x^{epsilon-4epsilon^3+o(1)} possible V for each fixed m,d.
There are at most Xx^{-epsilon} values of m and uniformly x^{o(1)} choices of d per m.
Uniqueness of R then gives x^{1-4epsilon^3+o(1)} as claimed.

## 8. Formalization and its scope

Lemma 1, Lemma 2, Proposition 3, and the main counting theorem are now proved in the
formal development. The final statement counts actual positive integers in distinct
amicable pairs, with no bound imposed on the partner. It has no unproved structural
or analytic hypotheses. The axiom report contains only `propext`, `Classical.choice`,
and `Quot.sound`; it does not contain `sorryAx` or custom mathematical axioms.

This is a formalization of the manuscript's argument, with explicit finite sets,
uniform tolerances, and exceptional-set bookkeeping. Some intermediate estimates
are weakened after obtaining a fixed power saving; others are stated as finite
versions before taking limits. `PROOF_MAP.md` records these choices, including
separately checked versions of the sharper Case I saving and totient calculation.
The informal audit alone is not the certificate: the certificate is the Lean proof
and its checked dependencies. Verifying that formal statements accurately represent
a prose manuscript still requires reading the definitions and their correspondence.

No assertion about novelty or the optimal true order of A(x) is part of this certificate.
