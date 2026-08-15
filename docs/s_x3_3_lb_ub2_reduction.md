# L-B': reduction to words with at most two t=2 steps

Date: 2026-08-06

This note proves a structural reduction for L-B'. It shows that only
words with U <= 2 need a k=0 analysis; every word with U >= 3 is
handled by the already-proved k>=1 branch.

## 1. Notation

For a rising word w of length L, let U be the number of t=2 steps,
S=L+U, and t_{L-1}=1. Let A_u=A_L be the rise-word numerator and let
r(w) be the least positive start in the word's congruence class.
The defining congruence is

    5^L r + A_u = 3*2^S + k 2^(S+3)

for a unique nonnegative integer k. The k=0 case is exactly the case
where A_u < 3*2^S and the resulting numerator is divisible by 5^L.

## 2. A_u lower bound

For t_{L-1}=1 and all valid words, 52.16 gives

    h = A_u / 5^L >= 1/3.

Hence A_u >= 5^L/3.

## 3. U >= 3 implies k >= 1

Suppose U >= 3. The H3 condition is 2U <= L+1, so L >= 2U-1.
Therefore

    2^S / 5^L
    = 2^U (2/5)^L
    <= 2^U (2/5)^(2U-1)
    = (5/2) (8/25)^U.

For U=3 this is (5/2)*(8/25)^3 = 0.08192 < 1/9. The function
(5/2)(8/25)^U is strictly decreasing in U, so for all U >= 3,

    2^S / 5^L < 1/9.

Equivalently 5^L/3 > 3*2^S. Together with A_u >= 5^L/3 this gives
A_u > 3*2^S, so k cannot be 0. Hence k >= 1.

## 4. k >= 1 branch closes L-B'

If k >= 1, then

    r >= (2^(S+3) - 1)/5.

For every S >= 1,

    (2^(S+3) - 1)/5 >= 2^(S/5)

and a fortiori >= 2^(S/5)/3 and >= 2^(S/5)/5. Therefore the weak
bound, the strong bound for r=3 mod 5, and the intermediate bound for
r=4 mod 5 all hold in the k>=1 branch. This is the already-proved
L-B'c branch.

## 5. Reduction

By Sections 3 and 4, L-B' is reduced to words with U in {0,1,2}.

`verify_lb_ub2_words.py` checks all such words for L <= 250 and writes
`lb_ub2_words_certificate.txt`:

    words_checked=2573499
    fails=0
    RESULT: PASS

That is a certificate, not the proof. The analytic proof for U<=2 is
the remaining part of L-B'a/b.

## 6. U=0 closed form and proof

For the all-ones word of length L, S=L and

    A_u = (5^L - 2^L)/3.

The congruence gives the exact minimal start:

    r = (2^(L+1) - 1)/3          if L is odd,
    r = (5*2^(L+1) - 1)/3        if L is even.

Proof: multiply the defining congruence by 3. One obtains

    5^L(3r+1) = 2^(L+1)(5+4k),

so q=(5+4k)/5^L is a positive integer with 3r+1=2^(L+1)q. The
integrality of k forces q=1 mod 4, and the integrality of 3r+1 forces
q=1 mod 3 when L is odd and q=2 mod 3 when L is even. The least
q satisfying both is q=1 (L odd) or q=5 (L even), giving the formulas
above. QED

For L odd, r >= (2^(L+1)-1)/3, and for L even, r >= (5*2^(L+1)-1)/3.
In both cases the required bounds

    r >= 2^(L/5)/5,
    r >= 2^(L/5) if r=3 mod 5,
    r >= 2^(L/5)/3 if r=4 mod 5

are immediate for L>=2; the single L=1 case r=1 is checked directly.
Thus U=0 is closed analytically.

## 7. U=1 and U=2: exact equations

Let one t=2 be at position j, 0<=j<=L-2. Then

    A_u = (5^L - 2^L)/3
        + 2^(j+1) (5^(L-1-j) - 2^(L-1-j))/3.

Multiplying the defining congruence by 3 gives

    5^(L-1-j) (5^(j+1)(3r+1) + 2^(j+1))
    = 2^(L+2)(5+4k).

For two t=2 positions j1<j2 with j2>j1+1, the analogous equation has
two doublings. Put m1=j1+1, m2=j2+1, d=m2-m1. Then

    A_u = (5^L + 2^(j1+1) 5^(L-j1-1)
              + 2^(j2+2) 5^(L-j2-1)
              - 4*2^L)/3,

and the congruence becomes

    5^(L-m2) *
    ( 5^(m2)(3r+1) + 2^(m1) 5^d + 2^(m2+1) )
    = (40 + 96k) 2^L.

Hence, with Q=(40+96k)/5^(L-m2) and
R=2^(m2+1)+2^(m1)5^d,

    r = (2^L Q - R - 5^(m2)) / (3*5^(m2)).

These equations are exact. U=1 is closed in Section 7a. The analytic
proof for U=2 from these equations is not yet complete; the numerical
certificate above is the current evidence.

## 7a. U=1 is closed

For U=1 put m=j+1 and e=L+2-m, so 1<=m<=L-1 and e>=2. From the
exact equation one gets

    r = (2^(L+2) Q - 2^m) / (3*5^m),

where Q is a positive integer congruent to 1 mod 4 and satisfying

    2^(L+2) Q = 2^m mod 5^m.

Let Q0 be the least positive residue of 2^(-e) modulo 5^m. Then
Q >= Q0. Two lower bounds follow:

    Q >= 1   =>  r >= (2^(L+2) - 2^m) / (3*5^m),

    Q0 >= (5^m+1)/2^e  =>  r >= 2^m/3.

The second bound is because 2^e Q0 = 1 + c 5^m with c>=1, so
Q0 >= (5^m+1)/2^e.

Now use the maximum of the two lower bounds:

    r >= max( (2^(L+2) - 2^m) / (3*5^m),  2^m/3 ).

Suppose both bounds were below the strong target
T = 2^((L+1)/5). From 2^m/3 < T one gets

    m < (L+1)/5 + log_2(3).

From (2^(L+2)-2^m)/(3*5^m) < T, using 2^(L+2)-2^m >= 2^(L+1),
one gets

    5^m > 2^(L+1) / (3 T)
          = 2^((4/5)(L+1)) / 3,

so

    m > log_5( 2^((4/5)(L+1)) / 3 )
      = (4/5)(L+1) log_5(2) - log_5(3).

For L >= 16 these two inequalities are incompatible:

    (4/5)(L+1) log_5(2) - log_5(3)
    > (L+1)/5 + log_2(3).

The finite cases L <= 15 are included in the certificate in Section 5.
Therefore r >= T whenever r=3 mod 5, and hence the intermediate and
weak bounds as well. U=1 is closed.

## 7b. U=2 remains open

The exact equation for U=2 is written in Section 7. The same two-bound
strategy should apply, but the algebra has not yet been completed.
This is now the only open subcase of L-B'a/b.

One useful numerical observation: for all U=2 words with L <= 100,
the least solution k of the defining congruence already gives
c=3r+1 >= 1, and

    min c / 2^((L+2)/5) = 59.0479...

at L=11, m1=1, m2=7. This is certificate evidence that the margin is
large, but it is not a proof for all L.

## 8. Status

- U>=3 words are closed by the k>=1 branch.
- U=0 words are closed by the exact formulas in Section 6.
- U=2 is the only open subcase of L-B'a/b.
