# S-R3.2: exact p-adic valuation and the remaining gap

Date: 2026-08-06

This note proves one exact p-adic valuation formula and reduces
S-R3.2 to a precise bound. It does not claim that S-R3.2 is closed.

## 1. Notation

For a fixed ray write

    A = 2^n_k,  B = 5^d_k,  X = 2^n_{k-1},  Y = 5^d_{k-1},

    D_m = X A^m - Y B^m.

Here gcd(AB,XY)=1 and gcd(D_m,10)=1.

## 2. Lemma (p-adic valuation formula)

Let p be an odd prime, p not 2 or 5, and suppose

    p | A-B,   p | D_m.

Let alpha = A/B and xi = X/Y in Q_p, and let c in Z_p be the unique
p-adic number satisfying

    xi * alpha^c = 1.

Then

    v_p(D_m) = v_p(A-B) + v_p(m-c).

Proof. From p | A-B and p | D_m,

    D_m = X A^m - Y B^m = B^m(X-Y) mod p,

and p does not divide B, so p | X-Y. Hence alpha = 1 mod p and
xi = 1 mod p. The p-adic logarithms of alpha and xi are nonzero, so

    c = -log(xi)/log(alpha)

lies in Z_p. Since xi alpha^c = 1,

    xi alpha^m - 1 = -xi alpha^m (alpha^{m-c} - 1),

and xi alpha^m is a p-adic unit. For odd p and U=alpha-1 with
v_p(U)>0, the standard p-adic exponential gives

    alpha^n - 1 = exp(n log(alpha)) - 1,

and v_p(exp(z)-1)=v_p(z) whenever v_p(z)>0. Therefore

    v_p(alpha^{m-c}-1)
    = v_p(m-c) + v_p(log(alpha))
    = v_p(m-c) + v_p(alpha-1)
    = v_p(m-c) + v_p(A-B).

Combining these identities proves the lemma. QED

## 3. Corollary: shape under the no-primitive-factor assumption

If p | D_m and p does not divide A-B, then p is already the primitive
factor required by S-R3.2. Thus, if D_m has no primitive factor, every
prime p | D_m satisfies p | A-B. By the lemma, for every p | D_m,

    v_p(D_m) = v_p(A-B) + v_p(m-c_p).

Hence

    D_m | (A-B) * N_m,

where

    N_m = product_{p|D_m} p^(v_p(m-c_p)).

This divisibility is automatic under the no-primitive-factor
assumption: by the same formula D_m is equal to the part of A-B
supported on p | D_m times N_m, and that part divides A-B.  Therefore
the inequality D_m > (A-B) * N_m can never hold in the case being
considered, so it cannot be used as an equivalent criterion for
S-R3.2.

## 4. Current gap

The lemma turns the exponent of every common prime factor into a
p-adic distance v_p(m-c_p), but it is a consequence of the
no-primitive-factor assumption rather than a route to a contradiction.
The remaining task is one of the following:

1. A generalized Lucas/Lehmer primitive divisor theorem showing that
   W_m = X A^m - Y B^m is a non-degenerate generalized Lucas sequence
   covered by the Bilu-Hanrot-Voutier framework, with the finitely
   many exceptional m in [1,25] handled explicitly; or
2. A separate argument proving that D_m has at least one prime divisor
   outside A-B, without relying on the automatic divisibility above.

Neither direction is closed yet. The small-prime certificate
s_x2_r32_small_certificate.txt covers 188 of 236 records with an
explicit primitive prime p <= 100000; the remaining 48 records still
need one of the two directions above.

## 5. Status

- The lemma in Section 2 is proved analytically and does not use
  enumeration.
- S-R3.2 as a whole remains open.
- This note does not treat "no prime below 100000 found" as a proof.
