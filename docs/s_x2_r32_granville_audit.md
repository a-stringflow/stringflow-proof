# S-R3.2 literature audit: why Granville cannot be cited directly

Date: 2026-08-06

This note records the literature audit for S-R3.2. The conclusion is
that the standard primitive-divisor theorem for Lucas sequences does
not directly apply to

    D_m = X A^m - Y B^m
        = 2^n_{k-1} (2^n_k)^m - 5^d_{k-1} (5^d_k)^m.

S-R3.2 therefore remains an open adaptation, not a citation.

## 1. Granville's theorem

Granville, "Primitive prime factors in second order linear recurrence
sequences" (Acta Arith. 155, 2012; arXiv:1212.6306), proves the
following for the standard Lucas sequence

    x_n = (r^n - s^n) / (r - s),

where r and s are pairwise coprime integers, 2 divides rs but not 4:
for every n > 1, except possibly n = 2 and n = 6, x_n has a primitive
prime factor dividing x_n to an odd power.

This is a theorem about the sequence with initial values

    x_0 = 0,   x_1 = 1.

## 2. The sequence D_m is not standard

D_m satisfies the same second-order recurrence

    D_{m+2} = (A+B) D_{m+1} - AB D_m,

but its initial values are

    D_0 = X - Y,
    D_1 = X A - Y B.

It is a linear combination of the standard Lucas sequences:

    2 D_m = (A-B)(X-Y) U_m + (X+Y) V_m,

where U_m = (A^m - B^m)/(A-B) and V_m = A^m + B^m.  Granville's
theorem does not cover arbitrary linear combinations of U_m and V_m
with initial values not equal to (0,1).

No reduction to a standard Lucas sequence term was found. In
particular:

- The continued-fraction determinant gives
  T_m d_k - P_m n_k = +/-1, but this only changes the exponents by
  one and does not produce a binomial r^n - s^n with equal exponents.
- Raising D_m to a power or multiplying by X,Y does not clear the
  coefficients in a way that produces (r^n - s^n)/(r-s).
- The theorem for A^m-B^m cannot be cited because D_m carries the
  coefficients X,Y.

## 3. Current certified coverage

`s_x2_r32_small_certificate.txt` gives explicit primitive primes
p <= 100000 for 188 of 236 records:

    records=236
    records_with_primitive_below_limit=188
    records_without_primitive_below_limit=48

The 48 uncovered records need either a generalized theorem or a
larger prime certificate.

## 4. Status

- Granville's theorem is correctly identified but does not close
  S-R3.2.
- S-R3.2 remains open.
- The p-adic valuation formula in `s_x2_r32_valuation_lemma.md`
  is exact but is a consequence of the no-primitive-factor
  assumption; it does not provide the required contradiction. The
  open task remains a generalized primitive divisor theorem or a
  separate argument for a prime outside A-B.
