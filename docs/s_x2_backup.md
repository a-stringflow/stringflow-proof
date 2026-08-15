# S-X2 后备路线：周期素因子 + b 窗口

日期：2026-08-06

状态：**已切换为当前主攻路线**。L-B′a/b 仍开放，但不再阻塞条件版
定理 53.4-LB；S-X2 作为独立后备继续推进。

## 1. 目标

对 `surv_ray_certificate.txt` 中每条 SURV-RAY 射线、窗口内每个
`m`，证明存在一个素因子

$$
p\mid D_m=2^{n_{k-1}+m n_k}-5^{d_{k-1}+m d_k}
$$

使得全局方程

$$
D_m\,m_0=2^S A_{\mathrm{chain}}+5^Q A_u
$$

模 $p$ 对全部可行 $b$ 无解。这里 $S=L+U$，
$A_{\mathrm{chain}}$ 是 C3 链分子，$A_u$ 是上升段分子。

## 2. 已闭合

1. Lucas 递推：

   $$
   D_{m+2}=(2^{n_k}+5^{d_k})D_{m+1}-2^{n_k}5^{d_k}D_m.
   $$

2. $\gcd(D_m,10)=1$。
3. 若奇素数 $p\ne5$ 同时整除 $D_m,D_{m+1}$，则
   $p\mid 2^{n_k}-5^{d_k}$；因此不整除 $A-B$ 的素因子在相邻项
   之间隔离，称为本路线的“原初素因子”。

证明见 `surv_ray.md` S-R3 与 `surv_ex.md` S-X2。

## 3. MODp 审计：小素因子门不能单独排除

对 25 条 `x0>10^6` 记录，`modular_x0_gt_1e6_audit.txt` 给出：

- 每条记录都有小素因子 $p\mid D_m$；
- 对阶较小的 $p\le257$，A/B 族的
  $A_{\mathrm{tot}}=2^S A_{\mathrm{chain}}+5^Q A_u$ 在模
  $p^{v_p(D_m)}$ 下均可满足；
- 显式见证同时给出可行 $b$ 与词形（`2first` / `2last`）。

因此“固定小模数 + MODp”单独不能关闭任何记录。

## 4. 周期素因子现状

对 37 条不同射线检查 p=3 奇偶族结构：

$$
3\mid 2^{n_k}+5^{d_k},\qquad
3\mid D_0\ \text{或}\ 3\mid D_1
$$

覆盖 29 条射线；其余 8 条如下（括号内为该射线窗口内 `m` 的小素
因子，精确模算术检查）：

| 射线 `base step` | 窗口 `m` | `D_m` 的小素因子 |
|---|---:|---|
| `475127550 579001193` | 2 | 257 |
| `475127550 579001193` | 3 | 无（`p≤5000`） |
| `174131244785 845863046269` | 1 | 无（`p≤5000`） |
| `298062923185496768844379933181551 331649849240626233041930875510999` | 1 | 7, 97, 193 |
| `629712772426123001886310808692550 3480213711371241242473484918973749` | 1 | 191, 449 |
| `11700066678965969731193076374306347 19290206874134575218026357020946395` | 1 | 无（`p≤5000`） |
| `30990273553100544949219433395252742 81270753980335665116465223811451879` | 1 | 3, 827 |
| `692856372074751835612134300261174121 5043526386037034724467089982846375347` | 1 | 7 |
| `113535474199599999405542366942646797618 351386331742948819501173415093894317669` | 1 | 无（`p≤5000`） |

## 5. Current m0 interval criterion (corrected)

For fixed `(Q,P,T,m)` and feasible b, use the A_chain bounds from
52.10/52.12 and the A_u bounds from 52.16 to define

    N_min(b) = 2^S A_chain,min(b) + 5^Q A_u,min(L,U),
    N_max(b) = 2^S A_chain,max(b) + 5^Q A_u,max(L,U).

Every solution must satisfy

    m0 = N / D_m in [N_min(b)/D_m, N_max(b)/D_m].

If this interval is disjoint from the allowed m0 range (frame A
[7,10^6], external records (10^6,S4]), then b is excluded. If the
absolute width satisfies

    m0_max - m0_min < 1,

then there is at most one integer m0 candidate. The earlier statement
"if the interval width is < D_m then there is at most one integer"
is wrong: the numerator interval width is D_m*(m0_max-m0_min), so
uniqueness is equivalent to m0_max-m0_min<1. A log2 width <1 also does
not imply integer uniqueness; for the Q=17 sample the absolute m0
width is about 10^8. Thus no record is currently in the point-check
branch.

Calibration: verify_s_x2_m0_interval.py samples endpoints and
midpoints of the A/B b-windows over all 236 records and finds every
sampled interval intersecting (10^6,S4]:

    records=236
    overlap_samples=1416
    records_all_sampled_b_disjoint=0
    RESULT: CALIBRATION (NO INTERVAL-ONLY EXCLUSION)

So closed-form intervals alone close no record.

## 5bis. Small primitive prime certificate

verify_s_x2_r32_small.py checks all 236 records for primes p<=100000
satisfying

    p | D_m,   p does not divide 2^n_k - 5^d_k.

The first five such primitive primes per record are written to
s_x2_r32_small_certificate.txt. This is a finite arithmetic
certificate, not an existence proof:

    records=236
    records_with_primitive_below_limit=188
    records_without_primitive_below_limit=48

The 48 uncovered records include Q=15, Q=24, Q=26, Q=47, Q=71, and
others. For these, S-R3.2 still needs a generalized Lucas primitive
divisor theorem or a larger prime certificate. "Not found" is not a
proof.

## 5ter. Exact MODp + H3 hits (blocking examples)

verify_s_x2_p3_h3_counterexample.py certifies two explicit word shapes
for Q=17, P=371253907 (the record already listed in modular_x0_gt_1e6_audit.txt):

1. MOD3 hit: A-family constant C3 chain with the rise word
   1 (21)^U 1, U=185626944. It satisfies 2U <= L+1, last symbol 1,
   and A_tot == 0 mod 3.
2. MOD9 hit: A-family rise word with U=0 (all ones) and C3 excess
   residues E_15=1, E_16=5. It satisfies H3 and A_tot == 0 mod 9.

Since v_3(D)=2 for this record, the p=3 gate cannot close it even
after adding the H3 word-form filter. This is a blocking example, not a
proof that the record survives; it only rules out one naive closure.

## 5quater. Existing complete exclusions and further blockers

verify_surv_ex_interval_certs.py re-verifies the 25 existing S-X3.3
gap-interval certificates and reports RESULT: PASS. These records are
already completely excluded by the interval-basin route, not by S-X2:

- Q=15: 1 record
- Q=17: 2 records
- Q=19: 2 records
- Q=20: 4 records
- Q=21: 11 records
- Q=22: 5 records

For the tested primitive primes
p in {7, 89, 10337, 2879, 9209} on the Q=17 records, the A-family
constant rise word U=0 admits a C3 excess sequence making
A_tot == 0 mod p. In other words, "p | D_m" plus "U=0" plus H3 is
satisfiable for these examples, so MODp alone cannot close those
records; the remaining gate must be H_exact.

## 6. Blockers

1. S-R3.2/3.3: prove that every D_m has a prime divisor not dividing
   A-B. 5bis gives small-prime certificates for 188/236 records; the
   remaining 48 have no certificate below 100000. Standard
   Lucas/Lehmer theorems for A^m-B^m do not apply directly because
   D_m = X A^m - Y B^m has coefficients X=2^n_{k-1}, Y=5^d_{k-1}.
2. Large-prime computability: exponents of D_m reach 10^23, so direct
   factorization is infeasible; Pocklington/Pratt certificates or
   analytic lower bounds are needed.
3. MODp satisfiability: small-prime gates have explicit witnesses and
   cannot exclude by themselves. Existing witnesses such as Q=17
   b=86077223 often violate H3 (2U<=L+1), so MODp must be combined
   with H_exact.
4. S-X4 coverage: Q=8..100 and 236 records are a certificate, not a
   proof that windows terminate for Q>100. The 220-digit extension
   `scan_surv_ray_extension.py` certifies 18 additional records for
   Q=211..215 (see `surv_ray_extension_q211_215_prec220.txt`).
   Therefore S-X4 cannot be closed by extending the certificate in the
   finite-certificate route; it needs an analytic argument for all Q.
   With L-B'/U=2 closed, the whole-family S-X3.3c bound
   S0(m) <= 5 log2(5m) bypasses S-X4 entirely; S-X4 is no longer a
   required dependency (2026-08-12).

## 7. Next steps

1. Close S-R3.2 for the 48 uncovered records, with a verifiable lower
   bound; for the 188 covered records, prove that the primitive prime
   actually excludes all feasible b.
2. For the 5bis-covered records, apply the corrected m0 interval
   criterion together with H_exact over the b-window.
3. For the 48 records with no small primitive prime, construct or
   prove a large primitive prime.

Status: as of 2026-08-06, no SURV-RAY record has a complete S-X2
exclusion chain. The certified MOD3/MOD9 examples in 5ter show that
p=3 cannot close Q=17, P=371253907 even after H3; interval-only
calibration remains non-excluding for all sampled b.

This document records state and criteria; it never treats "no
counterexample found" as a proof.
