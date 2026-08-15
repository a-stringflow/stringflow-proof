# L-B'a: exact W characterization and the weight-lemma reduction

Date: 2026-08-06

This file records the parts of the L-B'a chain argument that are now
proved exactly, and states the single remaining analytic subproblem.
It is not a proof of L-B'a.

## 1. The word-start set W

Let $W$ be the set of odd $r$ for which some nonempty word
$w=(t_0,\dots,t_{L-1})$, with $t_j\in\{1,2\}$ and $t_{L-1}=1$, has
minimal start equal to $r$.

For odd $r$, run the accelerated map

$$
n_{j+1}=\operatorname{oddpart}(5n_j+1)
$$

from $n_0=r$ until $n_L\equiv3\pmod8$, and record

$$
t_j=v_2(5n_j+1).
$$

**Lemma 1 (exact membership).** $r\in W$ iff all recorded $t_j$ are in
$\{1,2\}$, the word is nonempty, and

$$
r<2^{S+3},\qquad S=\sum_{j=0}^{L-1}t_j.
$$

Proof. If the recorded word has some $t_j>2$, then no word with the
required alphabet can have $r$ as a start, so $r\notin W$. Otherwise
the orbit identity gives

$$
2^S n_L=5^L r+A_u,
$$

with $n_L\equiv3\pmod8$, hence

$$
5^L r+A_u\equiv3\cdot2^S\pmod{2^{S+3}}.
$$

Therefore $r$ is a solution for the word $w$. All solutions modulo
$2^{S+3}$ are congruent to $r$, so the least positive solution is
exactly $r$ when $0<r<2^{S+3}$. Conversely, if $r\in W$, its first
word is nonempty, all $t_j\in\{1,2\}$, and the least solution is
$r<2^{S+3}$. $\square$

## 2. Unique odd k=0 parent

A k=0 parent $p$ of $r$ satisfies

$$
p=\frac{5r+1}{2^t},\qquad t\in\{1,2\}.
$$

Both $p$ and $r$ are odd. If $t=1$, then $p$ is odd iff $r\equiv1\pmod4$.
If $t=2$, then $p$ is odd iff $5r+1\equiv4\pmod8$, which is equivalent
to $r\equiv7\pmod8$. Hence there is at most one odd k=0 parent:

$$
h(r)=\frac{5r+1}{2}\quad(r\equiv1\pmod4),\qquad
h(r)=\frac{5r+1}{4}\quad(r\equiv7\pmod8),
$$

and none when $r\equiv3\pmod8$.

Consequently every chain

$$
r_0\to r_1\to\cdots\to r_n,\qquad
r_{i+1}=\frac{2^{t_{i+1}}r_i-1}{5},
$$

with all $r_i\in W$ and $r_0$ a root is obtained by iterating $h$
backward from $r_n$.

## 3. Reduction to the weight lemma

For a terminal chain of length $n$ ending in $r_n\equiv3\pmod5$, let
$S_n$ be the weight of the first word of $r_n$. The chain length bound
$r_n^4\ge5^n(1+1/r_n)$ follows if

$$
S_n\ge3n-1\qquad(n\ge8).
$$

Proof. The root has top-level k$\ge1$, so the L-B'c branch gives

$$
r_0\ge\frac{2^{S_0+3}-1}{5}.
$$

The chain recurrence gives

$$
2^T r_0=5^n r_n+C_n,\qquad 0<C_n<5^n,
$$

where $T=\sum t_i$ and $S_n=S_0+T$. Therefore

$$
r_n\ge\frac{2^{S_n+3}-2^T-5^{n+1}}{5^{n+1}}.
$$

Using $S_n\ge3n-1$ and $T\le2n$,

$$
r_n\ge\frac{2^{3n+2}-5^{n+1}-2^{n+1}}{5^{n+1}}.
$$

For $n=8$ the right side is greater than $5^{8/4}=25$, and it grows
faster than $5^{n/4}$ afterwards. Thus

$$
r_n^4\ge5^n\ge5^n(1+1/r_n)
$$

for $n\ge8$. The cases $n\le6$ are immediate from the exact minimum
table in `l_ba_atomic_progress.md`, and for $n=7$ the only odd
$r\equiv3\pmod5$ below 23 are 3 and 13; 3 is the empty word and 13 is
a root, so no terminal chain of length 7 has $r_7<23$. $\square$

## 4. Open subproblem

The remaining analytic subproblem is the weight lemma:

$$
S_n\ge3n-1
$$

for every terminal k=0 chain of length $n\ge8$ ending in
$r_n\equiv3\pmod5$. Exact calibration up to $2\cdot10^6$ shows that
the stronger slack inequality

$$
\left\lceil\frac{S+2}{3}\right\rceil-d\ge1
$$

holds for every such $r\ne23$ in that range; this is calibration, not
proof. The finite low-slack list is

$$
23,\ 73,\ 503,\ 54423;\qquad 9,\ 29,\ 21769.
$$

Closing the weight lemma closes L-B'a through the already-proved
threshold-tree and D-invariant reductions.

## 5. Exact Q-factor propagation

For a chain $r_0\to\cdots\to r_n$ define

$$
Q_i=\frac{r_i^5}{5^i(r_i+1)}.
$$

Then

$$
\frac{Q_i}{Q_{i-1}}
=\left(\frac{r_i}{r_{i-1}}\right)^5
\frac{r_{i-1}+1}{5(r_i+1)}.
$$

Using $r_i=(2^{t_i}r_{i-1}-1)/5$, the exact inequalities

$$
\frac{Q_i}{Q_{i-1}}\le\frac{16}{3125}\quad(t_i=1),\qquad
\frac{Q_i}{Q_{i-1}}\le\frac{256}{3125}\quad(t_i=2)
$$

hold for every step. Hence, if $a$ steps have $t=1$ and $b$ steps have
$t=2$,

$$
Q_n\le Q_0\left(\frac{16}{3125}\right)^a
\left(\frac{256}{3125}\right)^b.
$$

The desired chain inequality is $Q_n\ge1$. Therefore it suffices to
prove the root bound

$$
Q_0\ge\left(\frac{3125}{16}\right)^a
\left(\frac{3125}{256}\right)^b.
$$

This is equivalent, up to a bounded factor, to the weight lemma in
Section 4: both require the terminal root weight $S_0$ to be large
enough relative to the forward t-pattern. The Q-factor identity is
exact and is the natural induction carrier for a proof that the
finite low-slack list is exhaustive.

## 6. Forward closure and c=0 slack

**Lemma (W is forward-closed).** If $r\in W$ and a k=0 step

$$
c=\frac{2^t r-1}{5},\qquad t\in\{1,2\},
$$

is defined, then $c\in W$.

Proof. The first C3 word of $c$ is the suffix of the first C3 word of
$r$, so it is nonempty and all its steps are in $\{1,2\}$. If $S$ is
the weight of the first word of $r$, then $S_c=S+t$. From
$r<2^{S+3}$,

$$
c<\frac{2^t\,2^{S+3}}5
=2^{S+t+2}\cdot\frac25<2^{S+t+3}=2^{S_c+3}.
$$

By the exact membership test, $c\in W$. $\square$

The exact slack for the weight lemma is the Section 4 quantity

$$
\varepsilon_2(r)=\left\lceil\frac{S(r)+2}{3}\right\rceil-d(r).
$$

For $r\equiv3\pmod5$,

$$
S\ge3d-1 \iff \varepsilon_2(r)\ge1.
$$

For the recursive closure we also use the auxiliary uniform slack

$$
\varepsilon_0(r)=\left\lceil\frac{S(r)}3\right\rceil-d(r),
$$

which is not by itself equivalent to the weight lemma; a value
$\varepsilon_0=0$ can correspond to either $S=3d-1$ or $S=3d-2$.

Along a k=0 forward step,

$$
\varepsilon_0(c)-\varepsilon_0(r)
=\left\lceil\frac{S+t}{3}\right\rceil-\left\lceil\frac S3\right\rceil-1.
$$

For $t=1$ the difference is $-1$ for every residue of $S$ modulo 3;
for $t=2$ it is $0$ or $-1$. Hence $\varepsilon_0$ is nonincreasing
along every k=0 chain.

**Calibration of the low-slack preimage closure.** The exact
certificate `lb_e0_classification_certificate.txt` (bound $10^7$)
verifies the ten $E_0$ elements, the seventeen 3/4 elements with
$\varepsilon_0\le1$, forward closure, and zero backward violations.
The remaining analytic task is to prove the leaf classification used
in Section 7; the certificate is calibration, not proof.

Note: the objective's sample line `n=8, r=503, S_n=23` does not match
the exact first-C3-word computation; for $r=503$ the first word has
length 19 and weight $S_n=25$. The chain length is still $n=8$ and the
near-critical sample remains $n=7, r=23$.

## 7. E0 reduction: one finite classification closes the lemma

Let

$$
\varepsilon_0(r)=\left\lceil\frac{S(r)}3\right\rceil-d(r).
$$

If $r\equiv3\pmod5$, $d\ge8$, and the weight lemma fails, then
$S\le3d-2$, which implies

$$
\varepsilon_0(r)=\left\lceil\frac S3\right\rceil-d\le0.
$$

Hence it is enough to prove the classification

$$
E_0:=\{\,r\in W:\varepsilon_0(r)\le0\,\}
=\{5,7,9,23,29,71,201,17415,21769,54423\}.
$$

This closes the lemma because the only $r\equiv3\pmod5$ elements of
$E_0$ are $23$ and $54423$; they satisfy $d=7$ and $S=60=3d$
respectively, so neither is a counterexample with $d\ge8$.

The set $E_0$ is forward-closed under every defined k=0 step, and the
only leaves in $E_0$ are the non-3/4 residues

$$
5,\ 7,\ 71,\ 201,\ 17415.
$$

For the recursive reduction:

- if $r\in E_0$ has a k=0 child, the child is a smaller $E_0$ element,
  so $r$ must be one of finitely many h-preimages of $E_0$;
- if $r\in E_0$ is a leaf, its parent has
  $\varepsilon_0\le1$, so the leaf classification reduces to the
  finite 3/4 list
  $$
  \{9,13,23,29,39,73,89,153,183,223,503,629,
  21769,54423,68029,170073,399639\}.
  $$

This is a finite recursive certificate structure, but the leaf
classification is still calibration up to $10^7$, not a proof. The
exact certificate for the ten $E_0$ values was produced with the
membership test in this file's Section 1; it is reproducible and took
under a minute, but is not being counted as an analytic proof step.

## 8. Exact depth inequalities

Let $w$ be the first C3 word of $r\in W$, let $S$ be its weight, and
let $W_i=\sum_{j<i}t_j$ and

$$
A_i=\sum_{j=0}^{i-1}2^{W_j}5^{i-1-j}.
$$

The orbit identity gives

$$
2^{W_i}n_i=5^ir+A_i.
$$

For every ancestor $r_i=n_i$ at depth $i$, membership in $W$ is
equivalent to

$$
5^ir+A_i<2^{S+3}.
$$

Therefore the k=0 depth is

$$
d=\max\{\,i:\ 5^jr+A_j<2^{S+3}\ \text{for all }j\le i\,\},
$$

with the convention that the maximum is taken before the first
violation. If $d<L$, then

$$
5^dr+A_d<2^{S+3}\le5^{d+1}r+A_{d+1}.
$$

These inequalities, together with the bounds

$$
A_i\le5^i-4^i,
$$

are the exact arithmetic form of the remaining leaf classification.

## 9. Update 2026-08-06: E0 reduction status

The E0 classification remains open. The current reduction chain is recorded
in `e0_margin_automaton.md`; the exact remaining sublemma is:

> **F1-L.** If `r0 in W` is a leaf (no k=0 child) with
> `F = r0*5^(S/3)/(8*2^S) < 1`, then
> `r0 in {1,5,7,37,71,201,17415}`.

Known analytic steps:

- `M(c)=2^t M(p)+4c+1` and `m_{i+1}=5m_i+2^{-(S_i+3)}`;
- E0 classification reduces to five leaves;
- `d <= S_R` for depth-0 top ancestors;
- `eps0 <= 0 => F < 1` and `F > 1 => eps0 >= 1`;
- `F` decreases along child steps, so `F<1` is downward closed;
- certificates verify the seven `F<1` leaves up to `10^7` and the
  `F<1` top table.

No enumeration is used as a proof step in this document.

## 10. Update 2026-08-07: exact F-window lemmas

The following analytic steps are now recorded in
`e0_margin_automaton.md` Section 17:

- For every W element with depth `d >= 1`,
  `r > 2^(S+3)/5^(d+1) - 1`;
- `F < 1` implies `S <= 3d+3`;
- `F < 3.05` implies `S <= 3d+5`;
- consequently, a hypothetical F<1 leaf with `S >= 64` has
  `d >= 21`, `S_R in [d, 2d+3]`, and the unique root candidate is
  constrained by the prefix congruence modulo `5^(d+1)`.

The finite closure certificate `verify_e0_fa_closure.py 60000000`
(certificate file `e0_fa_closure_certificate.txt`) checks these
window inequalities and the F1/top/near tables up to `6*10^7`.
It is a certificate, not a proof.  F1-L remains open; the exact
unresolved subcase is the exclusion of the `S >= 64` leaf in
Corollary 17.4.

New analytic steps in `e0_margin_automaton.md` Sections 17--18:

- Proposition 17.8 removes the `eps0 <= 0` hypothesis from the
  weight lower bound: every W element with `r >= 5` and depth
  `d >= 1` satisfies `S > (d+1) log_2 5 - 3`.
- Corollary 17.9 gives the F<1 depth interval
  `ceil((S-3)/3) <= d < (S+3)/log_2 5 - 1` for `S >= 64`.
- Proposition 18.4 proves that a W element `s >= 5^5` with
  `F(s) < 3.05` must have `S(s) >= 31`.
- Corollary 18.5 proves the first part of the residue-class gap:
  if `r < s` are W, `r == s mod 5^5`, and both have `F < 3.05`,
  then `S(s) >= 31`; when `S(s) <= 35`, the class index
  `q = (s-r)/5^5` is at most 1.
- Proposition 18.7 sharpens the same bound for `F < 1`: a W element
  `s >= 5^5` with `F(s) < 1` has `S(s) >= 39`, and `S(s) <= 42`
  forces `q <= 1`.
- Propositions 18.10 and 18.11 reduce the g-chain length bounds to
  leaf-F lower bounds plus exact checks of the `7` and `17415`
  forward orbit segments: `F(183) > 1`, `F(229) > 3.05`,
  `F(425183) > 3.05`.  These reductions are analytic; the leaf-F
  lower bounds remain open.
- Proposition 18.13 records the conditional closure: if F1-L holds,
  then the F<1 halves of both global propositions follow from the
  seven known leaves' first seven forward orbit values (a finite
  exact check, not an unbounded scan).

The remaining open subcases for the uniqueness part are
`S <= 35, q = 1` and `S >= 36, q >= 2`; these still need W
membership or 2-adic realizability.  For `F < 1`, the `q = 1`
subcase is further reduced by the open small-value weight bound
(candidate lemma 18.9): every W element below `2*5^5` has
`S <= 32`.
