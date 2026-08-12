import Domination

/-!
# G5 delta-record grouping certificate

For P in the ranges used by 52.21.2bis, the fractional part
delta(P) = ceil(P*log2 5) - P*log2 5 has the records
delta(31) < delta(P) for 9 <= P < 59 and
delta(59) < delta(P) for 59 <= P < 205.  The comparisons
are certified by exact power inequalities, not by real
arithmetic. -/

namespace StringFlow

def tCeilTable : Nat -> Nat
  | 9 => 21
  | 10 => 24
  | 11 => 26
  | 12 => 28
  | 13 => 31
  | 14 => 33
  | 15 => 35
  | 16 => 38
  | 17 => 40
  | 18 => 42
  | 19 => 45
  | 20 => 47
  | 21 => 49
  | 22 => 52
  | 23 => 54
  | 24 => 56
  | 25 => 59
  | 26 => 61
  | 27 => 63
  | 28 => 66
  | 29 => 68
  | 30 => 70
  | 31 => 72
  | 32 => 75
  | 33 => 77
  | 34 => 79
  | 35 => 82
  | 36 => 84
  | 37 => 86
  | 38 => 89
  | 39 => 91
  | 40 => 93
  | 41 => 96
  | 42 => 98
  | 43 => 100
  | 44 => 103
  | 45 => 105
  | 46 => 107
  | 47 => 110
  | 48 => 112
  | 49 => 114
  | 50 => 117
  | 51 => 119
  | 52 => 121
  | 53 => 124
  | 54 => 126
  | 55 => 128
  | 56 => 131
  | 57 => 133
  | 58 => 135
  | 59 => 137
  | 60 => 140
  | 61 => 142
  | 62 => 144
  | 63 => 147
  | 64 => 149
  | 65 => 151
  | 66 => 154
  | 67 => 156
  | 68 => 158
  | 69 => 161
  | 70 => 163
  | 71 => 165
  | 72 => 168
  | 73 => 170
  | 74 => 172
  | 75 => 175
  | 76 => 177
  | 77 => 179
  | 78 => 182
  | 79 => 184
  | 80 => 186
  | 81 => 189
  | 82 => 191
  | 83 => 193
  | 84 => 196
  | 85 => 198
  | 86 => 200
  | 87 => 203
  | 88 => 205
  | 89 => 207
  | 90 => 209
  | 91 => 212
  | 92 => 214
  | 93 => 216
  | 94 => 219
  | 95 => 221
  | 96 => 223
  | 97 => 226
  | 98 => 228
  | 99 => 230
  | 100 => 233
  | 101 => 235
  | 102 => 237
  | 103 => 240
  | 104 => 242
  | 105 => 244
  | 106 => 247
  | 107 => 249
  | 108 => 251
  | 109 => 254
  | 110 => 256
  | 111 => 258
  | 112 => 261
  | 113 => 263
  | 114 => 265
  | 115 => 268
  | 116 => 270
  | 117 => 272
  | 118 => 274
  | 119 => 277
  | 120 => 279
  | 121 => 281
  | 122 => 284
  | 123 => 286
  | 124 => 288
  | 125 => 291
  | 126 => 293
  | 127 => 295
  | 128 => 298
  | 129 => 300
  | 130 => 302
  | 131 => 305
  | 132 => 307
  | 133 => 309
  | 134 => 312
  | 135 => 314
  | 136 => 316
  | 137 => 319
  | 138 => 321
  | 139 => 323
  | 140 => 326
  | 141 => 328
  | 142 => 330
  | 143 => 333
  | 144 => 335
  | 145 => 337
  | 146 => 340
  | 147 => 342
  | 148 => 344
  | 149 => 346
  | 150 => 349
  | 151 => 351
  | 152 => 353
  | 153 => 356
  | 154 => 358
  | 155 => 360
  | 156 => 363
  | 157 => 365
  | 158 => 367
  | 159 => 370
  | 160 => 372
  | 161 => 374
  | 162 => 377
  | 163 => 379
  | 164 => 381
  | 165 => 384
  | 166 => 386
  | 167 => 388
  | 168 => 391
  | 169 => 393
  | 170 => 395
  | 171 => 398
  | 172 => 400
  | 173 => 402
  | 174 => 405
  | 175 => 407
  | 176 => 409
  | 177 => 411
  | 178 => 414
  | 179 => 416
  | 180 => 418
  | 181 => 421
  | 182 => 423
  | 183 => 425
  | 184 => 428
  | 185 => 430
  | 186 => 432
  | 187 => 435
  | 188 => 437
  | 189 => 439
  | 190 => 442
  | 191 => 444
  | 192 => 446
  | 193 => 449
  | 194 => 451
  | 195 => 453
  | 196 => 456
  | 197 => 458
  | 198 => 460
  | 199 => 463
  | 200 => 465
  | 201 => 467
  | 202 => 470
  | 203 => 472
  | 204 => 474
  | _ => 0

/-- The tabulated `ceil(P * log2 5)` used by the stage certificates.
Values above the table are left as `0`; the certificate ranges only
use `P < 205`. -/
def tCeil : Nat -> Nat := fun P =>
  if P <= 204 then tCeilTable P else 0

theorem tCeil_of_le (P : Nat) (h : P <= 204) : tCeil P = tCeilTable P := by
  simp [tCeil, h]

theorem tCeil_large (P : Nat) (h : 205 <= P) : tCeil P = 0 := by
  unfold tCeil
  by_cases hle : P ≤ 204
  · omega
  · simp [hle]

def record31OK (P : Nat) : Bool :=
  if P <= 31 then decide (5^(31 - P) >= 2^(tCeil 31 - tCeil P))
  else decide (2^(tCeil P - tCeil 31) >= 5^(P - 31))

def record31Prop (P : Nat) : Prop :=
  if P <= 31 then 5^(31 - P) >= 2^(tCeil 31 - tCeil P)
  else 2^(tCeil P - tCeil 31) >= 5^(P - 31)

theorem record31OK_eq (P : Nat) : record31OK P = true <-> record31Prop P := by
  by_cases h : P <= 31 <;> simp [record31OK, record31Prop, h, decide_eq_true_eq]

def record59OK (P : Nat) : Bool :=
  if P <= 59 then decide (5^(59 - P) >= 2^(tCeil 59 - tCeil P))
  else decide (2^(tCeil P - tCeil 59) >= 5^(P - 59))

def record59Prop (P : Nat) : Prop :=
  if P <= 59 then 5^(59 - P) >= 2^(tCeil 59 - tCeil P)
  else 2^(tCeil P - tCeil 59) >= 5^(P - 59)

theorem record59OK_eq (P : Nat) : record59OK P = true <-> record59Prop P := by
  by_cases h : P <= 59 <;> simp [record59OK, record59Prop, h, decide_eq_true_eq]

theorem delta_record31_check : allInRange 9 59 record31OK = true := by
  native_decide

theorem delta_record59_check : allInRange 59 205 record59OK = true := by
  native_decide

theorem delta_record31 (P : Nat) (hP9 : 9 <= P) (hP59 : P < 59) :
    record31Prop P := by
  have hOK := allInRange_spec 9 59 record31OK delta_record31_check P hP9 hP59
  exact (record31OK_eq P).mp hOK

theorem delta_record59 (P : Nat) (hP59 : 59 <= P) (hP205 : P < 205) :
    record59Prop P := by
  have hOK := allInRange_spec 59 205 record59OK delta_record59_check P hP59 hP205
  exact (record59OK_eq P).mp hOK

/-- `5^P < 2^tCeil P` on the small range `9 <= P < 31`. -/
def tCeilPowSmallOK : Bool :=
  allInRange 9 31 (fun P => decide (5 ^ P < 2 ^ tCeil P))

theorem tCeil_pow_small_check : tCeilPowSmallOK = true := by
  native_decide

theorem tCeil_pow_small (P : Nat) (hP9 : 9 <= P) (hP31 : P < 31) :
    5 ^ P < 2 ^ tCeil P := by
  have h := allInRange_spec 9 31 (fun P => decide (5 ^ P < 2 ^ tCeil P))
    tCeil_pow_small_check P hP9 hP31
  exact of_decide_eq_true h

/-- `tCeil` is monotone from `31` on the certified range. -/
def tCeilMono31OK : Bool :=
  allInRange 31 205 (fun P => decide (tCeil 31 <= tCeil P))

theorem tCeil_mono31_check : tCeilMono31OK = true := by
  native_decide

theorem tCeil_mono31 (P : Nat) (hP31 : 31 <= P) (hP205 : P < 205) :
    tCeil 31 <= tCeil P := by
  have h := allInRange_spec 31 205 (fun P => decide (tCeil 31 <= tCeil P))
    tCeil_mono31_check P hP31 hP205
  exact of_decide_eq_true h

/-- `tCeil` is monotone from `59` on the certified range. -/
def tCeilMono59OK : Bool :=
  allInRange 59 205 (fun P => decide (tCeil 59 <= tCeil P))

theorem tCeil_mono59_check : tCeilMono59OK = true := by
  native_decide

theorem tCeil_mono59 (P : Nat) (hP59 : 59 <= P) (hP205 : P < 205) :
    tCeil 59 <= tCeil P := by
  have h := allInRange_spec 59 205 (fun P => decide (tCeil 59 <= tCeil P))
    tCeil_mono59_check P hP59 hP205
  exact of_decide_eq_true h

/-- The two base power inequalities at `P = 31` and `P = 59`. -/
def tCeilPowBaseOK : Bool :=
  decide (5 ^ 31 < 2 ^ tCeil 31) && decide (5 ^ 59 < 2 ^ tCeil 59)

theorem tCeil_pow_base_check : tCeilPowBaseOK = true := by
  native_decide

theorem tCeil_pow_base31 : 5 ^ 31 < 2 ^ tCeil 31 := by
  have h := tCeil_pow_base_check
  simp [tCeilPowBaseOK] at h
  exact h.1

theorem tCeil_pow_base59 : 5 ^ 59 < 2 ^ tCeil 59 := by
  have h := tCeil_pow_base_check
  simp [tCeilPowBaseOK] at h
  exact h.2

/-- Multiply the base at `31` with the G5' record on `[31,59)`. -/
theorem tCeil_pow_lt_of_record31
    (P : Nat) (hP31 : 31 <= P)
    (hmono : tCeil 31 <= tCeil P)
    (hrec : 5 ^ (P - 31) <= 2 ^ (tCeil P - tCeil 31)) :
    5 ^ P < 2 ^ tCeil P := by
  have hPsub : P = 31 + (P - 31) := by
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hP31).symm
  have hTsub : tCeil P = tCeil 31 + (tCeil P - tCeil 31) :=
    by simpa [Nat.add_comm] using (Nat.sub_add_cancel hmono).symm
  have hdpos : 0 < 2 ^ (tCeil P - tCeil 31) := Nat.pow_pos (by decide)
  have hmulbase : 5 ^ 31 * 2 ^ (tCeil P - tCeil 31) <
      2 ^ tCeil 31 * 2 ^ (tCeil P - tCeil 31) :=
    Nat.mul_lt_mul_of_pos_right tCeil_pow_base31 hdpos
  have hrec' : 5 ^ 31 * 5 ^ (P - 31) <=
      5 ^ 31 * 2 ^ (tCeil P - tCeil 31) :=
    Nat.mul_le_mul_left (5 ^ 31) hrec
  have hlt : 5 ^ 31 * 5 ^ (P - 31) <
      2 ^ tCeil 31 * 2 ^ (tCeil P - tCeil 31) :=
    Nat.lt_of_le_of_lt hrec' hmulbase
  have h5 : 5 ^ P = 5 ^ 31 * 5 ^ (P - 31) := by
    rw [hPsub, Nat.pow_add]
    simp
  have h2 : 2 ^ tCeil P = 2 ^ tCeil 31 * 2 ^ (tCeil P - tCeil 31) := by
    rw [hTsub, Nat.pow_add]
    simp
  rwa [h5, h2]

/-- Multiply the base at `59` with the G5' record on `[59,205)`. -/
theorem tCeil_pow_lt_of_record59
    (P : Nat) (hP59 : 59 <= P)
    (hmono : tCeil 59 <= tCeil P)
    (hrec : 5 ^ (P - 59) <= 2 ^ (tCeil P - tCeil 59)) :
    5 ^ P < 2 ^ tCeil P := by
  have hPsub : P = 59 + (P - 59) := by
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hP59).symm
  have hTsub : tCeil P = tCeil 59 + (tCeil P - tCeil 59) :=
    by simpa [Nat.add_comm] using (Nat.sub_add_cancel hmono).symm
  have hdpos : 0 < 2 ^ (tCeil P - tCeil 59) := Nat.pow_pos (by decide)
  have hmulbase : 5 ^ 59 * 2 ^ (tCeil P - tCeil 59) <
      2 ^ tCeil 59 * 2 ^ (tCeil P - tCeil 59) :=
    Nat.mul_lt_mul_of_pos_right tCeil_pow_base59 hdpos
  have hrec' : 5 ^ 59 * 5 ^ (P - 59) <=
      5 ^ 59 * 2 ^ (tCeil P - tCeil 59) :=
    Nat.mul_le_mul_left (5 ^ 59) hrec
  have hlt : 5 ^ 59 * 5 ^ (P - 59) <
      2 ^ tCeil 59 * 2 ^ (tCeil P - tCeil 59) :=
    Nat.lt_of_le_of_lt hrec' hmulbase
  have h5 : 5 ^ P = 5 ^ 59 * 5 ^ (P - 59) := by
    rw [hPsub, Nat.pow_add]
    simp
  have h2 : 2 ^ tCeil P = 2 ^ tCeil 59 * 2 ^ (tCeil P - tCeil 59) := by
    rw [hTsub, Nat.pow_add]
    simp
  rwa [h5, h2]

/-- `5^P < 2^tCeil P` for the phase-2 range `9 <= P < 205`. -/
theorem tCeil_pow_lt (P : Nat) (hP9 : 9 <= P) (hP205 : P < 205) :
    5 ^ P < 2 ^ tCeil P := by
  by_cases hP31 : P < 31
  · exact tCeil_pow_small P hP9 hP31
  · have h31 : 31 <= P := by omega
    by_cases hP59 : P < 59
    · have hrec := delta_record31 P hP9 hP59
      have hrec' : 5 ^ (P - 31) <= 2 ^ (tCeil P - tCeil 31) := by
        by_cases hle31 : P <= 31
        · have hP31eq : P = 31 := by omega
          subst P
          simp [record31Prop] at hrec
          simp
        · simpa [record31Prop, hle31] using hrec
      exact tCeil_pow_lt_of_record31 P h31 (tCeil_mono31 P h31 hP205) hrec'
    · have h59 : 59 <= P := by omega
      have hrec := delta_record59 P h59 hP205
      have hrec' : 5 ^ (P - 59) <= 2 ^ (tCeil P - tCeil 59) := by
        by_cases hle59 : P <= 59
        · have hP59eq : P = 59 := by omega
          subst P
          simp [record59Prop] at hrec
          simp
        · simpa [record59Prop, hle59] using hrec
      exact tCeil_pow_lt_of_record59 P h59 (tCeil_mono59 P h59 hP205) hrec'

/-- The tabulated ceiling is minimal: `2^(tCeil P - 1) <= 5^P` on the
certified small range. -/
def tCeilMinimalOK : Bool :=
  allInRange 9 205 (fun P => decide (2 ^ (tCeil P - 1) ≤ 5 ^ P))

theorem tCeil_minimal_check : tCeilMinimalOK = true := by
  native_decide

/-- `tCeil` is the minimal exponent with `5^P < 2^T` on
`9 <= P < 205`. -/
theorem tCeil_minimal (P T : Nat) (hP9 : 9 <= P) (hP205 : P < 205)
    (hT : T < tCeil P) : 2 ^ T ≤ 5 ^ P := by
  have hAll := allInRange_spec 9 205
    (fun P => decide (2 ^ (tCeil P - 1) ≤ 5 ^ P))
    tCeil_minimal_check P hP9 hP205
  have hle : 2 ^ (tCeil P - 1) ≤ 5 ^ P := of_decide_eq_true hAll
  have hTle : T ≤ tCeil P - 1 := by omega
  exact Nat.le_trans (Nat.pow_le_pow_right (show 0 < 2 by decide) hTle) hle

/-- `5^P < 2^T` forces `tCeil P <= T` on the certified range. -/
theorem tCeil_le_of_pow_lt (P T : Nat) (hP9 : 9 <= P) (hP205 : P < 205)
    (h : 5 ^ P < 2 ^ T) : tCeil P ≤ T := by
  by_cases hTlt : T < tCeil P
  · have hle := tCeil_minimal P T hP9 hP205 hTlt
    omega
  · omega

/-- The upper half of the ceiling identity: `2^T < 2 * 5^P` forces
`T <= tCeil P` on the certified range. -/
theorem tCeil_ge_of_pow_two_lt (P T : Nat) (hP9 : 9 <= P) (hP205 : P < 205)
    (h : 2 ^ T < 2 * 5 ^ P) : T ≤ tCeil P := by
  by_cases hTle : T ≤ tCeil P
  · exact hTle
  · have hTge : tCeil P + 1 ≤ T := by omega
    have hpow := Nat.pow_le_pow_right (show 0 < 2 by decide) hTge
    have hlt2 : 2 * 5 ^ P < 2 ^ (tCeil P + 1) := by
      have hmul := Nat.mul_lt_mul_of_pos_right (tCeil_pow_lt P hP9 hP205)
        (show 0 < 2 by decide)
      rw [← Nat.pow_succ] at hmul
      simpa [Nat.mul_comm] using hmul
    omega

/-- The tabulated ceiling is at least `2` on the certified range. -/
def tCeilGeTwoOK : Bool :=
  allInRange 9 205 (fun P => decide (2 ≤ tCeil P))

theorem tCeil_ge_two_check : tCeilGeTwoOK = true := by
  native_decide

theorem tCeil_ge_two (P : Nat) (hP9 : 9 <= P) (hP205 : P < 205) :
    2 ≤ tCeil P := by
  have h := allInRange_spec 9 205
    (fun P => decide (2 ≤ tCeil P)) tCeil_ge_two_check P hP9 hP205
  exact of_decide_eq_true h

/-- `2^k` is even for `k > 0`. -/
theorem pow_even_mod_two (k : Nat) (hk : 0 < k) : (2 ^ k) % 2 = 0 := by
  have hsplit : k = (k - 1) + 1 := by omega
  rw [hsplit, Nat.pow_succ]
  simp

/-- `5^P` is odd. -/
theorem five_odd_mod_two (P : Nat) : (5 ^ P) % 2 = 1 := by
  induction P with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod]
      rw [ih]

/-- The upper half of the ceiling identity: `2^tCeil P < 2 * 5^P`
on the certified range. -/
theorem tCeil_pow_two_lt (P : Nat) (hP9 : 9 <= P) (hP205 : P < 205) :
    2 ^ tCeil P < 2 * 5 ^ P := by
  have hTge2 := tCeil_ge_two P hP9 hP205
  have hTpos : 0 < tCeil P := by omega
  have hTlt : tCeil P - 1 < tCeil P :=
    Nat.sub_lt hTpos (by decide : 0 < 1)
  have hmin : 2 ^ (tCeil P - 1) ≤ 5 ^ P :=
    tCeil_minimal P (tCeil P - 1) hP9 hP205 hTlt
  have hk : 0 < tCeil P - 1 := by omega
  have hmod2 := pow_even_mod_two (tCeil P - 1) hk
  have hmod5 := five_odd_mod_two P
  have hne2 : Not (2 ^ (tCeil P - 1) = 5 ^ P) := by
    intro heq
    rw [heq] at hmod2
    rw [hmod5] at hmod2
    have hz : (1 : Nat) = 0 := hmod2
    exact (Nat.succ_ne_zero 0) hz
  have hstrict : 2 ^ (tCeil P - 1) < 5 ^ P :=
    Nat.lt_of_le_of_ne hmin hne2
  have hmul : 2 * 2 ^ (tCeil P - 1) < 2 * 5 ^ P :=
    Nat.mul_lt_mul_of_pos_left hstrict (by decide : 0 < 2)
  have hrewrite : 2 ^ tCeil P = 2 * 2 ^ (tCeil P - 1) := by
    have hsplit : tCeil P = (tCeil P - 1) + 1 := by omega
    calc
      2 ^ tCeil P = 2 ^ (tCeil P - 1 + 1) := by
        conv =>
          lhs
          rw [hsplit]
      _ = 2 ^ (tCeil P - 1) * 2 := by rw [Nat.pow_succ]
      _ = 2 * 2 ^ (tCeil P - 1) := by
        exact Nat.mul_comm (2 ^ (tCeil P - 1)) 2
  exact (by rw [hrewrite]; exact hmul)

end StringFlow
