import CycleBridge
import RealOrbitLocalLemma

namespace StringFlow

namespace CycleBridge

/-- Decomposition of a closed QB-8 word into the blocks used by the
PMI summation.  A block consists of a reset step into `headDepth r`,
the following rise suffix, and the C3 separator weight to the next
head. -/
structure CycleBlockDecomposition (m S P : Nat) (w : List Nat) where
  blockCount : Nat
  headDepth : Nat → Nat
  resetWeight : Nat → Nat
  suffixWord : Nat → List Nat
  c3Weight : Nat → Nat
  hhead0 : headDepth 0 = 0
  hhead_pos : ∀ r, r < blockCount → 1 ≤ headDepth r
  hhead_lt : ∀ r, r < blockCount → headDepth r < P
  hreset_eq : ∀ r, r < blockCount →
    resetWeight r = w.getI (headDepth r - 1)
  hreset_ge3 : ∀ r, r < blockCount → 3 ≤ resetWeight r
  hsuffix_one_two : ∀ r, r < blockCount →
     ∀ t ∈ suffixWord r, t = 1 ∨ t = 2
  hsuffix_exact : ∀ r, r < blockCount →
    ∀ k, k < (suffixWord r).length →
      twoValuation
        (5 * riseRun (StringFlow.Word.wordOrbit (w.take (headDepth r)) m)
          ((suffixWord r).take k) + 1)
      = (suffixWord r).getI k
  hc3_weight : ∀ r, r < blockCount → 3 ≤ c3Weight r
  hnext : ∀ r, r < blockCount →
    (if r + 1 < blockCount then headDepth (r + 1) else P) =
      headDepth r + resetWeight r + (suffixWord r).length + c3Weight r
  hweight : S =
    ((List.range blockCount).map
      (fun r => resetWeight r + StringFlow.wordWeight (suffixWord r) +
        c3Weight r)).sum

/-- Correct cyclic decomposition by rise runs.  The block head is the
state after a rise run; `resetWeight r` is the last rise step before
that head.  From the head, a nonempty C3 chain `c3Word r` leads to the
start of the next rise run, and `suffixWord r` is that rise run.  Its
last step is `resetWeight (r + 1)`.  The block occupies the C3 chain
followed by the rise suffix, so `hnext` adds both list lengths. -/
structure CycleRiseBlockDecomposition (m S P : Nat) (w : List Nat) where
  blockCount : Nat
  headDepth : Nat → Nat
  resetWeight : Nat → Nat
  c3Word : Nat → List Nat
  suffixWord : Nat → List Nat
  hperiod : w.length = P
  hclosed : StringFlow.Word.wordOrbit w m = m
  hhead_pos : ∀ r, r < blockCount → 1 ≤ headDepth r
  hhead_lt : ∀ r, r < blockCount → headDepth r < P
  hreset_eq : ∀ r, r < blockCount →
    resetWeight r = w.getI (headDepth r - 1)
  hreset_one_two : ∀ r, r < blockCount →
    resetWeight r = 1 ∨ resetWeight r = 2
  hc3_nonempty : ∀ r, r < blockCount → c3Word r ≠ []
  hc3_entries : ∀ r, r < blockCount →
    ∀ t ∈ c3Word r, 3 ≤ t
  hc3_segment : ∀ r, r < blockCount →
    ∀ k, k < (c3Word r).length →
      (c3Word r).getI k = w.getI (headDepth r + k)
  hc3_exact : ∀ r, r < blockCount →
    ∀ k, k < (c3Word r).length →
      twoValuation
        (5 * StringFlow.Word.wordOrbit
          (w.take (headDepth r + k)) m + 1) =
        (c3Word r).getI k
  hsuffix_one_two : ∀ r, r < blockCount →
     ∀ t ∈ suffixWord r, t = 1 ∨ t = 2
  hsuffix_segment : ∀ r, r < blockCount →
    ∀ k, k < (suffixWord r).length →
      (suffixWord r).getI k =
        w.getI ((headDepth r + (c3Word r).length + k) % P)
  hsuffix_exact : ∀ r, r < blockCount →
    ∀ k, k < (suffixWord r).length →
      twoValuation
        (5 * riseRun
          (StringFlow.Word.wordOrbit
            (w.take (headDepth r + (c3Word r).length)) m)
          ((suffixWord r).take k) + 1)
      = (suffixWord r).getI k
  hnext : ∀ r, r < blockCount →
    (if r + 1 < blockCount then headDepth (r + 1) else headDepth 0 + P) =
      headDepth r + (c3Word r).length + (suffixWord r).length
  hweight : S =
    ((List.range blockCount).map
      (fun r => StringFlow.wordWeight (c3Word r) +
        StringFlow.wordWeight (suffixWord r))).sum

/-- Integer-valued cyclic block endpoint used for telescoping. -/
def cycleRiseNextPrefixZ {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (i : Nat) : Int :=
  if i < d.blockCount then (d.headDepth i : Int)
  else (d.headDepth 0 : Int) + (P : Int)

/-- Integer telescoping identity for cyclic rise blocks:
`Σ(c3Length r + suffixLength r) = P`. -/
theorem cycleRiseBlockPeriodSum_int
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    (Finset.range d.blockCount).sum
        (fun r => ((d.c3Word r).length + (d.suffixWord r).length : Int)) =
      (P : Int) := by
  let f : Nat → Int := cycleRiseNextPrefixZ d
  have hdiff : ∀ r ∈ Finset.range d.blockCount,
      f (r + 1) - f r =
        ((d.c3Word r).length + (d.suffixWord r).length : Int) := by
    intro r hr
    have hrlt : r < d.blockCount := Finset.mem_range.mp hr
    have hnext := d.hnext r hrlt
    have hnextZ : f (r + 1) =
        (d.headDepth r : Int) +
          ((d.c3Word r).length + (d.suffixWord r).length : Int) := by
      dsimp [f, cycleRiseNextPrefixZ]
      have hcast : ((if r + 1 < d.blockCount then d.headDepth (r + 1)
          else d.headDepth 0 + P : Nat) : Int) =
          ((d.headDepth r + (d.c3Word r).length +
            (d.suffixWord r).length : Nat) : Int) := by
        exact_mod_cast hnext
      simpa [Nat.add_assoc] using hcast
    have hprevZ : f r = (d.headDepth r : Int) := by
      dsimp [f, cycleRiseNextPrefixZ]
      simp [hrlt]
    rw [hnextZ, hprevZ]
    ring
  have hsumdiff : (Finset.range d.blockCount).sum
        (fun r => f (r + 1) - f r) =
    (Finset.range d.blockCount).sum
        (fun r => ((d.c3Word r).length + (d.suffixWord r).length : Int)) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    exact hdiff r hr
  calc
    (Finset.range d.blockCount).sum
        (fun r => ((d.c3Word r).length + (d.suffixWord r).length : Int)) =
      (Finset.range d.blockCount).sum
        (fun r => f (r + 1) - f r) := hsumdiff.symm
    _ = f d.blockCount - f 0 := Finset.sum_range_sub f d.blockCount
    _ = (P : Int) := by
        dsimp [f, cycleRiseNextPrefixZ]
        simp [hpos]

/-- Natural-number form of the cyclic rise block period identity. -/
theorem cycleRiseBlockPeriodSum
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    P =
      (Finset.range d.blockCount).sum
        (fun r => (d.c3Word r).length + (d.suffixWord r).length) := by
  have h := cycleRiseBlockPeriodSum_int d hpos
  exact_mod_cast h.symm

/-- List-sum form of the cyclic rise block period identity. -/
theorem cycleRiseBlockPeriodSum_list
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    P =
      ((List.range d.blockCount).map
        (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum := by
  have hf := cycleRiseBlockPeriodSum d hpos
  have hlist : ((List.range d.blockCount).toFinset).sum
      (fun r => (d.c3Word r).length + (d.suffixWord r).length) =
      ((List.range d.blockCount).map
        (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum :=
    List.sum_toFinset
      (fun r => (d.c3Word r).length + (d.suffixWord r).length)
      (List.nodup_range)
  rw [List.toFinset_range] at hlist
  rw [← hlist]
  exact hf

/-- Every block occupies at least one word position, so the block count
is bounded by the period. -/
theorem cycleRiseBlockCount_le_P
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    d.blockCount ≤ P := by
  have hP := cycleRiseBlockPeriodSum_list d hpos
  have hsumle : ((List.range d.blockCount).map (fun _ => 1)).sum ≤
      ((List.range d.blockCount).map
        (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum := by
    refine List.sum_le_sum ?_
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    have hnonempty : d.c3Word r ≠ [] := d.hc3_nonempty r hrlt
    have hlen : 1 ≤ (d.c3Word r).length :=
      List.length_pos_iff.mpr hnonempty
    omega
  have hconst : ((List.range d.blockCount).map (fun _ => 1)).sum =
      d.blockCount := by
    rw [List.map_const']
    rw [List.sum_replicate]
    simp
  calc
    d.blockCount =
        ((List.range d.blockCount).map (fun _ => 1)).sum := hconst.symm
    _ ≤ ((List.range d.blockCount).map
        (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum := hsumle
    _ = P := hP.symm

/-- Rank of the head of a cyclic rise block. -/
def cycleRiseBlockHeadRank {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  twoValuation
    (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m + 1)

/-- The state immediately after the C3 chain of a cyclic rise block.
The rise suffix starts at this state. -/
def cycleRiseBlockC3TailState {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  StringFlow.Word.wordOrbit
    (w.take (d.headDepth r + (d.c3Word r).length)) m

/-- The state after the block's C3 chain is the concrete prefix orbit
at `headDepth r + c3Length r`. -/
lemma cycleRiseBlockC3TailState_eq_prefix
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (_hr : r < d.blockCount) :
    cycleRiseBlockC3TailState d r =
      StringFlow.Word.wordOrbit
        (w.take (d.headDepth r + (d.c3Word r).length)) m :=
  rfl

/-- Total positive charge along the suffix of a cyclic rise block. -/
def cycleRiseBlockCharge {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  riseChargeSum
    (cycleRiseBlockC3TailState d r)
    (d.suffixWord r)

/-- Local balance for one cyclic rise block. -/
theorem cycleRiseBlockBalance
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    2 * riseCountTwo (d.suffixWord r) ≤
      twoValuation (cycleRiseBlockC3TailState d r + 1) +
        cycleRiseBlockCharge d r := by
  have hexact : ∀ k, k < (d.suffixWord r).length →
      twoValuation
        (5 * riseRun (cycleRiseBlockC3TailState d r)
          ((d.suffixWord r).take k) + 1) =
        (d.suffixWord r).getI k := by
    intro k hk
    simpa [cycleRiseBlockC3TailState] using d.hsuffix_exact r hr k hk
  exact rise_block_balance
    (cycleRiseBlockC3TailState d r)
    (d.suffixWord r)
    (d.hsuffix_one_two r hr)
    hexact

/-- Total `t=2` steps in a cyclic rise decomposition. -/
def cycleRiseBlockH2Sum {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) : Nat :=
  ((List.range d.blockCount).map
    (fun r => riseCountTwo (d.suffixWord r))).sum

/-- Rank of the state immediately after a block's C3 chain. -/
def cycleRiseBlockTailRank {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  twoValuation (cycleRiseBlockC3TailState d r + 1)

/-- The abstract endpoint of a block's rise suffix. -/
def cycleRiseBlockSuffixEndpointState {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  riseRun (cycleRiseBlockC3TailState d r) (d.suffixWord r)

/-- Rank of the abstract endpoint of a block's rise suffix. -/
def cycleRiseBlockSuffixEndpointRank {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  twoValuation (cycleRiseBlockSuffixEndpointState d r + 1)

/-- Depth of the next cyclic block head, allowing the final block to
wrap by one period. -/
def cycleRiseBlockNextHeadDepth {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  if r + 1 < d.blockCount then d.headDepth (r + 1)
  else d.headDepth 0 + P

/-- Concrete state at the next cyclic block head. -/
def cycleRiseBlockNextHeadState {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  StringFlow.Word.wordOrbit
    (w.take (cycleRiseBlockNextHeadDepth d r)) m

/-- For a non-wrapping block, the recorded suffix is the actual dropped
word segment after the C3 chain. -/
lemma cycleRiseBlockSuffixWord_eq_drop_nonwrap
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount) :
    d.suffixWord r =
      (w.drop (d.headDepth r + (d.c3Word r).length)).take
        (d.suffixWord r).length := by
  let start := d.headDepth r + (d.c3Word r).length
  let len := (d.suffixWord r).length
  have hsum := d.hnext r hr
  have hnextlt : d.headDepth (r + 1) < P := d.hhead_lt (r + 1) hrnext
  have hnext : start + len = d.headDepth (r + 1) := by
    dsimp [start, len]
    have hcast : (d.headDepth (r + 1) : Nat) =
        d.headDepth r + (d.c3Word r).length + (d.suffixWord r).length := by
      simpa [hrnext, Nat.add_assoc] using hsum
    exact hcast.symm
  have hlen : len ≤ (w.drop start).length := by
    rw [List.length_drop, d.hperiod]
    have hnextlt' : start + len < P := by
      rw [hnext]
      exact hnextlt
    omega
  refine List.ext_getElem ?_ ?_
  · rw [List.length_take_of_le hlen]
  · intro k hk1 hk2
    have hk : k < len := by
      simpa [len] using hk1
    have hseg := d.hsuffix_segment r hr k hk
    have hkdrop : k < (w.drop start).length := by
      have hklen : k < len := by
        rw [List.length_take_of_le hlen] at hk2
        exact hk2
      rw [List.length_drop]
      have hlen' : len ≤ w.length - start := by
        simpa [List.length_drop] using hlen
      omega
    have hstartklt : start + k < P := by
      have hspan : start + len < P := by
        rw [hnext]
        exact hnextlt
      omega
    have hmod : (start + k) % P = start + k :=
      Nat.mod_eq_of_lt hstartklt
    have hdS := List.getElem_eq_getD
      (l := d.suffixWord r) (i := k) (h := hk1) 0
    have hdT := List.getElem_eq_getD
      (l := (w.drop start).take len) (i := k) (h := hk2) 0
    have htake := List.getElem_take
      (xs := w.drop start) (j := len) (i := k) (h := hk2)
    have hdD := List.getElem_eq_getD
      (l := w.drop start) (i := k) (h := hkdrop) 0
    have hdrop := UnifiedCoreAudit.getD_drop_add w k start 0
    calc
      (d.suffixWord r)[k] = (d.suffixWord r).getD k 0 := hdS
      _ = w.getD (start + k) 0 := by
        simpa [List.getI, start, hmod] using hseg
      _ = (w.drop start).getD k 0 := hdrop.symm
      _ = (w.drop start)[k] := hdD.symm
      _ = ((w.drop start).take len)[k] := htake.symm

/-- For a non-wrapping block, the abstract rise-suffix endpoint is the
next real block head. -/
theorem cycleRiseBlockSuffixEndpoint_eq_nextHead_nonwrap
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) (hrnext : r + 1 < d.blockCount) :
    cycleRiseBlockSuffixEndpointState d r =
      StringFlow.Word.wordOrbit
        (w.take (d.headDepth (r + 1))) m := by
  let start := d.headDepth r + (d.c3Word r).length
  let len := (d.suffixWord r).length
  have hsum := d.hnext r hr
  have hnextlt : d.headDepth (r + 1) < P := d.hhead_lt (r + 1) hrnext
  have hnext : start + len = d.headDepth (r + 1) := by
    dsimp [start, len]
    have hcast : (d.headDepth (r + 1) : Nat) =
        d.headDepth r + (d.c3Word r).length + (d.suffixWord r).length := by
      simpa [hrnext, Nat.add_assoc] using hsum
    exact hcast.symm
  have hlen : start + len ≤ w.length := by
    rw [d.hperiod]
    rw [hnext]
    exact le_of_lt hnextlt
  have hword := cycleRiseBlockSuffixWord_eq_drop_nonwrap d r hr hrnext
  have htakeEq : w.take (start + len) = w.take (d.headDepth (r + 1)) :=
    congrArg (fun n => w.take n) hnext
  have hdropEq : (w.drop start).take len =
      (w.take (d.headDepth (r + 1))).drop start := by
    rw [List.take_drop]
    exact congrArg (fun l => l.drop start) htakeEq
  have hsplit := wordOrbit_take_drop w m start len hlen
  have hsplit' :
      StringFlow.Word.wordOrbit
          ((w.take (d.headDepth (r + 1))).drop start)
          (StringFlow.Word.wordOrbit (w.take start) m) =
        StringFlow.Word.wordOrbit
          (w.take (d.headDepth (r + 1))) m := by
    rw [htakeEq] at hsplit
    exact hsplit.symm
  dsimp [cycleRiseBlockSuffixEndpointState]
  rw [riseRun_eq_wordOrbit, hword, hdropEq]
  simpa [cycleRiseBlockC3TailState] using hsplit'

/-- Per-block endpoint rank telescope:
`v2(endpoint+1) + 2*H2_r ≤ v2(c3-tail+1) + F_r`. -/
theorem cycleRiseBlockEndpointRank_le
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    cycleRiseBlockSuffixEndpointRank d r +
        2 * riseCountTwo (d.suffixWord r) ≤
      cycleRiseBlockTailRank d r + cycleRiseBlockCharge d r := by
  dsimp [cycleRiseBlockSuffixEndpointRank,
    cycleRiseBlockSuffixEndpointState, cycleRiseBlockTailRank,
    cycleRiseBlockCharge]
  exact rise_endpoint_rank_le
    (cycleRiseBlockC3TailState d r) (d.suffixWord r)
    (d.hsuffix_one_two r hr) (d.hsuffix_exact r hr)

/-- Summed endpoint rank telescope over all cyclic rise blocks. -/
theorem cycleRiseBlockEndpointRankSum_le
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) :
    ((List.range d.blockCount).map
        (fun r => cycleRiseBlockSuffixEndpointRank d r)).sum +
        2 * cycleRiseBlockH2Sum d ≤
      ((List.range d.blockCount).map
        (fun r => cycleRiseBlockTailRank d r)).sum +
        ((List.range d.blockCount).map
          (fun r => cycleRiseBlockCharge d r)).sum := by
  dsimp [cycleRiseBlockH2Sum]
  rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
    (fun r => riseCountTwo (d.suffixWord r))]
  have h : ∀ r ∈ List.range d.blockCount,
      cycleRiseBlockSuffixEndpointRank d r +
          2 * riseCountTwo (d.suffixWord r) ≤
        cycleRiseBlockTailRank d r + cycleRiseBlockCharge d r := by
    intro r hr
    exact cycleRiseBlockEndpointRank_le d r (List.mem_range.mp hr)
  have hsum1 : ((List.range d.blockCount).map
      (fun r => cycleRiseBlockSuffixEndpointRank d r +
        2 * riseCountTwo (d.suffixWord r))).sum ≤
      ((List.range d.blockCount).map
        (fun r => cycleRiseBlockTailRank d r + cycleRiseBlockCharge d r)).sum :=
    List.sum_le_sum h
  have hleft : ((List.range d.blockCount).map
      (fun r => cycleRiseBlockSuffixEndpointRank d r)).sum +
        ((List.range d.blockCount).map
          (fun r => 2 * riseCountTwo (d.suffixWord r))).sum =
      ((List.range d.blockCount).map
        (fun r => cycleRiseBlockSuffixEndpointRank d r +
          2 * riseCountTwo (d.suffixWord r))).sum := by
    rw [List.sum_map_add]
  have hright : ((List.range d.blockCount).map
      (fun r => cycleRiseBlockTailRank d r + cycleRiseBlockCharge d r)).sum =
      ((List.range d.blockCount).map
        (fun r => cycleRiseBlockTailRank d r)).sum +
        ((List.range d.blockCount).map
          (fun r => cycleRiseBlockCharge d r)).sum :=
    List.sum_map_add
  calc
    ((List.range d.blockCount).map
        (fun r => cycleRiseBlockSuffixEndpointRank d r)).sum +
        ((List.range d.blockCount).map
          (fun r => 2 * riseCountTwo (d.suffixWord r))).sum =
      ((List.range d.blockCount).map
        (fun r => cycleRiseBlockSuffixEndpointRank d r +
          2 * riseCountTwo (d.suffixWord r))).sum := hleft
    _ ≤ ((List.range d.blockCount).map
        (fun r => cycleRiseBlockTailRank d r + cycleRiseBlockCharge d r)).sum :=
      hsum1
    _ = ((List.range d.blockCount).map
        (fun r => cycleRiseBlockTailRank d r)).sum +
        ((List.range d.blockCount).map
          (fun r => cycleRiseBlockCharge d r)).sum := hright

/-- A rise word with entries `1` or `2` satisfies
`2 * (#t=2 steps) ≤ wordWeight`. -/
lemma two_mul_riseCountTwo_le_wordWeight
    (ts : List Nat)
    (hok : ∀ t ∈ ts, t = 1 ∨ t = 2) :
    2 * riseCountTwo ts ≤ StringFlow.wordWeight ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      have htail := ih (fun u hu => hok u (List.mem_cons.mpr (Or.inr hu)))
      rcases hok t (by simp) with h1 | h2
      · subst t
        unfold riseCountTwo StringFlow.wordWeight
        simp
        omega
      · subst t
        unfold riseCountTwo StringFlow.wordWeight
        simp
        omega

/-- For a rise word with entries `1` or `2`, the exact weight equals
the length plus the number of `t=2` steps. -/
lemma wordWeight_eq_length_add_riseCountTwo
    (ts : List Nat)
    (hok : ∀ t ∈ ts, t = 1 ∨ t = 2) :
    StringFlow.wordWeight ts = ts.length + riseCountTwo ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      have htail := ih (fun u hu => hok u (List.mem_cons.mpr (Or.inr hu)))
      rcases hok t (by simp) with h1 | h2
      · subst t
        unfold riseCountTwo StringFlow.wordWeight
        simp
        omega
      · subst t
        unfold riseCountTwo StringFlow.wordWeight
        simp
        omega

/-- Counting the `t=2` entries never exceeds the word length. -/
lemma riseCountTwo_le_length (ts : List Nat) :
    riseCountTwo ts ≤ ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rw [riseCountTwo]
      simp only [List.length_cons]
      split <;> omega

/-- The total `2*H2` in a cyclic rise decomposition is bounded by the
total C3-chain and suffix weight. -/
theorem cycleRiseBlockH2Sum_le_weight
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) :
    2 * cycleRiseBlockH2Sum d ≤
      ((List.range d.blockCount).map
        (fun r => StringFlow.wordWeight (d.c3Word r) +
          StringFlow.wordWeight (d.suffixWord r))).sum := by
  dsimp [cycleRiseBlockH2Sum]
  rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
    (fun r => riseCountTwo (d.suffixWord r))]
  refine List.sum_le_sum ?_
  intro r hr
  have hrlt : r < d.blockCount := List.mem_range.mp hr
  have hbound := two_mul_riseCountTwo_le_wordWeight (d.suffixWord r)
    (d.hsuffix_one_two r hrlt)
  omega

/-- Consequently, `2 * ΣH2 ≤ S` in every cyclic rise decomposition. -/
theorem cycleRiseBlockH2Sum_le_S
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) :
    2 * cycleRiseBlockH2Sum d ≤ S := by
  calc
    2 * cycleRiseBlockH2Sum d ≤
        ((List.range d.blockCount).map
          (fun r => StringFlow.wordWeight (d.c3Word r) +
            StringFlow.wordWeight (d.suffixWord r))).sum :=
      cycleRiseBlockH2Sum_le_weight d
    _ = S := d.hweight.symm

/-- A list whose entries are all at least three has weight at least its
length. -/
lemma wordWeight_ge_length_of_ge_three (ts : List Nat)
    (hok : ∀ t ∈ ts, 3 ≤ t) :
    ts.length ≤ StringFlow.wordWeight ts := by
  induction ts with
  | nil => simp [StringFlow.wordWeight]
  | cons t ts ih =>
      have htail := ih (fun u hu => hok u (List.mem_cons.mpr (Or.inr hu)))
      have ht := hok t (by simp)
      simp [StringFlow.wordWeight]
      omega

/-- Total-weight lower bound for a cyclic rise decomposition:
`P + ΣH2 ≤ S`. -/
theorem cycleRiseBlockWeight_lower_bound
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    P + cycleRiseBlockH2Sum d ≤ S := by
  have hP := cycleRiseBlockPeriodSum_list d hpos
  have hleft : ((List.range d.blockCount).map
      (fun r => (d.c3Word r).length + (d.suffixWord r).length +
        riseCountTwo (d.suffixWord r))).sum =
      P + cycleRiseBlockH2Sum d := by
    simp [cycleRiseBlockH2Sum, List.sum_map_add, hP,
      Nat.add_assoc]
  have hper : ∀ r ∈ List.range d.blockCount,
      (d.c3Word r).length + (d.suffixWord r).length +
          riseCountTwo (d.suffixWord r) ≤
        StringFlow.wordWeight (d.c3Word r) +
          StringFlow.wordWeight (d.suffixWord r) := by
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    have hw := wordWeight_eq_length_add_riseCountTwo (d.suffixWord r)
      (d.hsuffix_one_two r hrlt)
    have hc3 := wordWeight_ge_length_of_ge_three (d.c3Word r)
      (d.hc3_entries r hrlt)
    omega
  have hsum_le : ((List.range d.blockCount).map
      (fun r => (d.c3Word r).length + (d.suffixWord r).length +
        riseCountTwo (d.suffixWord r))).sum ≤
      ((List.range d.blockCount).map
        (fun r => StringFlow.wordWeight (d.c3Word r) +
          StringFlow.wordWeight (d.suffixWord r))).sum := by
    exact List.sum_le_sum hper
  calc
    P + cycleRiseBlockH2Sum d =
        ((List.range d.blockCount).map
          (fun r => (d.c3Word r).length + (d.suffixWord r).length +
            riseCountTwo (d.suffixWord r))).sum := hleft.symm
    _ ≤ ((List.range d.blockCount).map
        (fun r => StringFlow.wordWeight (d.c3Word r) +
          StringFlow.wordWeight (d.suffixWord r))).sum := hsum_le
    _ = S := d.hweight.symm

/-- A direct H2 bound from the total-weight lower bound. -/
theorem cycleRiseBlockH2Sum_le_remaining_weight
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    cycleRiseBlockH2Sum d ≤ S - P := by
  have h := cycleRiseBlockWeight_lower_bound d hpos
  omega

theorem cycleRiseBlockH2Sum_le_S_sub_P
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    cycleRiseBlockH2Sum d ≤ S - P := by
  exact cycleRiseBlockH2Sum_le_remaining_weight d hpos

/-- The total number of `t=2` rise steps is at most the period length. -/
theorem cycleRiseBlockH2Sum_le_P
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    cycleRiseBlockH2Sum d ≤ P := by
  have hP := cycleRiseBlockPeriodSum_list d hpos
  have hcount : cycleRiseBlockH2Sum d ≤
      ((List.range d.blockCount).map
        (fun r => (d.suffixWord r).length)).sum := by
    dsimp [cycleRiseBlockH2Sum]
    exact List.sum_le_sum (fun r _hr => riseCountTwo_le_length (d.suffixWord r))
  have hsuffix :
      ((List.range d.blockCount).map
        (fun r => (d.suffixWord r).length)).sum ≤
      ((List.range d.blockCount).map
        (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum := by
    exact List.sum_le_sum (fun _r _hr => by omega)
  calc
    cycleRiseBlockH2Sum d ≤
        ((List.range d.blockCount).map
          (fun r => (d.suffixWord r).length)).sum := hcount
    _ ≤ ((List.range d.blockCount).map
          (fun r => (d.c3Word r).length + (d.suffixWord r).length)).sum :=
      hsuffix
    _ = P := hP.symm

/-- The right-hand side of the PMI global comparison for cyclic rise
blocks. -/
def cycleRiseBlockAvoidBudgetSum {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) : Nat :=
  ((List.range d.blockCount).map
    (fun r => 2 * (d.headDepth r - d.resetWeight r) + 12 +
      cycleRiseBlockCharge d r)).sum

/-- Reset weight of the next cyclic block, wrapping in the final block. -/
def cycleRiseBlockNextResetWeight {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  if r + 1 < d.blockCount then d.resetWeight (r + 1)
  else d.resetWeight 0

/-- The shifted PMI budget: it is charged to the next block head, not
the current C3-chain head. -/
def cycleRiseBlockNextAvoidBudgetSum {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) : Nat :=
  ((List.range d.blockCount).map
    (fun r => 2 * (cycleRiseBlockNextHeadDepth d r -
        cycleRiseBlockNextResetWeight d r) + 12 +
      cycleRiseBlockCharge d r)).sum

/-- Depth of the C3-tail state of a cyclic rise block. -/
def cycleRiseBlockTailDepth {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  d.headDepth r + (d.c3Word r).length

/-- Reset weight entering the C3-tail state: the last C3 step of the
same block. -/
def cycleRiseBlockTailResetWeight {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat) : Nat :=
  (d.c3Word r).getI ((d.c3Word r).length - 1)

/-- The C3-tail depth of a block is positive. -/
lemma cycleRiseBlockTailDepth_pos {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    1 ≤ cycleRiseBlockTailDepth d r := by
  have hh : 1 ≤ d.headDepth r := d.hhead_pos r hr
  have hc3len : 1 ≤ (d.c3Word r).length := by
    cases hc : d.c3Word r with
    | nil => exact False.elim (d.hc3_nonempty r hr hc)
    | cons a as => simp
  dsimp [cycleRiseBlockTailDepth]
  omega

/-- The last C3 entry of a block is at least three. -/
lemma cycleRiseBlockTailResetWeight_ge_three {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    3 ≤ cycleRiseBlockTailResetWeight d r := by
  have hne : d.c3Word r ≠ [] := d.hc3_nonempty r hr
  have hlen : 1 ≤ (d.c3Word r).length := List.length_pos_iff.mpr hne
  have hidx : (d.c3Word r).length - 1 < (d.c3Word r).length := by omega
  have hmem : (d.c3Word r).getI ((d.c3Word r).length - 1) ∈ d.c3Word r := by
    rw [List.getI_eq_getElem (l := d.c3Word r)
      (n := (d.c3Word r).length - 1) hidx]
    exact List.getElem_mem hidx
  simpa [cycleRiseBlockTailResetWeight] using
    d.hc3_entries r hr ((d.c3Word r).getI ((d.c3Word r).length - 1)) hmem

/-- The last C3 entry is the concrete incoming word weight at the
C3-tail depth (when that depth is a valid word index). -/
lemma cycleRiseBlockTailResetWeight_eq_word_get
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (_hj : cycleRiseBlockTailDepth d r - 1 < P) :
    cycleRiseBlockTailResetWeight d r =
      w.getI (cycleRiseBlockTailDepth d r - 1) := by
  have hne : d.c3Word r ≠ [] := d.hc3_nonempty r hr
  have hlen : 1 ≤ (d.c3Word r).length := List.length_pos_iff.mpr hne
  have hk : (d.c3Word r).length - 1 < (d.c3Word r).length := by omega
  have hseg := d.hc3_segment r hr ((d.c3Word r).length - 1) hk
  have hidx : d.headDepth r + ((d.c3Word r).length - 1) =
      cycleRiseBlockTailDepth d r - 1 := by
    dsimp [cycleRiseBlockTailDepth]
    omega
  calc
    cycleRiseBlockTailResetWeight d r =
        (d.c3Word r).getI ((d.c3Word r).length - 1) := rfl
    _ = w.getI (d.headDepth r + ((d.c3Word r).length - 1)) := hseg
    _ = w.getI (cycleRiseBlockTailDepth d r - 1) := by rw [hidx]

/-- The C3-tail state is obtained from the state one word step earlier
by the last C3 step of the block. -/
lemma cycleRiseBlockTailState_eq_step_of_lt
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hj : cycleRiseBlockTailDepth d r - 1 < P) :
    cycleRiseBlockC3TailState d r =
      (5 * StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) /
        (2 ^ cycleRiseBlockTailResetWeight d r) := by
  have hjp : 1 ≤ cycleRiseBlockTailDepth d r :=
    cycleRiseBlockTailDepth_pos d r hr
  have hj' : cycleRiseBlockTailDepth d r - 1 < w.length := by
    rw [d.hperiod]
    exact hj
  have hsucc := wordOrbit_take_succ w m (cycleRiseBlockTailDepth d r - 1) hj'
  have hsum : cycleRiseBlockTailDepth d r - 1 + 1 =
      cycleRiseBlockTailDepth d r := by omega
  have hwget : w.getI (cycleRiseBlockTailDepth d r - 1) =
      cycleRiseBlockTailResetWeight d r :=
    (cycleRiseBlockTailResetWeight_eq_word_get d r hr hj).symm
  rw [hsum] at hsucc
  rw [hwget] at hsucc
  simpa [cycleRiseBlockC3TailState, cycleRiseBlockTailDepth] using hsucc

/-- Exact last-C3-step data at a C3-tail: the incoming weight is the
last C3 entry, its exact valuation matches that entry, and the C3-tail
state is the accelerated successor of the previous prefix state. -/
theorem cycleRiseBlockTailC3Step
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (hj : cycleRiseBlockTailDepth d r - 1 < P) :
    let x := StringFlow.Word.wordOrbit
      (w.take (cycleRiseBlockTailDepth d r - 1)) m
    let rj := cycleRiseBlockC3TailState d r
    let t := cycleRiseBlockTailResetWeight d r
    3 ≤ t ∧
    twoValuation (5 * x + 1) = t ∧
    2 ^ t * rj = 5 * x + 1 ∧
    w.getI (cycleRiseBlockTailDepth d r - 1) = t := by
  let x := StringFlow.Word.wordOrbit
    (w.take (cycleRiseBlockTailDepth d r - 1)) m
  let rj := cycleRiseBlockC3TailState d r
  let t := cycleRiseBlockTailResetWeight d r
  change 3 ≤ t ∧
    twoValuation (5 * x + 1) = t ∧
    2 ^ t * rj = 5 * x + 1 ∧
    w.getI (cycleRiseBlockTailDepth d r - 1) = t
  have hne : d.c3Word r ≠ [] := d.hc3_nonempty r hr
  have hlen : 1 ≤ (d.c3Word r).length := List.length_pos_iff.mpr hne
  have hk : (d.c3Word r).length - 1 < (d.c3Word r).length := by omega
  have hex := d.hc3_exact r hr ((d.c3Word r).length - 1) hk
  have hidx : d.headDepth r + ((d.c3Word r).length - 1) =
      cycleRiseBlockTailDepth d r - 1 := by
    dsimp [cycleRiseBlockTailDepth]
    omega
  have ht : 3 ≤ t := by
    simpa [t] using cycleRiseBlockTailResetWeight_ge_three d r hr
  have hval : twoValuation (5 * x + 1) = t := by
    dsimp [x, t, cycleRiseBlockTailResetWeight]
    rw [← hidx]
    exact hex
  have hstate := cycleRiseBlockTailState_eq_step_of_lt d r hr hj
  have hpos : 0 < 5 * x + 1 := by positivity
  have hle : t ≤ twoValuation (5 * x + 1) := by omega
  have hdvd : 2 ^ t ∣ 5 * x + 1 :=
    (StringFlow.Lte.twoValuation_ge_iff_dvd_pow (5 * x + 1) t hpos).mp hle
  have hmul : 2 ^ t * ((5 * x + 1) / 2 ^ t) = 5 * x + 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hdvd
  have hstep : 2 ^ t * rj = 5 * x + 1 := by
    dsimp [rj] at hstate ⊢
    rw [hstate]
    exact hmul
  have hincoming : w.getI (cycleRiseBlockTailDepth d r - 1) = t := by
    exact (cycleRiseBlockTailResetWeight_eq_word_get d r hr hj).symm.trans (by
      dsimp [t])
  exact ⟨ht, hval, hstep, hincoming⟩

/-- The state immediately before the last C3 step of a real block has
rank exactly two. -/
theorem cycleRiseBlockTailHeadRank_two
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleRiseBlockDecomposition m S P w)
    (r : Nat) (hr : r < d.blockCount)
    (hj : cycleRiseBlockTailDepth d r - 1 < P) :
    twoValuation
      (StringFlow.Word.wordOrbit
        (w.take (cycleRiseBlockTailDepth d r - 1)) m + 1) = 2 := by
  let x := StringFlow.Word.wordOrbit
    (w.take (cycleRiseBlockTailDepth d r - 1)) m
  have hxfull : S6Audit.FullOrbitFrom7 x := by
    dsimp [x]
    have hjl : cycleRiseBlockTailDepth d r - 1 ≤ w.length := by
      rw [d.hperiod]
      omega
    exact cycleQb8Input_prefix_full_reachable h
      (cycleRiseBlockTailDepth d r - 1) hjl
  have hodd : S6Audit.IsOdd x := S6Audit.FullOrbitFrom7_odd x hxfull
  have ht : 3 ≤ cycleRiseBlockTailResetWeight d r :=
    cycleRiseBlockTailResetWeight_ge_three d r hr
  have hne : d.c3Word r ≠ [] := d.hc3_nonempty r hr
  have hlen : 1 ≤ (d.c3Word r).length := List.length_pos_iff.mpr hne
  have hk : (d.c3Word r).length - 1 < (d.c3Word r).length := by omega
  have hex := d.hc3_exact r hr ((d.c3Word r).length - 1) hk
  have hidx : d.headDepth r + ((d.c3Word r).length - 1) =
      cycleRiseBlockTailDepth d r - 1 := by
    dsimp [cycleRiseBlockTailDepth]
    omega
  have hval : twoValuation (5 * x + 1) =
      cycleRiseBlockTailResetWeight d r := by
    dsimp [x, cycleRiseBlockTailResetWeight]
    rw [← hidx]
    exact hex
  have hc3 : 3 ≤ twoValuation (5 * x + 1) := by
    omega
  exact StringFlow.RealOrbitLocalLemma.state_rank_eq_two_of_outgoing_c3
    x hodd hc3

/-- Tail-charged PMI budget: `Σ(2*(tailDepth - tailReset) + 12 + F)`. -/
def cycleRiseBlockTailAvoidBudgetSum {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) : Nat :=
  ((List.range d.blockCount).map
    (fun r => 2 * (cycleRiseBlockTailDepth d r -
        cycleRiseBlockTailResetWeight d r) + 12 +
      cycleRiseBlockCharge d r)).sum

/-- If the tail-charged global comparison holds, some C3-tail rank
crosses the decisive window. -/
theorem cycleRiseBlockTailFailure_of_global_comparison
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hglobal : 2 * cycleRiseBlockH2Sum d >
      cycleRiseBlockTailAvoidBudgetSum d) :
    ∃ r : Nat, r < d.blockCount ∧
      2 * (cycleRiseBlockTailDepth d r -
          cycleRiseBlockTailResetWeight d r) + 13 ≤
        cycleRiseBlockTailRank d r := by
  by_contra hnone
  have hallAvoid : ∀ r : Nat, r < d.blockCount →
      cycleRiseBlockTailRank d r ≤
        2 * (cycleRiseBlockTailDepth d r -
          cycleRiseBlockTailResetWeight d r) + 12 := by
    intro r hr
    have hnot : ¬ (2 * (cycleRiseBlockTailDepth d r -
        cycleRiseBlockTailResetWeight d r) + 13 ≤
        cycleRiseBlockTailRank d r) := by
      intro hbad
      exact hnone ⟨r, hr, hbad⟩
    omega
  have hsum_le : 2 * cycleRiseBlockH2Sum d ≤
      cycleRiseBlockTailAvoidBudgetSum d := by
    dsimp [cycleRiseBlockH2Sum, cycleRiseBlockTailAvoidBudgetSum]
    rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
      (fun r => riseCountTwo (d.suffixWord r))]
    refine List.sum_le_sum ?_
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    have hbal : 2 * riseCountTwo (d.suffixWord r) ≤
        cycleRiseBlockTailRank d r + cycleRiseBlockCharge d r := by
      simpa [cycleRiseBlockTailRank] using cycleRiseBlockBalance d r hrlt
    have htail := hallAvoid r hrlt
    omega
  omega

/-- The final wrapping block alone contributes at least `2*P` to the
shifted avoidance budget. -/
theorem two_mul_P_le_cycleRiseBlockNextAvoidBudgetSum
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    2 * P ≤ cycleRiseBlockNextAvoidBudgetSum d := by
  let r := d.blockCount - 1
  have hr : r < d.blockCount := by
    dsimp [r]
    omega
  have hlast : ¬ r + 1 < d.blockCount := by
    dsimp [r]
    omega
  have hhead : 1 ≤ d.headDepth 0 := d.hhead_pos 0 hpos
  have hreset : d.resetWeight 0 = 1 ∨ d.resetWeight 0 = 2 :=
    d.hreset_one_two 0 hpos
  let term := fun i =>
    2 * (cycleRiseBlockNextHeadDepth d i -
        cycleRiseBlockNextResetWeight d i) + 12 +
      cycleRiseBlockCharge d i
  have hterm : 2 * P ≤ term r := by
    dsimp [term, cycleRiseBlockNextHeadDepth,
      cycleRiseBlockNextResetWeight]
    rw [if_neg hlast, if_neg hlast]
    omega
  have hrmem : r ∈ List.range d.blockCount := List.mem_range.mpr hr
  have hmem : term r ∈ (List.range d.blockCount).map term :=
    List.mem_map.mpr ⟨r, hrmem, rfl⟩
  have hleSum : term r ≤ ((List.range d.blockCount).map term).sum :=
    List.le_sum_of_mem hmem
  exact hterm.trans (by
    simpa [term, cycleRiseBlockNextAvoidBudgetSum] using hleSum)

/-- For every nonempty cyclic rise decomposition the proposed strict
PMI comparison has the wrong direction.  Directly:

`2*H2 ≤ 2*P ≤ nextAvoidBudget`. -/
theorem cycleRiseBlockH2Sum_le_nextAvoidBudget
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    2 * cycleRiseBlockH2Sum d ≤
      cycleRiseBlockNextAvoidBudgetSum d := by
  calc
    2 * cycleRiseBlockH2Sum d ≤ 2 * P :=
      Nat.mul_le_mul_left 2 (cycleRiseBlockH2Sum_le_P d hpos)
    _ ≤ cycleRiseBlockNextAvoidBudgetSum d :=
      two_mul_P_le_cycleRiseBlockNextAvoidBudgetSum d hpos

/-- The correct weak comparison holds for every cyclic rise
decomposition, including the empty one. -/
theorem cycleRiseBlockH2Sum_le_nextAvoidBudget_all
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w) :
    2 * cycleRiseBlockH2Sum d ≤
      cycleRiseBlockNextAvoidBudgetSum d := by
  by_cases hzero : d.blockCount = 0
  · simp [cycleRiseBlockH2Sum, cycleRiseBlockNextAvoidBudgetSum, hzero]
  · exact cycleRiseBlockH2Sum_le_nextAvoidBudget d
      (Nat.pos_of_ne_zero hzero)

/-- Hence the strict reverse comparison is false for every nonempty
cyclic rise decomposition, independently of any tail-rank estimate.
This audit concerns the old next-head budget, not the tail budget. -/
theorem cycleRiseBlockNextPMIGlobalComparison_false
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hpos : 0 < d.blockCount) :
    ¬ (2 * cycleRiseBlockH2Sum d > cycleRiseBlockNextAvoidBudgetSum d) := by
  intro hstrict
  have hle := cycleRiseBlockH2Sum_le_nextAvoidBudget d hpos
  omega

/-- Direct inequality forced by the endpoint balance and a per-block
tail-rank upper bound.  This is the exact direction supplied by the
current cyclic-rise data:

`2 * sum H2 <= sum (2 * (nextDepth - nextReset) + 12 + F)`.

Consequently the strict reverse inequality cannot be used as a PMI
conclusion under the same tail-rank hypotheses. -/
theorem cycleRiseBlockH2Sum_le_nextAvoidBudget_of_tailRank
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hc3 : ∀ r : Nat, r < d.blockCount →
      cycleRiseBlockTailRank d r ≤
        2 * (cycleRiseBlockNextHeadDepth d r -
          cycleRiseBlockNextResetWeight d r) + 12) :
    2 * cycleRiseBlockH2Sum d ≤
      cycleRiseBlockNextAvoidBudgetSum d := by
  dsimp [cycleRiseBlockH2Sum, cycleRiseBlockNextAvoidBudgetSum]
  rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
    (fun r => riseCountTwo (d.suffixWord r))]
  refine List.sum_le_sum ?_
  intro r hr
  have hrlt : r < d.blockCount := List.mem_range.mp hr
  have hbal := cycleRiseBlockEndpointRank_le d r hrlt
  have htail := hc3 r hrlt
  omega

/-- Audit: the old endpoint-based global-comparison implication, kept
only to document why the next-head budget cannot be the PMI target. -/
theorem cycleRiseBlockEndpointFailure_of_next_global_comparison
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hc3 : ∀ r : Nat, r < d.blockCount →
      cycleRiseBlockTailRank d r ≤
        2 * (cycleRiseBlockNextHeadDepth d r -
          cycleRiseBlockNextResetWeight d r) + 12)
    (hglobal : 2 * cycleRiseBlockH2Sum d >
      cycleRiseBlockNextAvoidBudgetSum d) :
    ∃ r : Nat, r < d.blockCount ∧
      2 * (cycleRiseBlockNextHeadDepth d r -
          cycleRiseBlockNextResetWeight d r) + 13 ≤
        cycleRiseBlockSuffixEndpointRank d r := by
  by_contra hnone
  have hallAvoid : ∀ r, r < d.blockCount →
      cycleRiseBlockSuffixEndpointRank d r ≤
        2 * (cycleRiseBlockNextHeadDepth d r -
          cycleRiseBlockNextResetWeight d r) + 12 := by
    intro r hr
    have hnot : ¬ (2 * (cycleRiseBlockNextHeadDepth d r -
        cycleRiseBlockNextResetWeight d r) + 13 ≤
        cycleRiseBlockSuffixEndpointRank d r) := by
      intro hbad
      exact hnone ⟨r, hr, hbad⟩
    omega
  have hsum_le : 2 * cycleRiseBlockH2Sum d ≤
      cycleRiseBlockNextAvoidBudgetSum d := by
    dsimp [cycleRiseBlockH2Sum, cycleRiseBlockNextAvoidBudgetSum]
    rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
      (fun r => riseCountTwo (d.suffixWord r))]
    refine List.sum_le_sum ?_
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    have hbal := cycleRiseBlockEndpointRank_le d r hrlt
    have htail := hc3 r hrlt
    have hend := hallAvoid r hrlt
    omega
  omega

/-- Audit: the per-block tail-rank premise `hc3` already forces
`2 * ΣH2 ≤ Σ(2*(nextHeadDepth - nextResetWeight) + 12 + F)`, so it
contradicts the old next-head global comparison.  This is an audit of
the superseded budget, not of the tail-based PMI comparison. -/
theorem cycleRiseBlockNextPMIGlobalComparison_false_of_hc3
    {m S P : Nat} {w : List Nat}
    (d : CycleRiseBlockDecomposition m S P w)
    (hc3 : ∀ r : Nat, r < d.blockCount →
      cycleRiseBlockTailRank d r ≤
        2 * (cycleRiseBlockNextHeadDepth d r -
          cycleRiseBlockNextResetWeight d r) + 12) :
    ¬ (2 * cycleRiseBlockH2Sum d > cycleRiseBlockNextAvoidBudgetSum d) := by
  intro hglobal
  have hsum_le :=
    cycleRiseBlockH2Sum_le_nextAvoidBudget_of_tailRank d hc3
  omega

/-- The remaining PMI global comparison for one cyclic rise
decomposition, charged to the C3-tail rank and its last C3 reset step. -/
def cycleRiseBlockPMIGlobalComparison (m S P : Nat) (w : List Nat) : Prop :=
  ∀ d : CycleRiseBlockDecomposition m S P w,
    2 * cycleRiseBlockH2Sum d > cycleRiseBlockTailAvoidBudgetSum d

/-- Top-level cyclic-rise PMI comparison for every real
`CycleQb8Input` word. -/
def cycleRiseBlockPMIGlobalComparisonHolds : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      cycleRiseBlockPMIGlobalComparison m S P w

/-- Every real `CycleQb8Input` has a nonempty cyclic rise block
decomposition.  This is the structural companion of
`cycleRiseBlockPMIGlobalComparisonHolds`; the latter is only meaningful
after this existence statement is established. -/
def cycleRiseBlockDecompositionExists : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      ∃ d : CycleRiseBlockDecomposition m S P w,
        1 ≤ d.blockCount

/-- Once a nonempty cyclic rise decomposition exists and the tail-based
PMI global comparison holds, some C3-tail rank crosses the decisive
window. -/
theorem cycleRiseBlockFailure_of_decomposition_and_global_comparison
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (hexists : cycleRiseBlockDecompositionExists)
    (hglobal : cycleRiseBlockPMIGlobalComparisonHolds) :
    ∃ d : CycleRiseBlockDecomposition m S P w,
      ∃ r : Nat, r < d.blockCount ∧
        2 * (cycleRiseBlockTailDepth d r -
            cycleRiseBlockTailResetWeight d r) + 13 ≤
          cycleRiseBlockTailRank d r := by
  rcases hexists m S P w rise c3 h with ⟨d, _hdpos⟩
  exact ⟨d, cycleRiseBlockTailFailure_of_global_comparison d
    (hglobal m S P w rise c3 h d)⟩

/-- Rank of the head of a block. -/
def cycleBlockHeadRank {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat) : Nat :=
  twoValuation
    (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m + 1)

/-- Total positive charge along the suffix of a block. -/
def cycleBlockCharge {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat) : Nat :=
  riseChargeSum
    (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m)
    (d.suffixWord r)

/-- The local rise-block balance specialized to one block of a
cycle decomposition. -/
theorem cycle_block_balance
    {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount) :
    2 * riseCountTwo (d.suffixWord r) ≤
      cycleBlockHeadRank d r + cycleBlockCharge d r := by
  exact rise_block_balance
    (StringFlow.Word.wordOrbit (w.take (d.headDepth r)) m)
    (d.suffixWord r)
    (d.hsuffix_one_two r hr)
    (d.hsuffix_exact r hr)

/-- If a block avoids the decisive window, then its `t=2` count
satisfies the local capacity bound. -/
theorem cycle_block_H2_bound_of_avoid
    {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat)
    (hr : r < d.blockCount)
    (havoid : cycleBlockHeadRank d r + cycleBlockCharge d r ≤
      2 * (d.headDepth r - d.resetWeight r) + 12) :
    riseCountTwo (d.suffixWord r) ≤
      d.headDepth r - d.resetWeight r + 6 := by
  let u := cycleBlockHeadRank d r
  let F := cycleBlockCharge d r
  let H2 := riseCountTwo (d.suffixWord r)
  have hbal : 2 * H2 ≤ u + F := by
    dsimp [u, F, H2]
    exact cycle_block_balance d r hr
  have hwindow : u ≤ 2 * (d.headDepth r - d.resetWeight r) + 12 := by
    dsimp [u, F] at havoid ⊢
    omega
  have hcharge : F ≤ 2 * (d.headDepth r - d.resetWeight r) + 12 - u := by
    dsimp [u, F] at havoid ⊢
    omega
  exact block_capacity_of_charge_bound
    (d.headDepth r) (d.resetWeight r) u F H2 hbal hwindow hcharge

/-- The block satisfies the decisive non-failure budget. -/
def cycleBlockAvoidsWindow {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) (r : Nat) : Prop :=
  cycleBlockHeadRank d r + cycleBlockCharge d r ≤
    2 * (d.headDepth r - d.resetWeight r) + 12

/-- Every block avoids the window.  This is the hypothesis used in the
PMI contradiction. -/
def cycleAllBlocksAvoidWindow {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) : Prop :=
  ∀ r, r < d.blockCount → cycleBlockAvoidsWindow d r

/-- The rank-only avoidance hypothesis needed by the PMI global
comparison: every block head is inside the decisive rank window. -/
def cycleAllBlocksRankAvoidWindow {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) : Prop :=
  ∀ r, r < d.blockCount →
    cycleBlockHeadRank d r ≤
      2 * (d.headDepth r - d.resetWeight r) + 12

/-- Total number of `t=2` steps over the blocks. -/
def cycleBlockH2Sum {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) : Nat :=
  ((List.range d.blockCount).map
    (fun r => riseCountTwo (d.suffixWord r))).sum

/-- The right-hand side of the missing PMI global comparison (6):
`Σ_r (2(j_r - t_r) + 12 + F_r)`. -/
def cycleBlockAvoidBudgetSum {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w) : Nat :=
  ((List.range d.blockCount).map
    (fun r => 2 * (d.headDepth r - d.resetWeight r) + 12 +
      cycleBlockCharge d r)).sum

/-- If the global PMI comparison (6) holds, then some block has rank
above the corrected decisive threshold.  The remaining PMI task is thus
exactly to prove that global sum inequality. -/
theorem cycleBlockFailure_of_global_comparison
    {m S P : Nat} {w : List Nat}
    (d : CycleBlockDecomposition m S P w)
    (hglobal : 2 * cycleBlockH2Sum d > cycleBlockAvoidBudgetSum d) :
    ∃ r : Nat, r < d.blockCount ∧
      2 * (d.headDepth r - d.resetWeight r) + 13 ≤
        cycleBlockHeadRank d r := by
  by_contra hnone
  have hallAvoid : cycleAllBlocksRankAvoidWindow d := by
    intro r hr
    have hnot : ¬ (2 * (d.headDepth r - d.resetWeight r) + 13 ≤
        cycleBlockHeadRank d r) := by
      intro hbad
      exact hnone ⟨r, hr, hbad⟩
    omega
  have hsum_le : 2 * cycleBlockH2Sum d ≤ cycleBlockAvoidBudgetSum d := by
    dsimp [cycleBlockH2Sum, cycleBlockAvoidBudgetSum]
    rw [← StringFlow.PMI.sum_map_mul_left (List.range d.blockCount) 2
      (fun r => riseCountTwo (d.suffixWord r))]
    refine List.sum_le_sum ?_
    intro r hr
    have hrlt : r < d.blockCount := List.mem_range.mp hr
    have hbal := cycle_block_balance d r hrlt
    have havoid := hallAvoid r hrlt
    omega
  omega

/-- The remaining PMI global comparison for one block decomposition. -/
def cycleQb8InputPMIGlobalComparison (m S P : Nat) (w : List Nat) : Prop :=
  ∀ d : CycleBlockDecomposition m S P w,
    2 * cycleBlockH2Sum d > cycleBlockAvoidBudgetSum d

/-- The top-level remaining PMI comparison for every real
`CycleQb8Input` word. -/
def cycleQb8InputPMIGlobalComparisonHolds : Prop :=
  ∀ m S P : Nat, ∀ w rise c3 : List Nat,
    CycleQb8Input m S P w rise c3 →
      cycleQb8InputPMIGlobalComparison m S P w

/-- If the top-level PMI comparison holds, every decomposition of a real
cycle word has a decisive-rank failure block. -/
theorem cycleBlockFailure_of_global_comparison_all
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (hglobal : cycleQb8InputPMIGlobalComparisonHolds)
    (d : CycleBlockDecomposition m S P w) :
    ∃ r : Nat, r < d.blockCount ∧
      2 * (d.headDepth r - d.resetWeight r) + 13 ≤
        cycleBlockHeadRank d r :=
  cycleBlockFailure_of_global_comparison d (hglobal m S P w rise c3 h d)

/-- The remaining PMI contradiction target. -/
def pmicontradictionOfAllBlocksAvoid (m S P : Nat) (w : List Nat) : Prop :=
  ∀ d : CycleBlockDecomposition m S P w,
    ¬ cycleAllBlocksAvoidWindow d

/-- The empty decomposition shows that the unconstrained target is false:
it must also require a nonempty block decomposition, and ultimately a real
`CycleQb8Input`. -/
def emptyCycleBlockDecomposition : CycleBlockDecomposition 0 0 0 [] where
  blockCount := 0
  headDepth := fun _ => 0
  resetWeight := fun _ => 0
  suffixWord := fun _ => []
  c3Weight := fun _ => 0
  hhead0 := rfl
  hhead_pos := by
    intro r hr
    omega
  hhead_lt := by
    intro r hr
    omega
  hreset_eq := by
    intro r hr
    omega
  hreset_ge3 := by
    intro r hr
    omega
  hsuffix_one_two := by
    intro r hr t ht
    omega
  hsuffix_exact := by
    intro r hr k hk
    omega
  hc3_weight := by
    intro r hr
    omega
  hnext := by
    intro r hr
    omega
  hweight := by
    simp

/-- With zero blocks, the all-blocks-avoid condition is vacuously true. -/
theorem emptyCycleBlockDecomposition_allAvoid :
    cycleAllBlocksAvoidWindow emptyCycleBlockDecomposition := by
  intro r hr
  simp [emptyCycleBlockDecomposition] at hr

/-- The unconstrained PMI contradiction is false. -/
theorem pmicontradictionOfAllBlocksAvoid_false :
    ¬ pmicontradictionOfAllBlocksAvoid 0 0 0 [] := by
  intro h
  exact h emptyCycleBlockDecomposition emptyCycleBlockDecomposition_allAvoid

/-- A `CycleQb8Input` is anchored at a rise step. Consequently, a nonempty
linear decomposition beginning at word index zero cannot have a C3 reset
step at that position.  The block decomposition must instead use a cyclic
C3-to-rise boundary, which is why the real PMI contradiction cannot be
stated on the current linear `CycleBlockDecomposition`. -/
theorem cycleQb8Input_no_linear_block_decomposition
    {m S P : Nat} {w rise c3 : List Nat}
    (h : CycleQb8Input m S P w rise c3)
    (d : CycleBlockDecomposition m S P w)
    (hblock : 1 ≤ d.blockCount) : False := by
  have hreset0 := d.hreset_eq 0 hblock
  have hge3 := d.hreset_ge3 0 hblock
  rw [d.hhead0] at hreset0
  rw [hreset0] at hge3
  rcases h.hrise_start with h1 | h2
  · rw [h1] at hge3
    omega
  · rw [h2] at hge3
    omega

end CycleBridge

end StringFlow
